import LeanDb.Entity

namespace LeanDb

/-! # The dependent select surface, and its reference semantics

`Rows ts` is computed by recursion on the list of entity types, so
`select [Ticket, User]` *forces* `where' : Stored Ticket × Stored User → Bool`
— a predicate over the wrong tables does not typecheck.

`gather`/`selectSpec` here are the executable reference semantics
(plan-v2 M2): fetch, product, filter, sort. The SQLite executor runs this
directly in v1; pushdown (M4) must stay observationally equal to it.
-/

/-- The row type of a multi-table select: one `Stored` per entity type,
    as nested pairs; a single table is unwrapped. -/
@[reducible] def Rows : List Type → Type
  | [] => PUnit
  | [α] => Stored α
  | α :: rest => Stored α × Rows rest

/-- Sort specification over a row type `ρ`, per plan.md §8: typed keys
    (`.key` with any `[Ord κ]`), raw comparators, descending, lexicographic
    composition. Results additionally carry an implicit final tiebreak on
    primary keys (§4.3 determinism), applied by the executor. -/
inductive SortBy (ρ : Type) where
  | preserve
  | key {κ : Type} [ord : Ord κ] (f : ρ → κ)
  | cmp (f : ρ → ρ → Ordering)
  | desc (s : SortBy ρ)
  | andThen (a b : SortBy ρ)

def SortBy.ord : SortBy ρ → ρ → ρ → Ordering
  | .preserve, _, _ => .eq
  | .key (ord := o) f, a, b => o.compare (f a) (f b)
  | .cmp f, a, b => f a b
  | .desc s, a, b => (s.ord a b).swap
  | .andThen s t, a, b => (s.ord a b).then (t.ord a b)


/-- Sort direction for a pushed `ORDER BY` (LDB-04). -/
inductive Dir where
  | asc | desc
  deriving Repr, DecidableEq

def Dir.sql : Dir → String
  | .asc => "ASC"
  | .desc => "DESC"

/-- A pushed order key: a column of the first table (name + direction).
    Multi-table `selectP` appends `, id ASC` per table for determinism. -/
structure Order (ts : List Type) where
  column : String
  dir : Dir := .asc
  deriving Repr

/-- `LIMIT`/`OFFSET` window (LDB-04). `limit` is range-checked before
    bind so it cannot wrap at Int64. -/
structure Window where
  limit : Option Nat := none
  offset : Nat := 0
  deriving Repr

def Window.isTrivial (w : Window) : Bool :=
  w.limit.isNone && w.offset == 0

/-- `true` when LIMIT/OFFSET fit in a SQLite INTEGER bind. Out-of-range
    windows are applied in Lean (`Window.apply`) so meaning and execution
    agree rather than wrapping or faulting. -/
def Window.sqlOk (w : Window) : Bool :=
  w.offset < Int64.maxValue.toNatClampNeg &&
    match w.limit with
    | none => true
    | some n => n < Int64.maxValue.toNatClampNeg

def Window.check (w : Window) : Except DbError Unit := do
  if w.offset >= Int64.maxValue.toNatClampNeg then
    throw (.sqlite "window offset is out of range")
  if let some n := w.limit then
    if n >= Int64.maxValue.toNatClampNeg then
      throw (.sqlite "window limit is out of range")

/-- Drop `offset` and keep `limit` rows. Applied in Lean after the residual
    filter when the plan is not exact, so a pushed `LIMIT` cannot hide a
    later matching row. -/
def Window.apply (w : Window) (rows : Array α) : Array α :=
  let start := min w.offset rows.size
  let stop := match w.limit with
    | none => rows.size
    | some n => min (start + n) rows.size
  rows.extract start stop

/-- A place rows come from: the real database, or an in-memory fixture in
    tests. Loading is by entity, never by string; the index says which
    position in the `select` table list is being loaded, so a plan's
    pushed conjuncts can narrow that table's fetch. -/
structure Source (m : Type → Type) where
  load : (i : Nat) → (α : Type) → [Entity α] → m (Array (Stored α))

/-- Typeclass computing, for a list of entity types, how to gather the
    cartesian product of their rows and how to read off row identities. -/
class RowsOf (ts : List Type) where
  gather : {m : Type → Type} → [Monad m] → (offset : Nat) → Source m → m (Array (Rows ts))
  ids : Rows ts → List Int64
  /-- The involved tables' specs, in list order — the joined executor's
      `FROM`/`SELECT` layout. -/
  specs : List TableSpec
  /-- Decode one joined result row laid out as `id, cols…` per table,
      starting at `start`. -/
  decodeFrom : (cols : Array Col) → (start : Nat) → Except DbError (Rows ts)
  /-- Map every table's column of rows through `f` (which must keep length
      and order) and reassemble — how the executor attaches child lists
      (LEP-0003 D) to joined results in one pass per table. -/
  mapTables : {m : Type → Type} → [Monad m] →
    (f : (α : Type) → [Entity α] → Array (Stored α) → m (Array (Stored α))) →
    Array (Rows ts) → m (Array (Rows ts))

/-- Decode `id, cols…` of a single entity from a slice of a joined row. -/
private def decodeStored (α : Type) [Entity α] (cols : Array Col) (start : Nat) :
    Except DbError (Stored α) := do
  let n := (Entity.fields (α := α)).size
  let id ← match cols.getD start .null with
    | .int v => pure v
    | c => .error (.decode (Entity.tableName α) "id" s!"expected INTEGER id, found {c.describe}")
  let v ← Entity.decode (cols.extract (start + 1) (start + 1 + n))
  return ⟨⟨id⟩, v⟩

instance [Entity α] : RowsOf [α] where
  gather offset src := src.load offset α
  ids r := [r.id.toInt64]
  specs := [Entity.spec α]
  decodeFrom cols start := decodeStored α cols start
  mapTables f rows := f α rows

instance [Entity α] [RowsOf (β :: ts)] : RowsOf (α :: β :: ts) where
  gather offset src := do
    let heads ← src.load offset α
    let tails ← RowsOf.gather (ts := β :: ts) (offset + 1) src
    return heads.flatMap fun h => tails.map fun t => (h, t)
  ids r := r.1.id.toInt64 :: RowsOf.ids (ts := β :: ts) r.2
  specs := Entity.spec α :: RowsOf.specs (β :: ts)
  decodeFrom cols start := do
    let h ← decodeStored α cols start
    let t ← RowsOf.decodeFrom (ts := β :: ts) cols (start + 1 + (Entity.fields (α := α)).size)
    return (h, t)
  mapTables f rows := do
    let hs ← f α (rows.map (·.1))
    let ts ← RowsOf.mapTables (ts := β :: ts) f (rows.map (·.2))
    return hs.zip ts

private def compareIds : List Int64 → List Int64 → Ordering
  | [], [] => .eq
  | [], _ => .lt
  | _, [] => .gt
  | a :: as, b :: bs => (compare a b).then (compareIds as bs)

/-- Filter and sort gathered rows: the lambda, the sort spec, and the
    deterministic id tiebreak. -/
def finishRows (ts : List Type) [RowsOf ts] (rows : Array (Rows ts))
    (where' : Rows ts → Bool) (sortBy : SortBy (Rows ts)) : Array (Rows ts) :=
  let rows := rows.filter where'
  match sortBy with
  | .preserve => rows
  | _ =>
      rows.qsort fun a b =>
        ((sortBy.ord a b).then (compareIds (RowsOf.ids (ts := ts) a) (RowsOf.ids (ts := ts) b))).isLT

/-- The meaning of `select`, in four lines: product, filter, sort — with
    the deterministic id tiebreak. Everything the engine does must equal
    this. -/
def selectSpec [Monad m] (ts : List Type) [RowsOf ts] (src : Source m)
    (where' : Rows ts → Bool) (sortBy : SortBy (Rows ts) := .preserve) :
    m (Array (Rows ts)) := do
  let rows ← RowsOf.gather (ts := ts) 0 src
  return finishRows ts rows where' sortBy

end LeanDb
