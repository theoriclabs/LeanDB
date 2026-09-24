import LeanDb.Typed.Schema
import LeanDb.Db
import LeanDb.Transaction

namespace LeanDb

/-! # Pure database state (M15-pre)

`Table` is one entity's AUTOINCREMENT counter and its rows in id order,
child lists attached. `DbState s` is a function from the schema's table
enum to that table's contents — the same value the kernel sees and the
compiled code runs. `get` transports along `IsSchema.Has.ty_eq`; `set`
is function update; `load` reads every table under one `readSnapshot`.
-/

/-- The production monad. `DbState.load : Db (DbState s)`. -/
abbrev Db := DbM

/-- A table's contents: the AUTOINCREMENT counter, and rows by id.
    No `[Entity α]` on the structure so `ty_eq ▸` transports it. -/
structure Table (α : Type) where
  next : Nat := 1
  rows : List (Stored α) := []
  deriving Repr

/-- The whole database: one table per entity of `s`. The Pi lives in
    `Type` because each `Table _` does, so `DbState s` is a `DbM` result. -/
structure DbState (s : Type) [i : IsSchema s] : Type where
  tables : (t : Fin i.nTables) → Table (i.pack t).ty

/-- Ids strictly increase, are positive, and stay below `next`. -/
def Table.idsOk [Entity α] (t : Table α) : Bool :=
  let rec go (prev : Option Int64) : List (Stored α) → Bool
    | [] => true
    | r :: rs =>
        let id := r.id.toInt64
        let ordered := match prev with
          | none => true
          | some p => p < id
        let inRange := (0 : Int64) < id && id.toNatClampNeg < t.next
        ordered && inRange && go (some id) rs
  go none t.rows

/-- The entity invariant holds on every row (true when there is none). -/
def Table.invariantsOk [Entity α] (t : Table α) : Bool :=
  t.rows.all fun r =>
    match Entity.invariant (α := α) with
    | none => true
    | some (_, p) => p r.val

/-- Parent columns round-trip through `encode`/`decode`. -/
def Table.decodesOk [Entity α] (t : Table α) : Bool :=
  t.rows.all fun r =>
    match Entity.decode (α := α) (Entity.encode r.val) with
    | .ok v => Entity.encode (α := α) v == Entity.encode r.val
    | .error _ => false

/-- Every row is `Checked` (`Entity.check` succeeds). -/
def Table.checkedOk [Entity α] (t : Table α) : Bool :=
  t.rows.all fun r =>
    match Entity.check α r.val with
    | .ok _ => true
    | .error _ => false

/-- Child lists re-attach (derived columns check). Vacuous with no lists. -/
def Table.childrenOk [Entity α] (t : Table α) : Bool :=
  t.rows.all fun r =>
    (Entity.children (α := α)).all fun link =>
      let pairs := (link.rows r.val).zipIdx.map fun (cols, i) => (i, cols)
      match link.attach pairs r.val with
      | .ok _ => true
      | .error _ => false

/-- Unique-index keys are unique among rows. -/
def Table.uniquesOk [Entity α] [HasUnique α] (t : Table α) : Bool :=
  (Unique.all α).all fun ix =>
    let rec distinct : List (Stored α) → Bool
      | [] => true
      | r :: rs =>
          let enc := Unique.encodeKey ix (Unique.keyOf ix r.val)
          rs.all (fun o => Unique.encodeKey ix (Unique.keyOf ix o.val) != enc) &&
            distinct rs
    distinct t.rows

/-- Local well-formedness of one table (ids, decode, Checked, children,
    unique keys). Foreign keys need the whole `DbState`. -/
def Table.check [Entity α] [HasUnique α] (t : Table α) : Bool :=
  t.idsOk && t.invariantsOk && t.decodesOk && t.checkedOk && t.childrenOk && t.uniquesOk

def Table.WF [Entity α] [HasUnique α] (t : Table α) : Prop := t.check = true

/-- No rows, every AUTOINCREMENT counter at 1. -/
def DbState.empty {s : Type} [i : IsSchema s] : DbState s where
  tables := fun _ => { next := 1, rows := [] }

/-- Rows of `α` in this state. `α` must be a table of `s`. -/
def DbState.get {s α : Type} [i : IsSchema s] [Entity α] [h : IsSchema.Has s α]
    (st : DbState s) : Table α :=
  h.ty_eq ▸ st.tables h.id

/-- Replace the table for `α` by function update. -/
def DbState.set {s α : Type} [i : IsSchema s] [Entity α] [h : IsSchema.Has s α]
    (st : DbState s) (tbl : Table α) : DbState s where
  tables := fun t =>
    if hEq : t = h.id then
      hEq.symm ▸ (h.ty_eq.symm ▸ tbl)
    else
      st.tables t

/-- Direct access by schema-table index. -/
def DbState.getAt {s : Type} [i : IsSchema s] (st : DbState s) (t : Fin i.nTables) :
    Table (i.pack t).ty :=
  st.tables t

/-- The inbound-key source table, transported along `sourceTy_eq`. -/
def DbState.getSource {s α : Type} [i : IsSchema s] [h : HasReferencedBy s α]
    (st : DbState s) (r : h.ReferencedBy) : Table (h.Source r) :=
  h.sourceTy_eq r ▸ st.tables (h.sourceId r)

/-- `eq.rec` along `e` then `e.symm` is the identity, for `Table`. -/
private theorem Table.eq_rec_cancel {α β : Type} (e : α = β) (t : Table β) :
    e ▸ (e.symm ▸ t : Table α) = t := by
  cases e
  rfl

private theorem Table.transport_nil_rows {α β : Type} (e : α = β) :
    (e ▸ ({ next := 1, rows := [] } : Table α)).rows = [] := by
  cases e
  rfl

private theorem Table.transport_nil_next {α β : Type} (e : α = β) :
    (e ▸ ({ next := 1, rows := [] } : Table α)).next = 1 := by
  cases e
  rfl

theorem DbState.get_set_same {s α : Type} [i : IsSchema s] [Entity α]
    [h : IsSchema.Has s α] (st : DbState s) (tbl : Table α) :
    DbState.get (α := α) (st.set tbl) = tbl := by
  unfold DbState.get DbState.set
  simp only [dif_pos]
  exact Table.eq_rec_cancel h.ty_eq tbl

theorem DbState.get_set_other {s α β : Type} [i : IsSchema s]
    [Entity α] [Entity β] [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (st : DbState s) (tbl : Table α) (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β) (st.set (α := α) tbl) = DbState.get (α := β) st := by
  unfold DbState.get DbState.set
  simp [dif_neg (Ne.symm hneq)]

theorem DbState.empty_rows {s α : Type} [i : IsSchema s] [Entity α]
    [h : IsSchema.Has s α] :
    (DbState.get (α := α) (DbState.empty (s := s))).rows = [] := by
  unfold DbState.get DbState.empty
  exact Table.transport_nil_rows h.ty_eq

theorem DbState.empty_next {s α : Type} [i : IsSchema s] [Entity α]
    [h : IsSchema.Has s α] :
    (DbState.get (α := α) (DbState.empty (s := s))).next = 1 := by
  unfold DbState.get DbState.empty
  exact Table.transport_nil_next h.ty_eq

/-- The next AUTOINCREMENT id: `sqlite_sequence` if present, otherwise
    one past the greatest stored id (1 on an empty table). -/
def DbState.loadNext (α : Type) [Entity α] (rows : Array (Stored α)) : Db Nat := do
  let name := Entity.tableName α
  let seq? ← untrackedSqlite fun db => do
    try
      let stmt ← db.prepare "SELECT seq FROM sqlite_sequence WHERE name = ?"
      stmt.bindText 1 name
      if ← stmt.step then some <$> stmt.columnInt64 0 else pure none
    catch _ =>
      pure none
  match seq? with
  | some n => return n.toNatClampNeg + 1
  | none =>
      let maxId := rows.foldl (init := (0 : Int64)) fun m r =>
        if r.id.toInt64 > m then r.id.toInt64 else m
      return maxId.toNatClampNeg + 1

/-- Build a `DbState` from a list of packed tables (id order of `tables`). -/
def DbState.ofList {s : Type} [i : IsSchema s]
    (packed : List (Σ t : Fin i.nTables, Table (i.pack t).ty)) : DbState s where
  tables := fun t =>
    let rec find : List (Σ t : Fin i.nTables, Table (i.pack t).ty) → Table (i.pack t).ty
      | [] => { next := 1, rows := [] }
      | ⟨t', tbl⟩ :: rest =>
          if h : t' = t then h ▸ tbl else find rest
    find packed

/-- Read every table of `s` in id order, under one deferred snapshot. -/
def DbState.load {s : Type} [i : IsSchema s] : Db (DbState s) :=
  readSnapshot do
    let packed ← i.tables.toList.mapM fun t => do
      let p := i.pack t
      have : Entity p.ty := p.entity
      let rows ← fetchAll p.ty
      let next ← DbState.loadNext p.ty rows
      pure (⟨t, { next, rows := rows.toList }⟩ : Σ t : Fin i.nTables, Table (i.pack t).ty)
    return DbState.ofList packed

/-- Whether any schema table named `tableName` contains `id`. -/
def DbState.containsId {s : Type} [i : IsSchema s] (st : DbState s)
    (tableName : String) (id : Int64) : Bool :=
  i.tables.any fun t =>
    let p := i.pack t
    have : Entity p.ty := p.entity
    Entity.tableName p.ty == tableName &&
      (st.tables t).rows.any fun row => row.id.toInt64 == id

/-- Every foreign key of `α` resolves to a row in the target table. -/
def Table.fksOk {s α : Type} [IsSchema s] [Entity α] [hf : HasForeignKey α]
    (st : DbState s) (t : Table α) : Bool :=
  t.rows.all fun r =>
    (ForeignKey.all α).all fun fk =>
      let tgt := hf.get fk r.val
      let inst := hf.targetEntity fk
      let name := @Entity.tableName (hf.Target fk) inst
      DbState.containsId st name tgt.toInt64

/-- One packed entity of the schema: local table check plus foreign keys. -/
def DbState.checkPacked {s : Type} [i : IsSchema s] (st : DbState s) (t : Fin i.nTables) : Bool :=
  let p := i.pack t
  let tbl := st.tables t
  have : Entity p.ty := p.entity
  @Table.check p.ty p.entity p.unique tbl &&
    @Table.fksOk s p.ty inferInstance p.entity p.foreignKey st tbl

/-- Decidable well-formedness: every schema table is present (by the Pi),
    every row decodes and is `Checked`, ids strictly increase and stay
    `< next`, unique keys are unique, foreign keys resolve, child lists
    attach. -/
def DbState.checkWF {s : Type} [i : IsSchema s] (st : DbState s) : Bool :=
  i.tables.all fun t => DbState.checkPacked st t

/-- Every row decodes and is `Checked`, and every constraint holds. -/
def DbState.WF {s : Type} [i : IsSchema s] (st : DbState s) : Prop :=
  DbState.checkWF st = true

/-- Total number of rows across every schema table. Bounds `deleteCascading`. -/
def DbState.rowCount {s : Type} [i : IsSchema s] (st : DbState s) : Nat :=
  i.tables.foldl (init := 0) fun acc t => acc + (st.tables t).rows.length

/-- Gather in-memory rows for a table list of schema `s`. Each position
    is `get`, so `Query.denote` does not need a polymorphic `Source`. -/
class GatherState (s : Type) (ts : List Type) [IsSchema s] where
  gather : DbState s → Array (Rows ts)

instance {s α : Type} [IsSchema s] [Entity α] [IsSchema.Has s α] :
    GatherState s [α] where
  gather st := (DbState.get (α := α) st).rows.toArray

instance {s α β : Type} {ts : List Type} [IsSchema s] [Entity α] [IsSchema.Has s α]
    [GatherState s (β :: ts)] : GatherState s (α :: β :: ts) where
  gather st :=
    let heads := (DbState.get (α := α) st).rows.toArray
    let tails := GatherState.gather (s := s) (ts := β :: ts) st
    heads.flatMap fun h => tails.map fun t => (h, t)

/-- Rows of `α`, via `get`. -/
def DbState.rows {s α : Type} [IsSchema s] [Entity α] [IsSchema.Has s α]
    (st : DbState s) : Array (Stored α) :=
  (st.get (α := α)).rows.toArray

/-- A `Pred.Snapshot` of every table, for quantifier denotation. -/
def DbState.snapshot {s : Type} [i : IsSchema s] (st : DbState s) : Pred.Snapshot :=
  i.tables.foldl (init := Pred.Snapshot.empty) fun snap t =>
    let p := i.pack t
    have : Entity p.ty := p.entity
    Pred.Snapshot.add (β := p.ty) snap (st.tables t).rows.toArray

end LeanDb
