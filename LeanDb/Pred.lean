import LeanDb.Select

namespace LeanDb

/-! # The typed predicate IR (LEP-0002, stage 2; LEP-0004 quantifiers)

`Pred ts` is a select predicate as data, indexed by the same table list
that types the predicate lambda. Its column references (`Pred.Col`) are
Lean values built from the generated field symbols, so a plan over a
column that does not exist, over a table not in the `select`, or against
a value of the wrong type is *unrepresentable*. `denote` gives every plan
a meaning over `Rows ts`; `approx` is the part that ships to SQL, and
`approx_sound` proves it never excludes a row the plan would accept.

This is the plan `select` carries: `leandb_plan` (`LeanDb.PlanElab`)
reifies the call-site lambda into a `Pred`, the executor sends `approx`
to SQL and still applies the lambda to what comes back (`finishRows`), so
pushdown narrows a fetch and never decides a result.

LEP-0004 adds `exists`/`forall` over a child table related by a foreign
key. Their meaning needs the child rows, so `denote` takes a `Snapshot`;
every other constructor ignores it. They render as correlated
`EXISTS`/`NOT EXISTS` subqueries, and `selectP` (`LeanDb.Db`) runs a plan
given as data — the only way to write one, since a lambda over `Rows ts`
cannot mention rows it was not given.

Two names collide with the encoded-value layer on purpose and are kept
apart by namespace: `LeanDb.Col` is a SQL value; `LeanDb.Pred.Col` is a
column reference. Inside `namespace Pred`, `Col` means the reference.
-/

/-! ## Rows, by shape

`Rows [α]` is `Stored α`, not a pair (see `LeanDb.Select`), so anything
walking a `Rows (α :: ts)` splits on `ts`. -/

/-- The head table's row. -/
def Rows.head : {α : Type} → {ts : List Type} → Rows (α :: ts) → Stored α
  | _, [], r => r
  | _, _ :: _, r => r.1

/-- The rows of every table but the head; only defined when there is one. -/
def Rows.tail {α β : Type} {ts : List Type} (r : Rows (α :: β :: ts)) : Rows (β :: ts) := r.2

/-- Prepend a row — the inverse of `head`/`tail`, splitting on `ts` as
    they do. A quantifier's body sees the child row at position 0. -/
def Rows.cons : {α : Type} → {ts : List Type} → Stored α → Rows ts → Rows (α :: ts)
  | _, [], c, _ => c
  | _, _ :: _, c, r => (c, r)

/-! ## Operators -/

/-- Null-safe equality, rendered `IS` / `IS NOT`. -/
inductive EqOp where
  | eq | ne
  deriving Repr, DecidableEq, BEq

def EqOp.sql : EqOp → String
  | .eq => "IS"
  | .ne => "IS NOT"

def EqOp.negate : EqOp → EqOp
  | .eq => .ne
  | .ne => .eq

/-- Equality in the encoded domain: `IS` on NULL means "both NULL", which
    is a fact about `LeanDb.Col` (`.null == .null`), not about `τ`. -/
def EqOp.eval : EqOp → LeanDb.Col → LeanDb.Col → Bool
  | .eq, a, b => a == b
  | .ne, a, b => a != b

/-- Ordered comparison; only ever over `SqlOrd` types. -/
inductive OrdOp where
  | lt | le | gt | ge
  deriving Repr, DecidableEq, BEq

def OrdOp.sql : OrdOp → String
  | .lt => "<"
  | .le => "<="
  | .gt => ">"
  | .ge => ">="

def OrdOp.negate : OrdOp → OrdOp
  | .lt => .ge
  | .le => .gt
  | .gt => .le
  | .ge => .lt

def OrdOp.holds : OrdOp → Ordering → Bool
  | .lt, o => o == .lt
  | .le, o => o != .gt
  | .gt, o => o == .gt
  | .ge, o => o != .lt

/-- Order of two encoded values, total: defined within one INTEGER or TEXT
    class (what SQLite's BINARY collation orders), `none` otherwise — REAL
    (NaN), NULL, or mixed classes. -/
def Col.order : LeanDb.Col → LeanDb.Col → Option Ordering
  | .int a, .int b => some (compare a b)
  | .text a, .text b => some (compare a b)
  | _, _ => none

/-- Ordered comparison in the encoded domain: `false` wherever `Col.order`
    is undefined. `ord` is denoted this way (rather than in the Lean
    domain) because `SqlOrd τ` carries no `Ord`; the `SqlOrd` law — the
    encoding preserves the type's order — is then exactly what makes this
    agree with the lambda, and `neg` exact: under the law an `ord` column
    is INTEGER/TEXT and never NULL, so `Col.order` is always `some`. -/
def OrdOp.eval (op : OrdOp) (a b : LeanDb.Col) : Bool :=
  match Col.order a b with
  | some o => op.holds o
  | none => false

namespace Pred

/-! ## Column references -/

/-- A column of one of the tables in `ts`, positionally (de Bruijn:
    `here`/`there`), with its Lean type `τ` and its STORAGE codec `i` — the
    codec that produced the bytes SQLite compares. Indexing by the codec is
    what makes `via`'s proof mean what it must. -/
inductive Col : List Type → (τ : Type) → ColCodec τ → Type 1 where
  /-- A declared field of the head table, from its symbol. The entity is
      recovered from the symbol type (`FieldOf`), so `Col.here
      Ticket.Field.title` needs no annotation. -/
  | here {F α : Type} {ts : List Type} [ent : Entity α] [fo : FieldOf F α] (f : F) :
      Col (α :: ts) (Entity.fieldTy (FieldOf.sym f)) (Entity.codec (FieldOf.sym f))
  /-- The head table's row identity (`Stored.id` / `.ref`). -/
  | id {α : Type} {ts : List Type} [ent : Entity α] : Col (α :: ts) (Id α) inferInstance
  /-- Skip one table. -/
  | there {α : Type} {ts : List Type} {τ : Type} {i : ColCodec τ} :
      Col ts τ i → Col (α :: ts) τ i
  /-- View a column through a function that is its own encoding. `h` is
      stated against the column's STORAGE codec `i`, so it says exactly
      that SQLite compares what the Lean predicate compares. `rfl` for
      any `ColCodec.via` newtype, and for `some`. -/
  | via {ts : List Type} {τ σ : Type} {i : ColCodec τ} {j : ColCodec σ}
      (c : Col ts τ i) (f : τ → σ) (h : ∀ a, i.toCol a = j.toCol (f a)) : Col ts σ j

/-- `Col [] τ i` is empty: every constructor but `via` lengthens the list,
    and `via` only re-types an existing reference. -/
theorem Col.nil_elim {τ : Type} {i : ColCodec τ} : Col [] τ i → False
  | .via c _ _ => Col.nil_elim c

/-- The storage codec, read off the index. -/
abbrev Col.codec {ts : List Type} {τ : Type} {i : ColCodec τ} (_ : Col ts τ i) : ColCodec τ := i

/-- Position of the referenced table in the `select` list. -/
def Col.tableIdx {ts : List Type} {τ : Type} {i : ColCodec τ} : Col ts τ i → Nat
  | .here (ent := _) (fo := _) _ => 0
  | .id (ent := _) => 0
  | .there c => c.tableIdx + 1
  | .via c _ _ => c.tableIdx

/-- The column name, for rendering only; `via` does not rename. -/
def Col.name {ts : List Type} {τ : Type} {i : ColCodec τ} : Col ts τ i → String
  | .here (ent := ent) (fo := fo) f => @Entity.fieldName _ ent (@FieldOf.sym _ _ ent fo f)
  | .id (ent := _) => "id"
  | .there c => c.name
  | .via c _ _ => c.name

/-- Read the column off a row. -/
def Col.proj : {ts : List Type} → {τ : Type} → {i : ColCodec τ} → Col ts τ i → Rows ts → τ
  | _, _, _, .here (ent := ent) (fo := fo) f, r =>
      @Entity.get _ ent (@FieldOf.sym _ _ ent fo f) (Rows.head r).val
  | _, _, _, .id (ent := _), r => (Rows.head r).id
  | _ :: [], _, _, .there c, _ => (Col.nil_elim c).elim
  | _ :: _ :: _, _, _, .there c, r => c.proj (Rows.tail r)
  | _, _, _, .via c f _, r => f (c.proj r)

/-! ## Snapshots (LEP-0004) -/

/-- The rows the reference semantics quantifies over: child tables, keyed
    by table name, holding rows as the database does — identity plus
    encoded columns. `rows β` reads `β`'s table back through its codec; a
    row that does not decode as `β` is not a row of `β`'s table. The
    executor fills one with `fetchAll` (`Pred.snapshot`), tests build one
    from fixtures with `add`. The constructor is private: the only ways in
    are `empty` and `add`, which encodes `Stored β` rows, so `rows β`'s
    decode is the codec's round trip and cannot lose a row for honest
    data — a hand-built snapshot cannot smuggle undecodable columns in
    and make a `forall` vacuously true.

    Rows are kept encoded rather than as `Stored β` because a total
    function *of a type* cannot return a typed array without an unchecked
    cast. The price is one decode of the child table per lookup, which
    `denote` pays once per quantifier node, not once per outer row. -/
structure Snapshot where
  private mk ::
  tables : List (String × Array (Int64 × Array LeanDb.Col))

/-- No child rows at all: every quantifier-free plan denotes the same
    under it, and `forall` is vacuous. -/
def Snapshot.empty : Snapshot := ⟨[]⟩

/-- `β`'s rows, decoded. An undecodable row is a failure, not a silent
    drop: dropping would make `forall` vacuously true over a corrupt
    snapshot (LDB-23). -/
def Snapshot.rows? (s : Snapshot) (β : Type) [Entity β] : Except DbError (Array (Stored β)) :=
  match s.tables.lookup (Entity.tableName β) with
  | none => .ok #[]
  | some raw => raw.mapM fun (id, cols) =>
      match (Entity.decode cols : Except DbError β) with
      | .ok v => .ok ⟨⟨id⟩, v⟩
      | .error e => .error e

/-- `β`'s rows, decoded. Panics on an undecodable row: the executor
    refuses those the same way, and a hand-built snapshot that smuggles
    one in must not make a `forall` vacuously true. -/
def Snapshot.rows (s : Snapshot) (β : Type) [Entity β] : Array (Stored β) :=
  match rows? s β with
  | .ok rs => rs
  | .error e => panic! s!"LeanDb.Pred.Snapshot.rows: undecodable row: {e}"

/-- Add already-encoded rows, including ones that may not decode as `β`.
    `rows?` fails instead of dropping them. -/
def Snapshot.addRaw (s : Snapshot) (table : String) (rows : Array (Int64 × Array LeanDb.Col)) :
    Snapshot :=
  ⟨(table, rows) :: s.tables⟩

/-- Add (or replace) one table's rows. -/
def Snapshot.add (s : Snapshot) (β : Type) [Entity β] (rows : Array (Stored β)) : Snapshot :=
  ⟨(Entity.tableName β, rows.map fun r => (r.id.toInt64, Entity.encode r.val)) :: s.tables⟩

end Pred

/-! ## The plan -/

/-- A select predicate as data over `Rows ts`. Three things are
    structural here that an untyped tree leaves to tactic discipline: an ordered
    comparison needs `SqlOrd τ` at the constructor (so no nullable or
    closed-enum column can appear in one, which is what makes `neg` exact);
    the comparison value is a `τ`, not a `LeanDb.Col`; and the residual is
    a leaf in the same tree.

    `ts` is an index, not a parameter: a quantifier's body is a `Pred` over
    the child table consed onto the outer list. -/
inductive Pred : List Type → Type 1 where
  | tt {ts : List Type} : Pred ts
  | ff {ts : List Type} : Pred ts
  /-- Column vs value, null-safe (`IS`/`IS NOT`). Denoted in the ENCODED
      domain, because `IS` on NULL is a fact about the encoding. -/
  | eq {ts : List Type} {τ : Type} {i : ColCodec τ} (c : Pred.Col ts τ i) (op : EqOp) (v : τ) :
      Pred ts
  /-- Ordered. `[SqlOrd τ]` AT THE CONSTRUCTOR is what makes `neg` exact.
      Denoted in the encoded domain through `Col.order` (see `OrdOp.eval`). -/
  | ord {ts : List Type} {τ : Type} {i : ColCodec τ} [so : SqlOrd τ]
      (c : Pred.Col ts τ i) (op : OrdOp) (v : τ) : Pred ts
  /-- Column vs column; across distinct tables this is a join condition. -/
  | eq2 {ts : List Type} {τ : Type} {i j : ColCodec τ}
      (a : Pred.Col ts τ i) (op : EqOp) (b : Pred.Col ts τ j) : Pred ts
  | ord2 {ts : List Type} {τ : Type} {i j : ColCodec τ} [so : SqlOrd τ]
      (a : Pred.Col ts τ i) (op : OrdOp) (b : Pred.Col ts τ j) : Pred ts
  | isNull {ts : List Type} {τ : Type} {i : ColCodec (Option τ)} (c : Pred.Col ts (Option τ) i) :
      Pred ts
  | isNotNull {ts : List Type} {τ : Type} {i : ColCodec (Option τ)}
      (c : Pred.Col ts (Option τ) i) : Pred ts
  /-- Membership in an `EnumSet` column (LEP-0003 A): `a ∈ c` when `set`,
      `a ∉ c` otherwise — one leaf, so `neg` flips the flag. Renders as a
      bit test against the variant's mask. -/
  | bit {ts : List Type} {α : Type} [ce : ClosedEnum α] {i : ColCodec (EnumSet α)}
      (c : Pred.Col ts (EnumSet α) i) (a : α) (set : Bool) : Pred ts
  /-- String prefix (LDB-14): `c` starts with `p`. Pushed as
      `(c LIKE ? ESCAPE '\' AND instr(c, ?) = 1)`, both bound — never
      interpolated. The `LIKE` (`likePattern p`) is there for the index:
      SQLite serves it as a range from a `COLLATE NOCASE` index
      (`IndexSpec.collate`). It folds ASCII case, so alone it would also
      accept `Hagrid` for `ha`; `instr(c, p) = 1` is byte-exact, so the
      conjunction is exactly `String.startsWith` and the leaf is as exact
      as `eq` — a pushed `LIMIT`, `COUNT(*)` or `EXISTS` over it is sound. -/
  | prefix {ts : List Type} {i : ColCodec String}
      (c : Pred.Col ts String i) (p : String) : Pred ts
  /-- Substring (LDB-14): `p` occurs in `c`. Pushed as
      `instr(c, ?) > 0` — byte-exact, like `String.contains`. -/
  | contains {ts : List Type} {i : ColCodec String}
      (c : Pred.Col ts String i) (p : String) : Pred ts
  /-- Case-insensitive substring (LDB-14): pushed as
      `instr(lower(c), lower(?)) > 0`. SQLite's `lower()` is ASCII-only
      without ICU, and so is Lean's `String.toLower`, so the two agree
      exactly; non-ASCII letters compare byte-exact on both sides. -/
  | icontains {ts : List Type} {i : ColCodec String}
      (c : Pred.Col ts String i) (p : String) : Pred ts
  | and {ts : List Type} (a b : Pred ts) : Pred ts
  | or {ts : List Type} (a b : Pred ts) : Pred ts
  /-- The residual, as a leaf: runs in Lean, never in SQL. -/
  | opaque {ts : List Type} (f : Rows ts → Bool) : Pred ts
  /-- Some row of `child` whose `fk` equals `parent` satisfies `body`,
      which may mention that row (position 0) and every outer row (shifted
      up by one). Both keys are typed `Id α`, so a quantifier over the
      wrong relation is unrepresentable. -/
  | «exists» {ts : List Type} {α child : Type} {i j : ColCodec (Id α)} [ent : Entity child]
      (parent : Pred.Col ts (Id α) i) (fk : Pred.Col [child] (Id α) j)
      (body : Pred (child :: ts)) : Pred ts
  /-- Every such row does. `forall` is `¬ exists ¬`; it is a constructor so
      the rendering (`NOT EXISTS … ¬body`) and the denotation are direct. -/
  | «forall» {ts : List Type} {α child : Type} {i j : ColCodec (Id α)} [ent : Entity child]
      (parent : Pred.Col ts (Id α) i) (fk : Pred.Col [child] (Id α) j)
      (body : Pred (child :: ts)) : Pred ts

instance : Inhabited (Pred ts) := ⟨.tt⟩

/-- What a plan reads: the tables and `(table, column)` pairs its pushed
    conjuncts mention, and whether a residual conjunct (whose reads the
    footprint cannot see) remains. Recorded statically per declaration by
    the plan tactic — there the table names are entity *type* names,
    resolved against the base later — and computed at run time from a
    `Pred` for the log. -/
structure Footprint where
  tables : List String := []
  columns : List (String × String) := []
  residual : Bool := false
  deriving Repr, BEq, Inhabited

namespace Footprint

private def dedup [BEq α] (xs : List α) : List α :=
  xs.foldl (fun acc x => if acc.contains x then acc else acc ++ [x]) []

def union (a b : Footprint) : Footprint :=
  { tables := dedup (a.tables ++ b.tables), columns := dedup (a.columns ++ b.columns),
    residual := a.residual || b.residual }

def isEmpty (f : Footprint) : Bool := f.tables.isEmpty && f.columns.isEmpty && !f.residual

/-- The columns of `f` among `changed`. -/
def touching (f : Footprint) (changed : List (String × String)) : List (String × String) :=
  f.columns.filter fun (t, c) => changed.any fun (t', c') => t == t' && (c == c' || c' == "*")

end Footprint

namespace Pred

/-- The footprint of a plan at run time; `names i` is the table at row
    position `i`. Quantifiers name the child table and shift the outer
    rows up by one. -/
private def colFootprint {ts : List Type} {τ : Type} {i : ColCodec τ} (names : Nat → String)
    (c : Pred.Col ts τ i) : Footprint :=
  let t := names c.tableIdx
  { tables := [t], columns := [(t, c.name)] }

partial def footprintWith {ts : List Type} (names : Nat → String) : Pred ts → Footprint
  | .tt => {}
  | .ff => {}
  | .eq c _ _ => colFootprint names c
  | .ord (so := _) c _ _ => colFootprint names c
  | .isNull c => colFootprint names c
  | .isNotNull c => colFootprint names c
  | .bit (ce := _) c _ _ => colFootprint names c
  | .prefix c _ => colFootprint names c
  | .contains c _ => colFootprint names c
  | .icontains c _ => colFootprint names c
  | .eq2 a _ b => (colFootprint names a).union (colFootprint names b)
  | .ord2 (so := _) a _ b => (colFootprint names a).union (colFootprint names b)
  | .and a b => (a.footprintWith names).union (b.footprintWith names)
  | .or a b => (a.footprintWith names).union (b.footprintWith names)
  | .opaque _ => { residual := true }
  | .exists (child := child) (ent := ent) parent fk body =>
      let childName := @Entity.tableName child ent
      let inner := fun i => if i == 0 then childName else names (i - 1)
      ((colFootprint names parent).union (colFootprint inner fk)).union
        ((body.footprintWith inner).union { tables := [childName] })
  | .forall (child := child) (ent := ent) parent fk body =>
      let childName := @Entity.tableName child ent
      let inner := fun i => if i == 0 then childName else names (i - 1)
      ((colFootprint names parent).union (colFootprint inner fk)).union
        ((body.footprintWith inner).union { tables := [childName] })

def footprint {ts : List Type} [RowsOf ts] (p : Pred ts) : Footprint :=
  let specs := RowsOf.specs ts
  p.footprintWith fun i => (specs[i]?.map (·.name)).getD s!"t{i}"

/-! ### Smart constructors -/

/-- Simplifying conjunction. -/
def andS {ts : List Type} : Pred ts → Pred ts → Pred ts
  | .tt, b => b
  | .ff, _ => .ff
  | a, .tt => a
  | _, .ff => .ff
  | a, b => .and a b

/-- Simplifying disjunction. -/
def orS {ts : List Type} : Pred ts → Pred ts → Pred ts
  | .ff, b => b
  | .tt, _ => .tt
  | a, .ff => a
  | _, .tt => .tt
  | a, b => .or a b

/-- Value/value equality. Both sides are Lean values of one type when the
    plan is built, so this always decides — in the encoded domain, with
    `IS` semantics. A closed-world case split against a captured parameter
    leaves these guards; every one folds, and the tree collapses to the
    surviving column conditions before SQL. -/
def vvEq {ts : List Type} {τ : Type} [ColCodec τ] (a : τ) (op : EqOp) (b : τ) : Pred ts :=
  if op.eval (toCol a) (toCol b) then .tt else .ff

/-- Value/value ordering. Decided now within one INTEGER/TEXT class — which
    is every case under the `SqlOrd` law. Outside it (a custom `SqlOrd`
    codec storing REAL) the leaf stays opaque so `approx` drops it and the
    lambda decides; its own denotation follows `OrdOp.eval`. -/
def vvOrd {ts : List Type} {τ : Type} [ColCodec τ] [SqlOrd τ] (a : τ) (op : OrdOp) (b : τ) : Pred ts :=
  match Col.order (toCol a) (toCol b) with
  | some o => if op.holds o then .tt else .ff
  | none => .opaque fun _ => false

/-- `∀` over the rows of `child` whose `fk` is table 0's identity — the
    common shape (`Pred.all (.here DishIngredient.Field.dish) body`). The
    key is any `Id α` column of the child, typed by unification: a symbol
    of the wrong type or of a reference to another entity does not
    elaborate. A parent reference that is not the row identity (a `Ref`
    column, a 1:1 relation the other way round) uses the constructor
    directly: `Pred.exists (.here DishIngredient.Field.ingredient) .id body`. -/
def all {ts : List Type} {α child : Type} [Entity α] [Entity child] {j : ColCodec (Id α)}
    (fk : Col [child] (Id α) j) (body : Pred (child :: α :: ts)) : Pred (α :: ts) :=
  .«forall» .id fk body

/-- `∃` over the rows of `child` whose `fk` is table 0's identity. -/
def any {ts : List Type} {α child : Type} [Entity α] [Entity child] {j : ColCodec (Id α)}
    (fk : Col [child] (Id α) j) (body : Pred (child :: α :: ts)) : Pred (α :: ts) :=
  .«exists» .id fk body

/-- Exact negation. `ord`/`ord2` flip the operator, exact by the `SqlOrd`
    argument at the constructor; `eq`/`eq2` flip `IS`/`IS NOT`; null tests
    swap; the string leaves (LDB-14) have no negated constructor, so their
    negation is the Lean predicate as an opaque leaf — exact, but left to
    the lambda; `and`/`or` by De Morgan; the quantifiers swap with their
    body negated; the residual negates its function. -/
def neg {ts : List Type} : Pred ts → Pred ts
  | .tt => .ff
  | .ff => .tt
  | .eq c op v => .eq c op.negate v
  | .ord (so := so) c op v => .ord (so := so) c op.negate v
  | .eq2 a op b => .eq2 a op.negate b
  | .ord2 (so := so) a op b => .ord2 (so := so) a op.negate b
  | .isNull c => .isNotNull c
  | .isNotNull c => .isNull c
  | .bit (ce := ce) c a set => .bit (ce := ce) c a (!set)
  | .prefix c p => .opaque fun r => !(String.startsWith (c.proj r) p)
  | .contains c p => .opaque fun r => !(String.contains (c.proj r) p)
  | .icontains c p => .opaque fun r => !((c.proj r).toLower.contains p.toLower)
  | .and a b => .or a.neg b.neg
  | .or a b => .and a.neg b.neg
  | .opaque f => .opaque fun r => !f r
  | .«exists» (ent := ent) p fk b => .«forall» (ent := ent) p fk b.neg
  | .«forall» (ent := ent) p fk b => .«exists» (ent := ent) p fk b.neg

/-! ### Denotation -/

/-- Bound `v` as SQL, or a constant 1/0 when it is outside the column's
    SQLite range. `none` from `toSql?` means the bound is larger than
    every stored value (`Nat` above `Int64.maxValue`): `<`/`≤`/`IS NOT`
    become true, `>`/`≥`/`IS` become false (LDB-18). -/
private def boundSql {τ : Type} [i : ColCodec τ] (sql : String) (outOfRangeTrue : Bool)
    (v : τ) : String × Array LeanDb.Col :=
  match i.toSql? v with
  | some c => (sql, #[c])
  | none => (if outOfRangeTrue then "1" else "0", #[])

private def boundHolds {τ : Type} [i : ColCodec τ] (eval : LeanDb.Col → LeanDb.Col → Bool)
    (outOfRange : Bool) (col v : τ) : Bool :=
  match i.toSql? v with
  | some b => eval (i.toCol col) b
  | none => outOfRange

/-- What a plan means over a row, given the child rows it may quantify
    over. `eq`/`isNull` in the encoded domain; `ord` in the encoded domain
    too (`OrdOp.eval`, see there); the residual is its function; a
    quantifier ranges over the snapshot's rows of its child whose key
    equals the parent reference (ids compare encoded, like `eq2`).

    Written as a function *of the row* built once per node, so the child
    table is decoded from the snapshot once per quantifier, not once per
    outer row. -/
def denote {ts : List Type} (snap : Snapshot) : Pred ts → Rows ts → Bool
  | .tt => fun _ => true
  | .ff => fun _ => false
  | .eq (i := i) c op v => fun r =>
      boundHolds (i := i) op.eval (op == .ne) (c.proj r) v
  | .ord (i := i) (so := _) c op v => fun r =>
      boundHolds (i := i) op.eval (op == .lt || op == .le) (c.proj r) v
  | .eq2 (i := i) (j := j) a op b => fun r => op.eval (i.toCol (a.proj r)) (j.toCol (b.proj r))
  | .ord2 (i := i) (j := j) (so := _) a op b => fun r =>
      op.eval (i.toCol (a.proj r)) (j.toCol (b.proj r))
  | .isNull (i := i) c => fun r => i.toCol (c.proj r) == .null
  | .isNotNull (i := i) c => fun r => !(i.toCol (c.proj r) == .null)
  | .bit (ce := ce) c a set => fun r => (@EnumSet.contains _ ce (c.proj r) a) == set
  | .prefix c p => fun r => String.startsWith (c.proj r) p
  | .contains c p => fun r => String.contains (c.proj r) p
  | .icontains c p => fun r => (c.proj r).toLower.contains p.toLower
  | .and a b =>
      let da := a.denote snap
      let db := b.denote snap
      fun r => da r && db r
  | .or a b =>
      let da := a.denote snap
      let db := b.denote snap
      fun r => da r || db r
  | .opaque f => f
  | .«exists» (i := i) (j := j) (child := child) (ent := ent) parent fk body =>
      let kids := @Snapshot.rows snap child ent
      let db := body.denote snap
      fun r => kids.any fun c =>
        j.toCol (fk.proj c) == i.toCol (parent.proj r) && db (Rows.cons c r)
  | .«forall» (i := i) (j := j) (child := child) (ent := ent) parent fk body =>
      let kids := @Snapshot.rows snap child ent
      let db := body.denote snap
      fun r => kids.all fun c =>
        !(j.toCol (fk.proj c) == i.toCol (parent.proj r)) || db (Rows.cons c r)

/-- Every opaque leaf weakened to `true`, simplifying as it goes. Monotone
    recursion suffices: `and`/`or` and both quantifiers are monotone in
    their sub-plans, so weakening each upward weakens the whole upward. -/
def approx {ts : List Type} : Pred ts → Pred ts
  | .and a b => andS a.approx b.approx
  | .or a b => orS a.approx b.approx
  | .opaque _ => .tt
  | .«exists» (ent := ent) p fk b => .«exists» (ent := ent) p fk b.approx
  | .«forall» (ent := ent) p fk b => .«forall» (ent := ent) p fk b.approx
  | p => p

/-- Opaque leaves: the conjuncts left to the lambda, quantifier bodies
    included. -/
def residuals {ts : List Type} : Pred ts → Nat
  | .opaque _ => 1
  | .and a b => a.residuals + b.residuals
  | .or a b => a.residuals + b.residuals
  | .«exists» (ent := _) _ _ b => b.residuals
  | .«forall» (ent := _) _ _ b => b.residuals
  | _ => 0

def hasOpaque {ts : List Type} (p : Pred ts) : Bool := p.residuals != 0

theorem denote_andS {ts : List Type} (snap : Snapshot) (a b : Pred ts) (r : Rows ts) :
    (andS a b).denote snap r = (a.denote snap r && b.denote snap r) := by
  unfold andS
  split <;> simp [denote]

theorem denote_orS {ts : List Type} (snap : Snapshot) (a b : Pred ts) (r : Rows ts) :
    (orS a b).denote snap r = (a.denote snap r || b.denote snap r) := by
  unfold orS
  split <;> simp [denote]

/-- `Array.any` is monotone in its predicate. -/
theorem any_mono {α : Type} {xs : Array α} {f g : α → Bool}
    (h : ∀ x, f x = true → g x = true) (hx : xs.any f = true) : xs.any g = true := by
  rw [Array.any_eq_true] at *
  obtain ⟨i, hi, hf⟩ := hx
  exact ⟨i, hi, h _ hf⟩

/-- `Array.all` is monotone in its predicate. -/
theorem all_mono {α : Type} {xs : Array α} {f g : α → Bool}
    (h : ∀ x, f x = true → g x = true) (hx : xs.all f = true) : xs.all g = true := by
  rw [Array.all_eq_true] at *
  intro i hi
  exact h _ (hx i hi)

/-- No over-narrowing: whatever the plan accepts, its pushable projection
    accepts — under any snapshot. This is the property the strict/lenient
    split of the tactic argues for; here it is a theorem, once. The
    quantifier cases are `Array.any`/`all` monotonicity over the body. -/
theorem approx_sound {ts : List Type} (snap : Snapshot) : ∀ (p : Pred ts) (r : Rows ts),
    p.denote snap r = true → p.approx.denote snap r = true
  | .and a b, r, h => by
      have h' : a.denote snap r = true ∧ b.denote snap r = true := by simpa [denote] using h
      show (andS a.approx b.approx).denote snap r = true
      rw [denote_andS, approx_sound snap a r h'.1, approx_sound snap b r h'.2]
      rfl
  | .or a b, r, h => by
      have h' : a.denote snap r = true ∨ b.denote snap r = true := by simpa [denote] using h
      show (orS a.approx b.approx).denote snap r = true
      rw [denote_orS]
      rcases h' with h' | h'
      · rw [approx_sound snap a r h']
        rfl
      · rw [approx_sound snap b r h', Bool.or_true]
  | .«exists» (ent := ent) parent fk body, r, h => by
      show denote snap (.«exists» (ent := ent) parent fk body.approx) r = true
      simp only [denote] at h ⊢
      refine any_mono (fun c hc => ?_) h
      rw [Bool.and_eq_true] at hc ⊢
      exact ⟨hc.1, approx_sound snap body _ hc.2⟩
  | .«forall» (ent := ent) parent fk body, r, h => by
      show denote snap (.«forall» (ent := ent) parent fk body.approx) r = true
      simp only [denote] at h ⊢
      refine all_mono (fun c hc => ?_) h
      rw [Bool.or_eq_true] at hc ⊢
      rcases hc with hc | hc
      · exact Or.inl hc
      · exact Or.inr (approx_sound snap body _ hc)
  | .opaque _, _, _ => rfl
  | .tt, _, h => h
  | .ff, _, h => h
  | .eq .., _, h => h
  | .ord (so := _) .., _, h => h
  | .eq2 .., _, h => h
  | .ord2 (so := _) .., _, h => h
  | .isNull .., _, h => h
  | .isNotNull .., _, h => h
  | .bit (ce := _) .., _, h => h
  -- the string leaves (LDB-14) are kept verbatim by `approx`, so their
  -- pushed form denotes exactly what the plan denotes
  | .prefix .., _, h => h
  | .contains .., _, h => h
  | .icontains .., _, h => h

/-- `hasOpaque = false` means `residuals = 0`. -/
theorem residuals_eq_zero_of_not_opaque {ts : List Type} {p : Pred ts}
    (h : p.hasOpaque = false) : p.residuals = 0 := by
  simp only [hasOpaque] at h
  cases hr : p.residuals with
  | zero => rfl
  | succ _ => simp [hr] at h

/-- No opaque leaf ⇒ `approx` denotes the same as `pred`. Structural
    equality `approx = pred` fails because `approx` uses `andS`/`orS`,
    which collapse `tt`/`ff`; denotational equality is the sound law
    (pushed windows and counts). -/
theorem approx_eq_denote {ts : List Type} (snap : Snapshot) :
    ∀ (p : Pred ts), p.hasOpaque = false →
      ∀ r : Rows ts, p.approx.denote snap r = p.denote snap r
  | .tt, _, _ => rfl
  | .ff, _, _ => rfl
  | .eq .., _, _ => rfl
  | .ord (so := _) .., _, _ => rfl
  | .eq2 .., _, _ => rfl
  | .ord2 (so := _) .., _, _ => rfl
  | .isNull .., _, _ => rfl
  | .isNotNull .., _, _ => rfl
  | .bit (ce := _) .., _, _ => rfl
  | .prefix .., _, _ => rfl
  | .contains .., _, _ => rfl
  | .icontains .., _, _ => rfl
  | .opaque _, h, _ => by
      have : (1 : Nat) = 0 := residuals_eq_zero_of_not_opaque (p := .opaque _) h
      cases this
  | .and a b, h, r => by
      have hz : a.residuals + b.residuals = 0 := by
        simpa [residuals] using residuals_eq_zero_of_not_opaque (p := .and a b) h
      have ⟨ha0, hb0⟩ := Nat.add_eq_zero_iff.mp hz
      have ha : a.hasOpaque = false := by simp [hasOpaque, ha0]
      have hb : b.hasOpaque = false := by simp [hasOpaque, hb0]
      simp only [approx]
      rw [denote_andS, approx_eq_denote snap a ha r, approx_eq_denote snap b hb r]
      simp [denote]
  | .or a b, h, r => by
      have hz : a.residuals + b.residuals = 0 := by
        simpa [residuals] using residuals_eq_zero_of_not_opaque (p := .or a b) h
      have ⟨ha0, hb0⟩ := Nat.add_eq_zero_iff.mp hz
      have ha : a.hasOpaque = false := by simp [hasOpaque, ha0]
      have hb : b.hasOpaque = false := by simp [hasOpaque, hb0]
      simp only [approx]
      rw [denote_orS, approx_eq_denote snap a ha r, approx_eq_denote snap b hb r]
      simp [denote]
  | .«exists» (ent := ent) parent fk body, h, r => by
      have hb0 : body.residuals = 0 := by
        simpa [residuals] using residuals_eq_zero_of_not_opaque
          (p := .«exists» (ent := ent) parent fk body) h
      have hb : body.hasOpaque = false := by simp [hasOpaque, hb0]
      have hpt : ∀ c, body.approx.denote snap (Rows.cons c r) =
          body.denote snap (Rows.cons c r) :=
        fun c => approx_eq_denote snap body hb _
      simp [approx, denote, hpt]
  | .«forall» (ent := ent) parent fk body, h, r => by
      have hb0 : body.residuals = 0 := by
        simpa [residuals] using residuals_eq_zero_of_not_opaque
          (p := .«forall» (ent := ent) parent fk body) h
      have hb : body.hasOpaque = false := by simp [hasOpaque, hb0]
      have hpt : ∀ c, body.approx.denote snap (Rows.cons c r) =
          body.denote snap (Rows.cons c r) :=
        fun c => approx_eq_denote snap body hb _
      simp [approx, denote, hpt]

end Pred

/-- Encoding preserves Lean order. `SqlOrd` itself is a marker; this law
    is what makes a pushed `<`/`≤`/`>`/`≥` agree with the lambda. -/
class LawfulSqlOrd (α : Type) [ColCodec α] [SqlOrd α] [Ord α] : Prop where
  order_toCol : ∀ a b : α, Col.order (toCol (α := α) a) (toCol (α := α) b) = some (compare a b)

instance : LawfulSqlOrd Int64 where
  order_toCol _ _ := rfl

instance : LawfulSqlOrd String where
  order_toCol _ _ := rfl

instance : LawfulSqlOrd Bool where
  order_toCol a b := by
    cases a <;> cases b <;> rfl

instance : LawfulSqlOrd (Id α) where
  order_toCol a b := by
    -- `toCol` is `Col.int a.toInt64`; `compare` on `Id` is `compare` on `Int64`.
    change Col.order (Col.int a.toInt64) (Col.int b.toInt64) = some (compare a.toInt64 b.toInt64)
    rfl

/-- `SqlOrd Nat` is sound on `0 … Int64.maxValue`; above that `toCol` clamps. -/
theorem nat_order_toCol (n m : Nat) (hn : n ≤ natSqlMax) (hm : m ≤ natSqlMax) :
    Col.order (toCol (α := Nat) n) (toCol (α := Nat) m) = some (compare n m) := by
  have hn' := nat_lt_two_pow_63_of_le_max hn
  have hm' := nat_lt_two_pow_63_of_le_max hm
  have hencn : toCol (α := Nat) n = Col.int (Int64.ofNat n) := by
    change Col.int ((natToSql n).getD Int64.maxValue) = Col.int (Int64.ofNat n)
    rw [natToSql_of_le hn]; rfl
  have hencm : toCol (α := Nat) m = Col.int (Int64.ofNat m) := by
    change Col.int ((natToSql m).getD Int64.maxValue) = Col.int (Int64.ofNat m)
    rw [natToSql_of_le hm]; rfl
  rw [hencn, hencm]
  change some (compare (Int64.ofNat n) (Int64.ofNat m)) = some (compare n m)
  congr 1
  have hinj : Int64.ofNat n = Int64.ofNat m ↔ n = m := by
    constructor
    · intro heq
      have := congrArg Int64.toNatClampNeg heq
      rw [Int64.toNatClampNeg_ofNat_of_lt hn', Int64.toNatClampNeg_ofNat_of_lt hm'] at this
      exact this
    · intro heq
      rw [heq]
  simp [compare, compareOfLessAndEq, Int64.ofNat_lt_iff_lt hn' hm', hinj]

namespace Pred

/-! ### The plan surface -/

/-- Table indices a predicate touches. A quantifier touches its parent's
    table and every *outer* table its body references (body indices ≥ 1,
    shifted down); the child is not a table of the select. -/
def tables {ts : List Type} : Pred ts → List Nat
  | .tt | .ff | .opaque _ => []
  | .eq c .. => [c.tableIdx]
  | .ord (so := _) c .. => [c.tableIdx]
  | .isNull c => [c.tableIdx]
  | .isNotNull c => [c.tableIdx]
  | .bit (ce := _) c .. => [c.tableIdx]
  | .prefix c .. => [c.tableIdx]
  | .contains c .. => [c.tableIdx]
  | .icontains c .. => [c.tableIdx]
  | .eq2 a _ b => [a.tableIdx, b.tableIdx]
  | .ord2 (so := _) a _ b => [a.tableIdx, b.tableIdx]
  | .and a b | .or a b => (a.tables ++ b.tables).eraseDups
  | .«exists» (ent := _) p _ b => (p.tableIdx :: b.tables.filterMap outer).eraseDups
  | .«forall» (ent := _) p _ b => (p.tableIdx :: b.tables.filterMap outer).eraseDups
where
  /-- A body index as an outer index: the child (0) is not one. -/
  outer : Nat → Option Nat
    | 0 => none
    | n + 1 => some n

/-- Does the predicate relate two distinct tables? For a quantifier: does
    it, through its parent and its body, touch more than one outer table. -/
def hasJoin {ts : List Type} : Pred ts → Bool
  | .eq2 a _ b => a.tableIdx != b.tableIdx
  | .ord2 (so := _) a _ b => a.tableIdx != b.tableIdx
  | .and a b | .or a b => a.hasJoin || b.hasJoin
  | q@(.«exists» (ent := _) ..) => q.tables.length > 1
  | q@(.«forall» (ent := _) ..) => q.tables.length > 1
  | _ => false

/-- Top-level conjuncts. -/
def conjuncts {ts : List Type} : Pred ts → List (Pred ts)
  | .and a b => a.conjuncts ++ b.conjuncts
  | .tt => []
  | p => [p]

/-- The part of the predicate pushable onto table `i` alone: the top-level
    conjuncts that touch only `i`. Dropping the rest only widens the fetch
    — never wrong. The result stays a `Pred ts`; the single-table fetch
    renders it with every index aliased to its one table. -/
def forTable {ts : List Type} (i : Nat) (p : Pred ts) : Pred ts :=
  (p.conjuncts.filter fun c => c.tables == [i]).foldl andS .tt

/-- The quantified child entities, packed with their instances and
    deduplicated by table name — what the executor's snapshot fetch
    iterates over. -/
def children {ts : List Type} : Pred ts → List ((β : Type) × Entity β)
  | .and a b | .or a b => dedup (a.children ++ b.children)
  | .«exists» (child := child) (ent := ent) _ _ b => dedup (⟨child, ent⟩ :: b.children)
  | .«forall» (child := child) (ent := ent) _ _ b => dedup (⟨child, ent⟩ :: b.children)
  | _ => []
where
  dedup (xs : List ((β : Type) × Entity β)) : List ((β : Type) × Entity β) :=
    xs.foldl (init := []) fun acc x =>
      if acc.any (fun y => @Entity.tableName y.1 y.2 == @Entity.tableName x.1 x.2) then acc
      else acc ++ [x]

/-- Node count: `render`'s termination measure. `neg` preserves it
    (`size_neg`). -/
def size {ts : List Type} : Pred ts → Nat
  | .and a b | .or a b => a.size + b.size + 1
  | .«exists» (ent := _) _ _ b => b.size + 1
  | .«forall» (ent := _) _ _ b => b.size + 1
  | _ => 1

theorem size_neg {ts : List Type} : ∀ p : Pred ts, p.neg.size = p.size
  | .tt | .ff | .opaque _ => rfl
  | .eq .. | .eq2 .. | .isNull .. | .isNotNull .. => rfl
  | .ord (so := _) .. | .ord2 (so := _) .. => rfl
  | .bit (ce := _) .. => rfl
  | .prefix .. | .contains .. | .icontains .. => rfl
  | .and a b => by simp [neg, size, size_neg a, size_neg b]
  | .or a b => by simp [neg, size, size_neg a, size_neg b]
  | .«exists» (ent := _) _ _ b => by simp [neg, size, size_neg b]
  | .«forall» (ent := _) _ _ b => by simp [neg, size, size_neg b]

/-- Escape `p` for `LIKE … ESCAPE '\'` and append `%`: a literal `\`, `%`
    or `_` in `p` must reach SQLite as `\x`, so `LIKE` matches the
    character itself instead of a wildcard. The result is bound as a
    parameter, never interpolated. -/
def likePattern (p : String) : String :=
  ((p.replace "\\" "\\\\").replace "%" "\\%").replace "_" "\\_" ++ "%"

/-- Render as SQL. `aliasOf` names the table at each index (`t0…` for the
    executors); `depth` numbers nested subquery aliases `s0, s1, …`.
    Returns the SQL and the bind values in placeholder order. Total: an
    opaque leaf renders as `1` — callers pass `p.approx`, which has none.

    `not = true` renders the NEGATION of the subtree, structurally:
    operators flip, `and`/`or` trade places, quantifiers swap. This is
    how `forall` renders its body (`NOT EXISTS`). Every leaf's SQL is
    exact, so its negated rendering is exact too. The string leaves
    (LDB-14) need this path: `neg` has no pushed form for them (it makes
    them opaque, which renders as `1`).

    For every constructor the engine predates LDB-14, `render … true`
    produces exactly what `p.neg.render` produced.

    `exists` is a correlated subquery: inside it the child is table 0
    (`s{depth}`) and every outer index shifts up by one. `forall` is
    `NOT EXISTS` of the negated body (rendered with `not = true`) — there
    is no textual `NOT (…)`. -/
def render {ts : List Type} (aliasOf : Nat → String) (depth : Nat := 0) (not : Bool := false) :
    Pred ts → String × Array LeanDb.Col
  | .tt => (if not then "0" else "1", #[])
  | .ff => (if not then "1" else "0", #[])
  | .eq (i := i) c op v =>
      let op := if not then op.negate else op
      boundSql (i := i) s!"{col aliasOf c} {op.sql} ?" (op == .ne) v
  | .ord (i := i) (so := _) c op v =>
      let op := if not then op.negate else op
      boundSql (i := i) s!"{col aliasOf c} {op.sql} ?" (op == .lt || op == .le) v
  | .eq2 a op b =>
      -- col/col comparison: `IS`/`IS NOT` are valid SQLite binary operators
      (s!"{col aliasOf a} {(if not then op.negate else op).sql} {col aliasOf b}", #[])
  | .ord2 (so := _) a op b =>
      (s!"{col aliasOf a} {(if not then op.negate else op).sql} {col aliasOf b}", #[])
  | .isNull c => (s!"{col aliasOf c}{if not then " IS NOT NULL" else " IS NULL"}", #[])
  | .isNotNull c => (s!"{col aliasOf c}{if not then " IS NULL" else " IS NOT NULL"}", #[])
  | .bit (ce := ce) c a set =>
      let bind := LeanDb.Col.int (Int64.ofNat (@EnumSet.bitOf _ ce a).toNat)
      let set := if not then !set else set
      (s!"(({col aliasOf c} & ?) {if set then "!=" else "="} 0)", #[bind])
  -- LDB-14: every parameter is bound. `prefix` is the index-friendly
  -- `LIKE` narrowed by the exact `instr(…) = 1` (see `prefix`), and its
  -- negation is the De Morgan dual. `instr` is byte-exact against
  -- `String.contains`; `lower` is ASCII-only on both sides (SQLite without
  -- ICU, Lean `String.toLower`), so `icontains` is exact too.
  | .prefix c p =>
      let cs := col aliasOf c
      (if not then s!"({cs} NOT LIKE ? ESCAPE '\\' OR instr({cs}, ?) != 1)"
        else s!"({cs} LIKE ? ESCAPE '\\' AND instr({cs}, ?) = 1)",
        #[.text (likePattern p), .text p])
  | .contains c p =>
      (s!"instr({col aliasOf c}, ?){if not then " =" else " >"} 0", #[.text p])
  | .icontains c p =>
      (s!"instr(lower({col aliasOf c}), lower(?)){if not then " =" else " >"} 0", #[.text p])
  | .and a b =>
      let (sa, ba) := a.render aliasOf depth not
      let (sb, bb) := b.render aliasOf depth not
      (s!"({sa} {if not then "OR" else "AND"} {sb})", ba ++ bb)
  | .or a b =>
      let (sa, ba) := a.render aliasOf depth not
      let (sb, bb) := b.render aliasOf depth not
      (s!"({sa} {if not then "AND" else "OR"} {sb})", ba ++ bb)
  | .opaque _ => ("1", #[])
  | .«exists» (child := child) (ent := ent) parent fk body =>
      let s := s!"s{depth}"
      -- ¬∃(fk ∧ b) = NOT EXISTS(fk ∧ b): the body stays positive
      let (bs, bb) := body.render (fun | 0 => s | n + 1 => aliasOf n) (depth + 1) false
      let q := if not then "NOT EXISTS" else "EXISTS"
      (s!"{q} ({subquery (@Entity.tableName child ent) s fk.name (col aliasOf parent) bs})", bb)
  | .«forall» (child := child) (ent := ent) parent fk body =>
      let s := s!"s{depth}"
      -- ∀(fk → b) = NOT EXISTS(fk ∧ ¬b); ¬∀(fk → b) = EXISTS(fk ∧ ¬b)
      let (bs, bb) := body.render (fun | 0 => s | n + 1 => aliasOf n) (depth + 1) true
      let q := if not then "EXISTS" else "NOT EXISTS"
      (s!"{q} ({subquery (@Entity.tableName child ent) s fk.name (col aliasOf parent) bs})", bb)
termination_by p => p.size
decreasing_by all_goals (simp [size]; try omega)
where
  col {ts : List Type} {τ : Type} {i : ColCodec τ} (aliasOf : Nat → String) (c : Col ts τ i) :
      String :=
    /- `quoteIdent`, not a bare `\"…\"`: an escaped Lean field name
       (`«a"b»`) is a legal column name, and its embedded quotes must stay
       inside the quoted identifier, exactly as the DDL quotes them. -/
    s!"{aliasOf c.tableIdx}.{quoteIdent c.name}"
  /-- The correlated subquery: `child`'s rows, as `s`, whose `fk` is the
      outer `parent`, narrowed by the rendered `body`. -/
  subquery (table s fk parent body : String) : String :=
    s!"SELECT 1 FROM {quoteIdent table} AS {s} WHERE {s}.{quoteIdent fk} IS {parent} AND {body}"

/-- The executors' aliases: table `n` is `tn`. -/
def tAlias (n : Nat) : String := s!"t{n}"

/-- `render` under the executors' aliases — what `describe` logs. -/
def renderT {ts : List Type} (p : Pred ts) : String × Array LeanDb.Col := p.render tAlias

/-- The human form logged per `select`: the SQL of the pushable projection
    and the number of conjuncts left to the lambda. -/
def describe {ts : List Type} (p : Pred ts) : String :=
  s!"pushed: {p.approx.renderT.1}, residual conjuncts: {p.residuals}"

/-- Exactly `tt`: nothing to push, so a fetch needs no `WHERE` at all. -/
def isTrivial {ts : List Type} : Pred ts → Bool
  | .tt => true
  | _ => false

end Pred

/-- Marker type carrying the predicate in its *type*, so the `leandb_plan`
    default-argument tactic can reflect the actual call-site lambda from
    its goal. Runtime-wise this is just `Pred ts`. -/
def PlanFor {ts : List Type} (_where' : Rows ts → Bool) : Type 1 := Pred ts

instance {ts : List Type} {w : Rows ts → Bool} : Inhabited (PlanFor w) := ⟨(.tt : Pred ts)⟩

def PlanFor.plan {ts : List Type} {w : Rows ts → Bool} (p : PlanFor w) : Pred ts := p

end LeanDb
