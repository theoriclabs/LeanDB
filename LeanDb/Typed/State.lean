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

/-- A table's contents: the AUTOINCREMENT counter, and rows with their
    invariant proofs. `get`/`set` transport along `ty_eq` with
    `Has.entity_eq` (not bare `▸`, which cannot synthesize `Entity`
    for the motive's bound type). -/
structure Table (α : Type) [Entity α] where
  next : Nat := 1
  rows : List (Valid α) := []

/-- Transport `Table` along `ty_eq` given `entity_eq`. Reduces on `rfl`. -/
def Table.cast {α β : Type} {ea : Entity α} {eb : Entity β}
    (e : α = β) (he : (e ▸ ea : Entity β) = eb) (t : @Table α ea) : @Table β eb :=
  match e, he with
  | rfl, rfl => t

theorem Entity.eq_symm {α β : Type} {ea : Entity α} {eb : Entity β}
    (e : α = β) (he : (e ▸ ea : Entity β) = eb) :
    (e.symm ▸ eb : Entity α) = ea :=
  match e, he with
  | rfl, rfl => rfl

/-- The whole database: one table per entity of `s`. The Pi lives in
    `Type` because each `Table _` does, so `DbState s` is a `DbM` result. -/
structure DbState (s : Type) [i : IsSchema s] : Type where
  tables : (t : Fin i.nTables) → @Table (i.pack t).ty (i.pack t).entity

/-- Walk of `idsOk`. `next` is the AUTOINCREMENT counter. -/
def Table.idsOk.go [Entity α] (next : Nat) : Option Int64 → List (Valid α) → Bool
  | _, [] => true
  | prev, r :: rs =>
      let id := r.id.toInt64
      let ordered := match prev with
        | none => true
        | some p => p < id
      let inRange := (0 : Int64) < id && id.toNatClampNeg < next
      ordered && inRange && Table.idsOk.go next (some id) rs

/-- Ids strictly increase, are positive, and stay below `next`. -/
def Table.idsOk [Entity α] (t : Table α) : Bool :=
  Table.idsOk.go t.next none t.rows

/-- AUTOINCREMENT counter is at least 1 and at most one past the largest
    SQLite INTEGER (`natSqlMax + 1`). `next = natSqlMax + 1` means every
    representable id has been issued; a further `insert` must not wrap
    `Int64.ofNat`. Empty tables start at 1. -/
def Table.nextOk [Entity α] (t : Table α) : Bool :=
  1 ≤ t.next && t.next ≤ natSqlMax + 1

/-- Every `Ref` / `Option (Ref)` on a stored row is unset or at least 1.
    Combined with `idsOk`, apps can map issued ids to `Nat` without a
    non-negativity hypothesis (`Id.toNat`). -/
def Table.refsOk [Entity α] [HasForeignKey α] (t : Table α) : Bool :=
  t.rows.all fun r =>
    (ForeignKey.all α).all fun fk =>
      match ForeignKey.get fk r.val with
      | none => true
      | some tgt => Id.positive tgt

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

/-- Keys of `ix` are pairwise distinct on this list. -/
def Table.uniquesOk.distinct [Entity α] [HasUnique α] (ix : Unique α) :
    List (Valid α) → Bool
  | [] => true
  | r :: rs =>
      let enc := Unique.encodeKey ix (Unique.keyOf ix r.val)
      rs.all (fun o => Unique.encodeKey ix (Unique.keyOf ix o.val) != enc) &&
        Table.uniquesOk.distinct ix rs

/-- Unique-index keys are unique among rows. -/
def Table.uniquesOk [Entity α] [HasUnique α] (t : Table α) : Bool :=
  (Unique.all α).all fun ix => Table.uniquesOk.distinct ix t.rows

/-- Local well-formedness of one table (ids, decode, Checked, children,
    unique keys, AUTOINCREMENT range). Foreign keys need the whole `DbState`. -/
def Table.check [Entity α] [HasUnique α] [HasForeignKey α] (t : Table α) : Bool :=
  t.nextOk && t.idsOk && t.refsOk && t.invariantsOk && t.decodesOk && t.checkedOk &&
    t.childrenOk && t.uniquesOk

def Table.WF [Entity α] [HasUnique α] [HasForeignKey α] (t : Table α) : Prop :=
  t.check = true

/-- Empty table for a packed entity (the instance is `p.entity`, not synthesized). -/
def Table.ofPacked (p : PackedEntity) (next : Nat := 1)
    (rows : List (@Valid p.ty p.entity) := []) : @Table p.ty p.entity :=
  @Table.mk p.ty p.entity next rows

/-- Drop the row with this id, keeping the packed `Entity` instance. -/
def Table.eraseIdP (p : PackedEntity) (t : @Table p.ty p.entity) (id : Int64) :
    @Table p.ty p.entity :=
  Table.ofPacked p (@Table.next p.ty p.entity t)
    ((@Table.rows p.ty p.entity t).filter fun r =>
      (@Valid.id p.ty p.entity r).toInt64 != id)

/-- No rows, every AUTOINCREMENT counter at 1. -/
def DbState.empty {s : Type} [i : IsSchema s] : DbState s where
  tables := fun t => Table.ofPacked (i.pack t)

/-- Rows of `α` in this state. `α` must be a table of `s`. -/
def DbState.get {s α : Type} [i : IsSchema s] [ent : Entity α] [h : IsSchema.Has s α]
    (st : DbState s) : Table α :=
  Table.cast h.ty_eq h.entity_eq (st.tables h.id)

/-- Replace the table for `α` by function update. -/
def DbState.set {s α : Type} [i : IsSchema s] [ent : Entity α] [h : IsSchema.Has s α]
    (st : DbState s) (tbl : Table α) : DbState s where
  tables := fun t =>
    if hEq : t = h.id then
      hEq.symm ▸ Table.cast h.ty_eq.symm (Entity.eq_symm h.ty_eq h.entity_eq) tbl
    else
      st.tables t

/-- Direct access by schema-table index. -/
def DbState.getAt {s : Type} [i : IsSchema s] (st : DbState s) (t : Fin i.nTables) :
    @Table (i.pack t).ty (i.pack t).entity :=
  st.tables t

/-- The inbound-key source table, transported along `sourceTy_eq`. -/
def DbState.getSource {s α : Type} [i : IsSchema s] [h : HasReferencedBy s α]
    (st : DbState s) (r : h.ReferencedBy) : @Table (h.Source r) (h.sourceEntity r) :=
  Table.cast (h.sourceTy_eq r) (h.sourceEntity_eq r) (st.tables (h.sourceId r))

/-- `Table.cast` along `e` then `e.symm` is the identity. -/
private theorem Table.cast_cancel {α β : Type} {ea : Entity α} {eb : Entity β}
    (e : α = β) (he : e ▸ ea = eb) (t : @Table β eb) :
    Table.cast e he (Table.cast e.symm (Entity.eq_symm e he) t) = t := by
  cases e
  cases he
  rfl

private theorem Table.cast_nil_rows {α β : Type} {ea : Entity α} {eb : Entity β}
    (e : α = β) (he : (e ▸ ea : Entity β) = eb) :
    (Table.cast e he ({ next := 1, rows := [] } : @Table α ea)).rows = [] := by
  cases e
  cases he
  rfl

private theorem Table.cast_nil_next {α β : Type} {ea : Entity α} {eb : Entity β}
    (e : α = β) (he : (e ▸ ea : Entity β) = eb) :
    (Table.cast e he ({ next := 1, rows := [] } : @Table α ea)).next = 1 := by
  cases e
  cases he
  rfl

theorem DbState.get_set_same {s α : Type} [i : IsSchema s] [ent : Entity α]
    [h : IsSchema.Has s α] (st : DbState s) (tbl : Table α) :
    DbState.get (α := α) (st.set tbl) = tbl := by
  unfold DbState.get DbState.set
  simp only [dif_pos]
  exact Table.cast_cancel h.ty_eq h.entity_eq tbl

theorem DbState.get_set_other {s α β : Type} [i : IsSchema s]
    [Entity α] [Entity β] [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (st : DbState s) (tbl : Table α) (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β) (st.set (α := α) tbl) = DbState.get (α := β) st := by
  unfold DbState.get DbState.set
  simp [dif_neg (Ne.symm hneq)]

/-- `set` is function update: every packed slot except `α`'s is unchanged. -/
theorem DbState.set_tables_other {s α : Type} [i : IsSchema s] [Entity α]
    [h : IsSchema.Has s α] (st : DbState s) (tbl : Table α)
    (t : Fin i.nTables) (hne : t ≠ h.id) :
    (st.set (α := α) tbl).tables t = st.tables t := by
  unfold DbState.set
  simp [dif_neg hne]

theorem DbState.empty_rows {s α : Type} [i : IsSchema s] [ent : Entity α]
    [h : IsSchema.Has s α] :
    (DbState.get (α := α) (DbState.empty (s := s))).rows = [] := by
  unfold DbState.get DbState.empty
  simp only [Table.ofPacked]
  exact Table.cast_nil_rows h.ty_eq h.entity_eq

theorem DbState.empty_next {s α : Type} [i : IsSchema s] [ent : Entity α]
    [h : IsSchema.Has s α] :
    (DbState.get (α := α) (DbState.empty (s := s))).next = 1 := by
  unfold DbState.get DbState.empty
  simp only [Table.ofPacked]
  exact Table.cast_nil_next h.ty_eq h.entity_eq

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
    (packed : List (Σ t : Fin i.nTables, @Table (i.pack t).ty (i.pack t).entity)) : DbState s where
  tables := fun t =>
    let rec find : List (Σ t : Fin i.nTables, @Table (i.pack t).ty (i.pack t).entity) →
        @Table (i.pack t).ty (i.pack t).entity
      | [] => Table.ofPacked (i.pack t)
      | ⟨t', tbl⟩ :: rest =>
          if h : t' = t then h ▸ tbl else find rest
    find packed

/-- Wrap a decoded row; invariant failure is corruption, never a stored row. -/
def Valid.ofStoredM [Entity α] (r : Stored α) : Db (Valid α) :=
  match Valid.ofStored? r with
  | some v => (Pure.pure (f := Db) v)
  | none => throw (.invariant (Entity.tableName α) "Valid.ofStored?")

/-- Read every table of `s` in id order, under one deferred snapshot. -/
def DbState.load {s : Type} [i : IsSchema s] : Db (DbState s) :=
  readSnapshot do
    let packed ← i.tables.toList.mapM fun t => do
      let p := i.pack t
      let rows ← @fetchAll p.ty p.entity
      let next ← @DbState.loadNext p.ty p.entity rows
      let wrapped ← rows.toList.mapM (@Valid.ofStoredM p.ty p.entity)
      pure (⟨t, Table.ofPacked p next wrapped⟩ :
        Σ t : Fin i.nTables, @Table (i.pack t).ty (i.pack t).entity)
    return DbState.ofList packed

/-- Whether any schema table named `tableName` contains `id`. -/
def DbState.containsId {s : Type} [i : IsSchema s] (st : DbState s)
    (tableName : String) (id : Int64) : Bool :=
  i.tables.any fun t =>
    let p := i.pack t
    @Entity.tableName p.ty p.entity == tableName &&
      (@Table.rows p.ty p.entity (st.tables t)).any fun row =>
        (@Valid.id p.ty p.entity row).toInt64 == id

/-- Every foreign key of `α` resolves to a row in the target table. A
    nullable `Option (Ref)` that is `none` is vacuously ok. -/
def Table.fksOk {s α : Type} [IsSchema s] [Entity α] [hf : HasForeignKey α]
    (st : DbState s) (t : Table α) : Bool :=
  t.rows.all fun r =>
    (ForeignKey.all α).all fun fk =>
      match hf.get fk r.val with
      | none => true
      | some tgt =>
          let inst := hf.targetEntity fk
          let name := @Entity.tableName (hf.Target fk) inst
          DbState.containsId st name tgt.toInt64

/-- One packed entity of the schema: local table check plus foreign keys. -/
def DbState.checkPacked {s : Type} [i : IsSchema s] (st : DbState s) (t : Fin i.nTables) : Bool :=
  let p := i.pack t
  let tbl := st.tables t
  @Table.check p.ty p.entity p.unique p.foreignKey tbl &&
    @Table.fksOk s p.ty inferInstance p.entity p.foreignKey st tbl

/-- Decidable well-formedness: every schema table is present (by the Pi),
    every row decodes and is `Checked`, ids and `Ref`s are ≥ 1 and ids
    stay `< next`, the AUTOINCREMENT counter is `1 ≤ next ≤ natSqlMax + 1`,
    unique keys are unique, foreign keys resolve, child lists attach. -/
def DbState.checkWF {s : Type} [i : IsSchema s] (st : DbState s) : Bool :=
  i.tables.all fun t => DbState.checkPacked st t

/-- Every row decodes and is `Checked`, and every constraint holds. -/
def DbState.WF {s : Type} [i : IsSchema s] (st : DbState s) : Prop :=
  DbState.checkWF st = true

/-- `load` plus a `checkWF` gate. `load` itself checks the entity
    invariant on every decoded row (`Valid.ofStoredM`) but not unique
    indexes or foreign keys; this wrapper refuses a state that is not
    `WF`. LeanDB writes preserve `WF` (see `LeanDb.Typed.Laws`). -/
def DbState.loadWF {s : Type} [i : IsSchema s] : Db (DbState s) := do
  let st ← DbState.load
  unless st.checkWF do
    throw (.invariant "schema" "checkWF")
  return st

/-- Total number of rows across every schema table. Bounds `deleteCascading`. -/
def DbState.rowCount {s : Type} [i : IsSchema s] (st : DbState s) : Nat :=
  i.tables.foldl (init := 0) fun acc t =>
    let p := i.pack t
    acc + (@Table.rows p.ty p.entity (st.tables t)).length

/-- Gather in-memory rows for a table list of schema `s`. Each position
    is `get`, so `Query.denote` does not need a polymorphic `Source`. -/
class GatherState (s : Type) (ts : List Type) [IsSchema s] where
  gather : DbState s → Array (Rows ts)

instance {s α : Type} [IsSchema s] [Entity α] [IsSchema.Has s α] :
    GatherState s [α] where
  gather st := ((DbState.get (α := α) st).rows.map Valid.toStored).toArray

instance {s α β : Type} {ts : List Type} [IsSchema s] [Entity α] [IsSchema.Has s α]
    [GatherState s (β :: ts)] : GatherState s (α :: β :: ts) where
  gather st :=
    let heads := ((DbState.get (α := α) st).rows.map Valid.toStored).toArray
    let tails := GatherState.gather (s := s) (ts := β :: ts) st
    heads.flatMap fun h => tails.map fun t => (h, t)

/-- Rows of `α`, via `get`, as `Stored` (for `Pred`). -/
def DbState.rows {s α : Type} [IsSchema s] [Entity α] [IsSchema.Has s α]
    (st : DbState s) : Array (Stored α) :=
  ((st.get (α := α)).rows.map Valid.toStored).toArray

/-- Encoded child-table rows of one parent table, from the lists already
    attached on each parent. One snapshot slot per child table, so
    `any`/`all` over a list see the same rows SQL's `EXISTS` does. -/
def Table.childSnapshot {α : Type} [Entity α] (t : Table α) (snap : Pred.Snapshot) :
    Pred.Snapshot :=
  (Entity.children (α := α)).foldl (init := snap) fun snap link =>
    let raw : Array (Int64 × Array Col) := Id.run do
      let mut out : Array (Int64 × Array Col) := #[]
      let mut n : Nat := 1
      for r in t.rows do
        let recs := link.rows r.val
        for hi : i in [0:recs.size] do
          let cols := recs[i]
          out := out.push
            (Int64.ofNat n, #[.int r.id.toInt64, .int (Int64.ofNat i)] ++ cols)
          n := n + 1
      return out
    Pred.Snapshot.addRaw snap link.table raw

/-- A `Pred.Snapshot` of every schema table and every attached child list,
    for quantifier denotation. -/
def DbState.snapshot {s : Type} [i : IsSchema s] (st : DbState s) : Pred.Snapshot :=
  i.tables.foldl (init := Pred.Snapshot.empty) fun snap t =>
    let p := i.pack t
    let tbl := st.tables t
    let snap := @Pred.Snapshot.add snap p.ty p.entity
      ((@Table.rows p.ty p.entity tbl).map (@Valid.toStored p.ty p.entity)).toArray
    @Table.childSnapshot p.ty p.entity tbl snap

end LeanDb
