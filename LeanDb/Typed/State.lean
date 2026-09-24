import LeanDb.Typed.Schema
import LeanDb.Db
import LeanDb.Transaction

namespace LeanDb

/-! # Pure database state (M14)

`Table` is one entity's AUTOINCREMENT counter and its rows in id order,
child lists attached. `DbState s` is one table per entity of schema `s`.
Production state is abstracted by reading every table in id order
(`fetchAll`).

`DbState` lives in `Type` (so it can be a `DbM` result). Tables of
different entities are stored by name and recovered with a typed `get`.
-/

/-- The production monad. `DbState.load : Db (DbState s)`. -/
abbrev Db := DbM

/-- A table's contents: the AUTOINCREMENT counter, and rows by id. -/
structure Table (α : Type) [Entity α] where
  next : Nat := 1
  rows : List (Stored α) := []
  deriving Repr

/-- Untyped payload of one table, so `DbState` can sit in `Type`. -/
structure DbState.Slot : Type where
  name : String
  next : Nat
  /-- `Array (Stored α)` for the entity named `name`. -/
  rows : Array (Stored Unit)

/-- The whole database, one slot per entity of the schema. -/
structure DbState (s : Type) [IsSchema s] : Type where
  slots : Array DbState.Slot

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

unsafe def DbState.castRows {α β : Type} (rows : Array (Stored α)) : Array (Stored β) :=
  unsafeCast rows

/-- No rows, every AUTOINCREMENT counter at 1. -/
def DbState.empty {s : Type} [i : IsSchema s] : DbState s where
  slots := i.tables.map fun t =>
    let p := i.pack t
    { name := @Entity.tableName p.ty p.entity, next := 1
      rows := (#[] : Array (Stored Unit)) }

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

unsafe def DbState.loadImpl {s : Type} [i : IsSchema s] : Db (DbState s) :=
  readSnapshot do
    let slots ← i.tables.mapM fun t => do
      let p := i.pack t
      let rows ← @fetchAll p.ty p.entity
      let next ← @DbState.loadNext p.ty p.entity rows
      pure {
        name := @Entity.tableName p.ty p.entity
        next
        rows := DbState.castRows (α := p.ty) (β := Unit) rows
      }
    return ⟨slots⟩

/-- Read every table of `s` in id order, under one deferred snapshot. -/
@[implemented_by DbState.loadImpl]
def DbState.load {s : Type} [IsSchema s] : Db (DbState s) :=
  pure ⟨#[]⟩

unsafe def DbState.getImpl {s α : Type} [IsSchema s] [Entity α]
    (st : DbState s) : Table α :=
  match st.slots.find? (fun sl => sl.name == Entity.tableName α) with
  | none => { next := 1, rows := [] }
  | some sl =>
      { next := sl.next, rows := (DbState.castRows (α := Unit) (β := α) sl.rows).toList }

/-- Rows of `α` in this state. -/
@[implemented_by DbState.getImpl]
def DbState.get {s α : Type} [IsSchema s] [Entity α] (st : DbState s) : Table α :=
  { next := 1, rows := [] }

/-- Every foreign key of `α` resolves to a row in the target table. -/
def Table.fksOk {s α : Type} [IsSchema s] [Entity α] [hf : HasForeignKey α]
    (st : DbState s) (t : Table α) : Bool :=
  t.rows.all fun r =>
    (ForeignKey.all α).all fun fk =>
      let tgt := hf.get fk r.val
      let inst := hf.targetEntity fk
      let tbl := @DbState.get s (hf.Target fk) inferInstance inst st
      tbl.rows.any fun row => row.id.toInt64 == tgt.toInt64

/-- One packed entity of the schema: local table check plus foreign keys. -/
def DbState.checkPacked {s : Type} [IsSchema s] (st : DbState s) (p : PackedEntity) : Bool :=
  let tbl := @DbState.get s p.ty inferInstance p.entity st
  @Table.check p.ty p.entity p.unique tbl &&
    @Table.fksOk s p.ty inferInstance p.entity p.foreignKey st tbl

/-- Decidable well-formedness: every schema table is present, every row
    decodes and is `Checked`, ids strictly increase and stay `< next`,
    unique keys are unique, foreign keys resolve, child lists attach. -/
def DbState.checkWF {s : Type} [sch : IsSchema s] (st : DbState s) : Bool :=
  let namesOk := (st.slots.toList.zip sch.tables.toList).all fun (sl, t) =>
    sl.name == @Entity.tableName (sch.pack t).ty (sch.pack t).entity
  st.slots.size == sch.tables.size && namesOk &&
    sch.tables.all fun t => DbState.checkPacked st (sch.pack t)

/-- Every row decodes and is `Checked`, and every constraint holds. -/
def DbState.WF {s : Type} [IsSchema s] (st : DbState s) : Prop :=
  DbState.checkWF st = true

unsafe def DbState.setImpl {s α : Type} [IsSchema s] [Entity α]
    (st : DbState s) (tbl : Table α) : DbState s :=
  let name := Entity.tableName α
  let slot : DbState.Slot := {
    name
    next := tbl.next
    rows := DbState.castRows (α := α) (β := Unit) tbl.rows.toArray
  }
  if st.slots.any (·.name == name) then
    ⟨st.slots.map fun sl => if sl.name == name then slot else sl⟩
  else
    ⟨st.slots.push slot⟩

/-- Replace the table for `α`. Adds a slot if the name was missing. -/
@[implemented_by DbState.setImpl]
def DbState.set {s α : Type} [IsSchema s] [Entity α]
    (st : DbState s) (tbl : Table α) : DbState s :=
  st

unsafe def DbState.sourceImpl {s : Type} [IsSchema s] (st : DbState s) : Source (_root_.Id) where
  load _ α _ := (DbState.get (α := α) st).rows.toArray

/-- In-memory `Source` for `selectSpec`. -/
@[implemented_by DbState.sourceImpl]
def DbState.source {s : Type} [IsSchema s] (st : DbState s) : Source (_root_.Id) :=
  ⟨fun _ α _ => (DbState.get (α := α) st).rows.toArray⟩

/-- A `Pred.Snapshot` of every table, for quantifier denotation. -/
def DbState.snapshot {s : Type} [i : IsSchema s] (st : DbState s) : Pred.Snapshot :=
  i.tables.foldl (init := Pred.Snapshot.empty) fun snap t =>
    let p := i.pack t
    have : Entity p.ty := p.entity
    let tbl := DbState.get (α := p.ty) st
    Pred.Snapshot.add (β := p.ty) snap tbl.rows.toArray

end LeanDb
