import LeanDb.Native.Witness
import LeanDb.Model.Request
import LeanDb.Typed.Link
import LeanDb.Typed.Constraint

/-! # Native hooks for the storage requests

The model's `T.insert`, `T.update`/`T.patch`, `T.delete`, `T.find`, `T.findBy`, `T.select`
and `Query.linkField` build `StorageRequest.insert/update/delete/find/findBy/select/linkField`.
The native interpreter (`LeanDb.Native.Interpreter`) lowers each request to one hook below,
on the exact `EntityStorage` the request carries.

- Declared unique conflicts are VALUES of the entity's own conflict type `C`:
  the native alternative is mapped to the request's `Constraint C` whose
  `identity` equals `storage.sourceUnique index` (the exact identity mapping).
- Everything else is a framework failure, a `StorageFault`. In a `Txn` the
  caller's `fault` aborts and rolls back the whole operation. Reads return it.
- Ids leave as model `Ref`s, and rows as `Row Scope T` through the trusted
  row constructor, after the live lookup in the same snapshot or transaction.
-/

namespace LeanDb.Native
open LeanDb

/-- Framework failures of the storage requests. None is a domain conflict. -/
inductive StorageFault where
  /-- A model `Ref` that names no native row id (or another scope). -/
  | invalidReference (why : String)
  /-- A stored id with no model `Ref` (corruption). -/
  | invalidIdentity (why : String)
  /-- The value fails the entity's range/invariant check. -/
  | invalidRow (checks : List String)
  /-- A reference field names no row (`ON DELETE`/FK identity). -/
  | missingReference (constraint : ConstraintMetadata)
  /-- A delete is restricted by an inbound reference. -/
  | restricted (constraint : ConstraintMetadata)
  /-- A native unique the request did not declare (no `Constraint` with its identity). -/
  | unmappedConflict (constraint : ConstraintMetadata)
  /-- The row the step names is no longer there. -/
  | gone
  deriving Repr, BEq

/-- A stable machine code per alternative, for framework replies and logs. -/
def StorageFault.code : StorageFault → String
  | .invalidReference _ => "identity.invalid_reference"
  | .invalidIdentity _ => "storage.invalid_identity"
  | .invalidRow _ => "storage.invalid_row"
  | .missingReference _ => "storage.missing_reference"
  | .restricted _ => "storage.restricted"
  | .unmappedConflict _ => "storage.unmapped_constraint"
  | .gone => "storage.gone"

/-- `StorageRequest.find`: the row with this identity, read in the enclosing snapshot or
    transaction. Reference validation is pure; an invalid or cross-scope reference is an
    error, never a different row. -/
def EntityStorage.find {s T Scope} [IsSchema s] [LeanDb.Model.Entity T]
    (storage : EntityStorage s T) (reference : Ontology.Ref T) :
    Except String (Read s (Option (LeanDb.Model.Row Scope T))) :=
  letI := storage.entity
  letI := storage.schema
  match refToId reference with
  | .error error => .error error
  | .ok id => .ok do
    let row ← Read.get T id
    return row.map (fun value => LeanDb.Model.Trusted.row reference value.val)

/-- The model row of a stored native row. -/
def EntityStorage.rowOf {s T Scope} [IsSchema s] [LeanDb.Model.Entity T]
    (storage : EntityStorage s T) (row : @Valid T storage.entity) :
    Except StorageFault (LeanDb.Model.Row Scope T) :=
  match idToRef (@Valid.id T storage.entity row) with
  | .ok reference => .ok (LeanDb.Model.Trusted.row reference (@Valid.val T storage.entity row))
  | .error why => .error (.invalidIdentity why)

/-- `StorageRequest.select`: every row, in id order. -/
def EntityStorage.select {s T Scope} [IsSchema s] [LeanDb.Model.Entity T]
    (storage : EntityStorage s T) :
    Read s (Except StorageFault (List (LeanDb.Model.Row Scope T))) :=
  letI := storage.entity
  letI := storage.schema
  do
    let rows ← Read.all (Query.from T)
    return rows.mapM (storage.rowOf (Scope := Scope))

/-- `StorageRequest.findBy`: one probe of the declared constraint's native unique index
    (single-field or composite), keyed by `lookup.encode value`. `key_agrees` makes
    that the native key of exactly the rows whose declared key is `value`. -/
def EntityStorage.findBy {s T K Scope} [IsSchema s] [LeanDb.Model.Entity T]
    (storage : EntityStorage s T) {key : LeanDb.Model.UniqueKey T K}
    (lookup : UniqueStorage storage key) (value : K) :
    Read s (Except StorageFault (Option (LeanDb.Model.Row Scope T))) :=
  letI := storage.entity
  letI := storage.unique
  letI := storage.schema
  do
    match ← Read.findBy T lookup.index (lookup.encode value) with
    | none => return .ok none
    | some row => return (storage.rowOf (Scope := Scope) row).map some

/-- The request's declared conflict for a native alternative, by exact identity. -/
def EntityStorage.conflictOf {s T C ε σ} [IsSchema s] (storage : EntityStorage s T)
    (conflicts : List (LeanDb.Model.Constraint C)) (fault : StorageFault → ε)
    (index : @LeanDb.Unique T storage.entity storage.unique) : Txn σ s ε C :=
  match conflicts.find? (fun constraint => constraint.identity == storage.sourceUnique index) with
  | some constraint => Txn.pure constraint.publicFailure
  | none =>
      Txn.throw (fault (.unmappedConflict
        (@Unique.metadata T storage.entity storage.unique storage.indexes index)))

/-- `StorageRequest.insert`, through `Txn.insertUnique`. A declared unique conflict is
    returned as `.error c` and writes nothing; a missing reference aborts. -/
def EntityStorage.insert {s T C ε σ} [IsSchema s] [LeanDb.Model.Entity T]
    (storage : EntityStorage s T) (value : T) (conflicts : List (LeanDb.Model.Constraint C))
    (fault : StorageFault → ε) : Txn σ s ε (Except C (Ontology.Ref T)) :=
  letI := storage.entity
  letI := storage.indexes
  letI := storage.unique
  letI := storage.foreignKey
  letI := storage.schema
  do
    let checked ← (LeanDb.Entity.check T value).orAbort (fun why => fault (.invalidRow why.names))
    match ← Txn.insertUnique checked (fun key => fault (.missingReference (ForeignKey.metadata key))) with
    | .ok row =>
        let reference ← (idToRef row.id).orAbort (fun why => fault (.invalidIdentity why))
        return .ok reference
    | .error index => return .error (← storage.conflictOf conflicts fault index)

/-- The stored columns whose value `patch` changes on `live`, among the fields it
    names. Only constraints over these can newly conflict. -/
def EntityStorage.changedFields {s T} [IsSchema s] (storage : EntityStorage s T)
    (names : List String) (old new : T) : @Fields T storage.entity :=
  letI := storage.entity
  ⟨fun field => names.contains (Entity.fieldName field) &&
    @toCol _ (Entity.codec field) (Entity.get field old) != @toCol _ (Entity.codec field) (Entity.get field new)⟩

/-- `StorageRequest.update`: re-read the row in the admitted writer, apply the change,
    and write only the columns whose value changed (`Txn.patch`). Only constraints
    that touch a changed column are checked; a clash is `.error c` and writes
    nothing. An unchanged row writes nothing. -/
def EntityStorage.update {s T C ε σ Scope} [IsSchema s] [LeanDb.Model.Entity T]
    (storage : EntityStorage s T) (row : LeanDb.Model.Row Scope T) (patch : LeanDb.Model.Change T)
    (conflicts : List (LeanDb.Model.Constraint C)) (fault : StorageFault → ε) :
    Txn σ s ε (Except C Unit) :=
  letI := storage.entity
  letI := storage.indexes
  letI := storage.unique
  letI := storage.foreignKey
  letI := storage.schema
  do
    let id ← (refToId row.id).orAbort (fun why => fault (.invalidReference why))
    let some live ← Txn.get T id | Txn.throw (fault .gone)
    let next := patch.apply live.val
    let changed := storage.changedFields patch.fields live.val next
    unless (Entity.fields (α := T)).any changed.mem do return .ok ()
    let checked ← (LeanDb.Entity.check T next).orAbort (fun why => fault (.invalidRow why.names))
    match ← Txn.patch T live changed checked with
    | .ok _ => return .ok ()
    | .error .gone => Txn.throw (fault .gone)
    | .error (.invalid why) => Txn.throw (fault (.invalidRow why.names))
    | .error (.missingRef key) => Txn.throw (fault (.missingReference (ForeignKey.metadata key.fk)))
    | .error (.duplicate index _) => return .error (← storage.conflictOf conflicts fault index.ix)

/-- `StorageRequest.delete`: inbound references declared to cascade (model
    `constraint Loan.removeWithBook : cascade book`, or native `cascade%`)
    are deleted with the row; a restricting one (e.g. `Loan.member`) aborts. -/
def EntityStorage.delete {s T ε σ Scope} [IsSchema s] [LeanDb.Model.Entity T]
    (storage : EntityStorage s T) (row : LeanDb.Model.Row Scope T) (fault : StorageFault → ε) :
    Txn σ s ε Unit :=
  letI := storage.entity
  letI := storage.schema
  letI := storage.referencedBy
  do
    let id ← (refToId row.id).orAbort (fun why => fault (.invalidReference why))
    match ← Txn.delete T id with
    | .ok _ => pure ()
    | .error .gone => Txn.throw (fault .gone)
    | .error (.restricted key _) => Txn.throw (fault (.restricted (ReferencedBy.metadata key.val)))

end LeanDb.Native

/-! ## The typed join (e.g. `Loan ⋈ Member`: one column, by target id) -/

namespace LeanDb.Native
open LeanDb

/-- Lower the join to `Read.linkField`: the targets some edge links to
    `parent`, each once, in target-id order, selecting `column` alone (no other
    target column is read or decoded). -/
def LinkStorage.project {s P T E V} [IsSchema s] [LeanDb.Model.Entity P]
    (link : LinkStorage s P T E) (column : @FieldStorage T V link.target.entity)
    (parent : Ontology.Ref P) : Except String (Read s (List V)) :=
  letI := link.parent.entity
  letI := link.target.entity
  letI := link.edge.entity
  letI := link.edge.schema
  letI := link.target.schema
  match refToId parent with
  | .error why => .error why
  | .ok id => .ok do
      let values ← Read.linkField link.relation id column.field
      return column.valueType ▸ values

/-- Lower an authored `if h : allowed then visible <$> Book.borrowers … h else hidden`
    to `Read.discloseIf`: when `allowed` is false the read IS `pure hidden`, so no
    statement is prepared (`LinkStorage.projectIf_denied`). -/
def LinkStorage.projectIf {s P T E V β} [IsSchema s] [LeanDb.Model.Entity P]
    (link : LinkStorage s P T E) (column : @FieldStorage T V link.target.entity)
    (parent : Ontology.Ref P) (allowed : Prop) [Decidable allowed]
    (visible : List V → β) (hidden : β) : Except String (Read s β) :=
  match link.project column parent with
  | .error why => .error why
  | .ok read => .ok (Read.discloseIf allowed (fun _ => read) visible hidden)

theorem LinkStorage.projectIf_denied {s P T E V β} [IsSchema s] [LeanDb.Model.Entity P]
    (link : LinkStorage s P T E) (column : @FieldStorage T V link.target.entity)
    (parent : Ontology.Ref P) (allowed : Prop) [Decidable allowed]
    (visible : List V → β) (hidden : β) (denied : ¬ allowed) (read : Read s β)
    (lowered : link.projectIf column parent allowed visible hidden = .ok read) :
    read = .pure hidden := by
  unfold LinkStorage.projectIf at lowered
  split at lowered
  · exact absurd lowered (by simp)
  · simp only [Except.ok.injEq] at lowered
    rw [← lowered, Read.discloseIf_denied _ _ _ _ denied]

end LeanDb.Native

namespace LeanDb.Native
open LeanDb

/-- `StorageRequest.linkField` (`Query.linkField`, e.g. a book's borrowers):
    lowered to `Read.linkField` on the request's own target storage, selecting
    the one column the evidence names: each target once, in target-id order. -/
def LinkEvidence.project {s E P T V : Type} [IsSchema s] {edges : EntityStorage s E}
    {key : LeanDb.Model.LinkKey E P T} (evidence : LinkEvidence edges key)
    (targets : EntityStorage s T) {path : Ontology.FieldPath T V} (column : ColumnEvidence targets path)
    (parent : Ontology.Ref P) : Except String (Read s (List V)) :=
  letI := evidence.parentIdentity
  letI := evidence.link.parent.entity
  letI := targets.entity
  letI := evidence.link.edge.entity
  letI := evidence.link.edge.schema
  letI := targets.schema
  -- The relation names edge columns only, so it reads the request's own target
  -- storage: the column symbol and the target table come from `targets`.
  let relation := evidence.link.relation
  match refToId parent with
  | .error why => .error why
  | .ok id => .ok do
      let values ← Read.linkField relation id column.column.field
      return column.column.valueType ▸ values

end LeanDb.Native
