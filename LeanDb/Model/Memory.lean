import LeanDb.Model.Request

/-! # The in-memory backend

A reference interpreter of the storage requests (`Interpreter Engine portableStorage …`): rows
are stored as the JSON of each entity's row representation and decoded (with every check)
on each read. It follows the same storage semantics as SQLite (`LeanDb.Native`):

* identities count up per entity from 1 and are never reused;
* `select` and `linkField` answer in identity order; `linkField` names each target once;
* a clash with one of the request's declared constraints is a conflict value and writes
  nothing; `update` checks only constraints over fields whose stored value changes;
* a reference field naming no row is a `missingReference` fault, and deleting a row that is
  still referenced is a `restricted` fault (cascades are the generated `T.delete`'s, which
  deletes the referencing rows first);
* a stored value the codec refuses is a `decode` fault, never a value.

Faults abort the run: `run` returns no store, as a native transaction rolls back. It is a
test and reference backend, not a proof of SQLite's behavior. -/

namespace LeanDb.Model.Memory
open Ontology

structure Key where
  entity : TypeId
  scope : String
  id : String
  deriving BEq, DecidableEq, Repr

structure Store where
  rows : List (Key × Lean.Json) := []
  next : List (TypeId × Nat) := []
  /-- Reference fields of each entity written so far: field name and target entity. -/
  references : List (TypeId × List (String × TypeId)) := []
  /-- Join projections answered (`linkField`), for tests. -/
  projectionReads : Nat := 0

inductive Fault where
  | decode (errors : ValidationErrors)
  /-- The row a write names is no longer there. -/
  | gone
  /-- A reference field names no row. -/
  | missingReference (entity field : String)
  /-- A delete is restricted: a row of `entity` still references it through `field`. -/
  | restricted (entity field : String)
  /-- A stored edge names a target row that is not there. -/
  | danglingLink
  /-- A declared constraint with no fields. -/
  | unsupportedConstraint (identity : String)
  deriving Repr

/-- The machine code, shared with LeanDB's native `StorageFault.code` where they agree. -/
def Fault.code : Fault → String
  | .decode _ => "storage.decode"
  | .gone => "storage.gone"
  | .missingReference .. => "storage.missing_reference"
  | .restricted .. => "storage.restricted"
  | .danglingLink => "storage.dangling_link"
  | .unsupportedConstraint _ => "storage.unsupported_constraint"

abbrev Engine := StateT Store (Except Fault)

private def key [HasTypeId T] (ref : Ref T) : Key := ⟨HasTypeId.typeId (α := T), ref.scope.value, ref.key⟩

private def liftChecked (result : Validation A) : Engine A :=
  match result with | .ok value => pure value | .error errors => throw (.decode errors)

/-- The reference fields of `T`, from its derived field metadata. -/
private def referencesOf [Entity T] : List (String × TypeId) :=
  (Domain.fields (T := T)).filterMap fun field => match field.kind with
    | .reference target => some (field.name, target)
    | _ => none

/-- The row a stored reference names: a bare integer key, or the structured form. -/
private def referencedKey (json : Lean.Json) (field : String) (target : TypeId) : Option Key :=
  match json.getObjVal? field with
  | .error _ => none
  | .ok value =>
    match jsonPositiveInteger? value with
    | some id => some ⟨target, "default", id⟩
    | none => match value.getObjValAs? String "scope", value.getObjValAs? String "key" with
      | .ok scope, .ok id => some ⟨target, scope, id⟩
      | _, _ => none

private def entityName [Entity T] : String := (HasTypeId.typeId (α := T)).name

def lookup [Entity T] (ref : Ref T) : Engine (Option (Row Scope T)) := do
  match (← get).rows.find? (fun item => item.1 == key ref) with
  | none => pure none
  | some (_, json) =>
    let value ← liftChecked ((Entity.recordRepresentation (T := T)).decode json)
    pure (some (Trusted.row ref value))

private def conflict (json : Lean.Json) (identity : TypeId) (excluding : Option Key)
    (constraints : List (Constraint E)) : Engine (Option E) := do
  let rows := (← get).rows
  for constraint in constraints do
    if constraint.fields.isEmpty then throw (Fault.unsupportedConstraint constraint.identity)
    let matchesRow := fun (row : Key × Lean.Json) => row.1.entity == identity && excluding != some row.1 &&
      constraint.fields.all (fun field => match json.getObjVal? field, row.2.getObjVal? field with
        | .ok a, .ok b => a == b | _, _ => false)
    if rows.any matchesRow then return some constraint.publicFailure
  return none

/-- Every reference field of the new value names a stored row; records `T`'s references. -/
private def checkReferences [Entity T] (json : Lean.Json) : Engine Unit := do
  let identity := HasTypeId.typeId (α := T)
  let references := referencesOf (T := T)
  let store ← get
  for (field, target) in references do
    match referencedKey json field target with
    | some target => unless store.rows.any (·.1 == target) do throw (.missingReference (entityName (T := T)) field)
    | none => throw (.missingReference (entityName (T := T)) field)
  unless store.references.any (·.1 == identity) do
    set { store with references := store.references ++ [(identity, references)] }

private def putRow [Entity T] (ref : Ref T) (value : T) : Engine Unit :=
  modify fun store => { store with rows := store.rows.filter (fun row => row.1 != key ref) ++
    [(key ref, (Entity.recordRepresentation (T := T)).encode value)] }

private def insertRow [Entity T] (value : T) : Engine (Ref T) := do
  let identity := HasTypeId.typeId (α := T)
  let store ← get
  let next := (store.next.find? (fun entry => entry.1 == identity)).map Prod.snd |>.getD 1
  let ref ← liftChecked (Ref.parse (T := T) (toString next))
  putRow ref value
  modify fun store => { store with next := store.next.filter (fun entry => entry.1 != identity) ++ [(identity, next + 1)] }
  return ref

/-- Every stored row of one entity, decoded through its row representation, by numeric id. -/
def entityRows [Entity T] : Engine (List (Row Scope T)) := do
  let identity := HasTypeId.typeId (α := T)
  let stored := (← get).rows.filter (fun row => row.1.entity == identity)
    |>.mergeSort (fun a b => a.1.id.toNat?.getD 0 ≤ b.1.id.toNat?.getD 0)
  let mut rows := []
  for (rowKey, json) in stored do
    let ref ← liftChecked (Ref.parse (T := T) rowKey.id rowKey.scope)
    let value ← liftChecked ((Entity.recordRepresentation (T := T)).decode json)
    rows := rows ++ [Trusted.row ref value]
  return rows

/-- A row still referenced by another row cannot be deleted. -/
private def checkUnreferenced (target : Key) : Engine Unit := do
  let store ← get
  for (source, references) in store.references do
    for (field, entity) in references do
      unless entity == target.entity do continue
      if store.rows.any (fun row => row.1.entity == source && referencedKey row.2 field entity == some target) then
        throw (.restricted source.name field)

/-- One storage request, at any access. -/
def request {resources : StorageResources} {Scope : Type} {access : Access} :
    {A : Type} → StorageRequest resources Scope access A → Engine A
  | _, @StorageRequest.find _ _ _ T inst _storage ref => do
    let _ : Entity T := inst
    lookup (Scope := Scope) ref
  | _, @StorageRequest.findBy _ _ _ T _ inst _storage unique _lookup probe => do
    let _ : Entity T := inst
    let rows ← entityRows (Scope := Scope) (T := T)
    return rows.find? fun row => unique.equal (unique.key row.value) probe
  | _, @StorageRequest.select _ _ _ T inst _storage => do
    let _ : Entity T := inst
    entityRows (Scope := Scope) (T := T)
  | _, @StorageRequest.linkField _ _ _ E _P T V instE instT _edges link _proof _targets field _column parent => do
    let _ : Entity E := instE
    let _ : Entity T := instT
    let edges ← entityRows (Scope := Scope) (T := E)
    let targets := (edges.filter fun edge => link.parent edge.value == parent).map (link.target ·.value)
    -- Each target once, by numeric id (the native plan's ORDER BY target id).
    let distinct := targets.foldl (fun acc ref => if acc.any (· == ref) then acc else acc ++ [ref]) []
    let ordered := distinct.mergeSort fun a b => a.key.toNat?.getD 0 ≤ b.key.toNat?.getD 0
    modify fun store => { store with projectionReads := store.projectionReads + 1 }
    let mut values : List V := []
    for ref in ordered do
      let .some row ← lookup (Scope := Scope) ref | throw Fault.danglingLink
      values := values ++ [field.get row.value]
    return values
  | _, @StorageRequest.insert _ _ T _ inst _storage value conflicts => do
    let _ : Entity T := inst
    let identity := HasTypeId.typeId (α := T)
    let json := (Entity.recordRepresentation (T := T)).encode value
    match ← conflict json identity none conflicts with
    | some failure => return .error failure
    | none =>
      checkReferences (T := T) json
      return .ok (← insertRow value)
  | _, @StorageRequest.update _ _ T _ inst _storage row patch conflicts => do
    let _ : Entity T := inst
    let .some current ← lookup (Scope := Scope) row.id | throw Fault.gone
    let updated := patch.apply current.value
    let codec := Entity.recordRepresentation (T := T)
    let before := codec.encode current.value
    let json := codec.encode updated
    -- Only fields the change names and whose stored value differs are written or checked.
    let changed := patch.fields.filter fun field =>
      match before.getObjVal? field, json.getObjVal? field with
      | .ok a, .ok b => a != b
      | _, _ => true
    if changed.isEmpty then return .ok ()
    let touched := conflicts.filter fun c => c.fields.any changed.contains
    match ← conflict json (HasTypeId.typeId (α := T)) (some (key row.id)) touched with
    | some failure => return .error failure
    | none =>
      checkReferences (T := T) json
      putRow row.id updated
      return .ok ()
  | _, @StorageRequest.delete _ _ T inst _storage row => do
    let _ : Entity T := inst
    let identity := key row.id
    unless (← get).rows.any (·.1 == identity) do throw Fault.gone
    checkUnreferenced identity
    modify fun store => { store with rows := store.rows.filter (fun row => row.1 != identity) }

/-- The in-memory backend as an interpreter, for any family (its evidence is not used). -/
def interpreter {resources : StorageResources} {access : Access} {Scope : Type} :
    Interpreter Engine resources access Scope := ⟨request⟩

/-- Run a program. A fault discards every write. -/
def run {resources : StorageResources} {access : Access} {Scope A : Type}
    (program : Program resources access Scope A) (store : Store := {}) : Except Fault (A × Store) :=
  (program.run interpreter).run store

end LeanDb.Model.Memory
