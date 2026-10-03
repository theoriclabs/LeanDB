import LeanDbDomain.Witness
import LeanApp.Domain.Flow

namespace LeanDb.Domain

/-- Privileged native assembly hook. Reference validation is pure; the actual
    row lookup/reconstruction remains in the enclosing snapshot or transaction.
    This uses the ORIGINAL T, not a DTO or a recovered runtime TypeId. -/
def EntityStorage.find {s T Scope} [IsSchema s] [LeanApp.Domain.Entity T]
    (storage : EntityStorage s T) (reference : LeanApp.Domain.Ref T) :
    Except String (Read s (Option (LeanApp.Domain.Row Scope T))) :=
  letI := storage.entity
  letI := storage.schema
  match refToId reference with
  | .error error => .error error
  | .ok id => .ok do
    let row ← Read.get T id
    return row.map (fun value => LeanApp.Domain.Trusted.row reference value.val)

/-- Privileged membership-policy hook. Both nominal dictionaries come from the
    actual generated relation; invalid/cross-storage-scope references reject.
    The read lowers to indexed EXISTS without hydrating parent/target rows. -/
def MemberStorage.contains {s Parent Target} [IsSchema s]
    (storage : MemberStorage s Parent Target) (parent : LeanApp.Domain.Ref Parent)
    (member : LeanApp.Domain.Ref Target) : Except String (Read s Bool) :=
  letI := storage.parentIdentity
  letI := storage.targetIdentity
  letI := storage.parent.entity
  letI := storage.target.entity
  letI := storage.edge.entity
  letI := storage.edge.unique
  letI := storage.edge.foreignKey
  letI := storage.edge.schema
  let ids : Except String (Id Parent × Id Target) := do
    return (← refToId parent, ← refToId member)
  match ids with
  | .error error => .error error
  | .ok (parentId, targetId) => .ok (Read.memberContains storage.relation parentId targetId)

/-- Privileged projection hook with coherent column evidence. Protected Flow
    lowering must invoke it through the policy-first interpreter branch. SQL
    selects only the proven target column, in deterministic target-ID order. -/
def MemberStorage.project {s Parent Target Value} [IsSchema s]
    (storage : MemberStorage s Parent Target)
    (column : @FieldStorage Target Value storage.target.entity)
    (parent : LeanApp.Domain.Ref Parent) : Except String (Read s (List Value)) :=
  letI := storage.parentIdentity
  letI := storage.parent.entity
  letI := storage.target.entity
  letI := storage.edge.entity
  letI := storage.edge.unique
  letI := storage.edge.foreignKey
  letI := storage.edge.schema
  letI := storage.target.schema
  match refToId parent with
  | .error error => .error error
  | .ok parentId => .ok (column.project storage.relation parentId)

/-- Lower the shared algebra's carried projection witness without reconstructing
    whole target rows or recovering a column from a runtime field name. -/
def ProjectionStorage.project {s Parent Target Value} [IsSchema s]
    {storage : MemberStorage s Parent Target} {path : Ontology.FieldPath Target Value}
    (selection : ProjectionStorage storage path) (parent : LeanApp.Domain.Ref Parent) :
    Except String (Read s (List Value)) :=
  storage.project selection.column parent

/-- Inclusion always takes the authenticated actor's identity. Re-read the
    parent in the admitted transaction before binding the native handle; a
    missing live parent aborts. Only the generated exact pair duplicate is
    discharged, while real typed FK failures remain for the caller to map. -/
def MemberStorage.includeActor {s Parent Target Scope Error} [IsSchema s]
    (storage : MemberStorage s Parent Target) (parent : LeanApp.Domain.Ref Parent)
    (actor : LeanApp.Domain.SignedIn Scope Target) (missingParent : Error) :
    Except String (Txn Scope s Error
      (Except (@ForeignKey storage.Edge storage.edge.entity storage.edge.foreignKey) Unit)) :=
  letI := storage.parentIdentity
  letI := storage.targetIdentity
  letI := storage.parent.entity
  letI := storage.target.entity
  letI := storage.edge.entity
  letI := storage.edge.unique
  letI := storage.edge.foreignKey
  letI := storage.parent.schema
  letI := storage.edge.schema
  let ids : Except String (Id Parent × Id Target) := do
    return (← refToId parent, ← refToId actor.id)
  match ids with
  | .error error => .error error
  | .ok (parentId, targetId) => .ok do
    let some live ← Txn.get Parent parentId | Txn.throw missingParent
    Txn.includeMember (storage.relation.bind live) targetId

end LeanDb.Domain
