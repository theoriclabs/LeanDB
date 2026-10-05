import LeanDbDomain.Witness
import LeanApp.Domain.Resources

namespace LeanDb.Domain

/-- Instantiate the ONE portable resource vocabulary with actual native
    schema witnesses. The field name selects HasMemberStorage at assembly;
    the witness itself retains the real typed relation and Edge. -/
@[reducible] def storageResources (s : Type) [IsSchema s] : LeanApp.Domain.ResourceFamily where
  entity := fun type => EntityStorage s type
  member := fun parent _field target => MemberStorage s parent target
  projection := fun relation path => ProjectionStorage relation path
  -- DB does not supply an authentication engine. No witness of this slot exists;
  -- API replaces it with its dependent native Auth.Storage, on the same entity.
  auth := fun _ => ULift Empty
  -- A declared unique constraint's typed native index, anchored to the exact
  -- entity dictionary the request carries (`RequestF.findBy`).
  unique := fun storage key => UniqueStorage storage key
  -- The portable join (`Query.linkField`): link and target-column evidence.
  link := fun edges key => LinkEvidence edges key
  column := fun storage path => ColumnEvidence storage path

instance {s T} [IsSchema s] [HasEntityStorage s T] :
    LeanApp.Domain.HasEntityResource (storageResources s) T where
  witness := HasEntityStorage.storage (s := s) (T := T)

/-- Every constraint `native_schema%` derived from `constraint T.c : unique …`
    (single-field or composite) has typed lookup evidence on the native storage. -/
instance {s T K} [IsSchema s] [HasEntityStorage s T] (storage : (storageResources s).entity T)
    (key : LeanApp.Domain.UniqueKey T K) [evidence : HasUniqueStorage s T K key]
    [same : SameStorage (HasEntityStorage.storage (s := s) (T := T)) storage] :
    LeanApp.Domain.HasUniqueResource (storageResources s) T K storage key where
  witness := same.same ▸ evidence.lookup

instance {s E P T} [IsSchema s] [HasEntityStorage s E] (storage : (storageResources s).entity E)
    (key : LeanApp.Domain.LinkKey E P T) [evidence : HasLinkEvidence s E P T key]
    [same : SameStorage (HasEntityStorage.storage (s := s) (T := E)) storage] :
    LeanApp.Domain.HasLinkResource (storageResources s) E P T storage key where
  witness := same.same ▸ evidence.evidence

instance {s T V} [IsSchema s] [HasEntityStorage s T] (storage : (storageResources s).entity T)
    (path : Ontology.FieldPath T V) [evidence : HasColumnEvidence s T V path]
    [same : SameStorage (HasEntityStorage.storage (s := s) (T := T)) storage] :
    LeanApp.Domain.HasColumnResource (storageResources s) T V storage path where
  witness := same.same ▸ evidence.evidence

instance {s P T field} [IsSchema s] [HasMemberStorage s P field T] :
    LeanApp.Domain.HasMemberResource (storageResources s) P field T where
  witness := HasMemberStorage.storage (s := s) (Parent := P) (field := field) (Target := T)

/-- Resolve the native column and portable lens together, retaining the exact
    generated EditableField dictionary in the dependent portable result. -/
instance {s P T member field V} [IsSchema s]
    (storage : (storageResources s).member P member T)
    [selection : HasFieldProjection s T field V storage.target] :
    @LeanApp.Domain.HasProjectionResource (storageResources s) P T member storage field V
      (@HasFieldProjection.editable s T field V inferInstance storage.target selection) := by
  letI := @HasFieldProjection.editable s T field V inferInstance storage.target selection
  exact ⟨{ column := selection.column, source_agrees := selection.source_agrees }⟩

end LeanDb.Domain
