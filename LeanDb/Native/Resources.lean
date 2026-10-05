import LeanDb.Native.Witness
import LeanDb.Model.Resources

/-! # The native storage family

`storageResources s` instantiates the model's `StorageResources` with the schema's own
dictionaries, so a generalized model program (`f.withResources`) demands exactly the
evidence `native_schema%` generated for schema `s`. -/

namespace LeanDb.Native

/-- The model's storage family, with the actual native witnesses of schema `s`. -/
@[reducible] def storageResources (s : Type) [IsSchema s] : LeanDb.Model.StorageResources where
  entity := fun type => EntityStorage s type
  -- A declared unique constraint's typed native index, anchored to the exact entity
  -- dictionary the request carries (`StorageRequest.findBy`).
  unique := fun storage key => UniqueStorage storage key
  -- The join (`Query.linkField`): link and target-column evidence.
  link := fun edges key => LinkEvidence edges key
  column := fun storage path => ColumnEvidence storage path

instance {s T} [IsSchema s] [HasEntityStorage s T] :
    LeanDb.Model.HasEntityResource (storageResources s) T where
  witness := HasEntityStorage.storage (s := s) (T := T)

/-- Every constraint `native_schema%` derived from `constraint T.c : unique …` (single-field
or composite) has typed lookup evidence on the native storage. -/
instance {s T K} [IsSchema s] [HasEntityStorage s T] (storage : (storageResources s).entity T)
    (key : LeanDb.Model.UniqueKey T K) [evidence : HasUniqueStorage s T K key]
    [same : SameStorage (HasEntityStorage.storage (s := s) (T := T)) storage] :
    LeanDb.Model.HasUniqueResource (storageResources s) T K storage key where
  witness := same.same ▸ evidence.lookup

instance {s E P T} [IsSchema s] [HasEntityStorage s E] (storage : (storageResources s).entity E)
    (key : LeanDb.Model.LinkKey E P T) [evidence : HasLinkEvidence s E P T key]
    [same : SameStorage (HasEntityStorage.storage (s := s) (T := E)) storage] :
    LeanDb.Model.HasLinkResource (storageResources s) E P T storage key where
  witness := same.same ▸ evidence.evidence

instance {s T V} [IsSchema s] [HasEntityStorage s T] (storage : (storageResources s).entity T)
    (path : Ontology.FieldPath T V) [evidence : HasColumnEvidence s T V path]
    [same : SameStorage (HasEntityStorage.storage (s := s) (T := T)) storage] :
    LeanDb.Model.HasColumnResource (storageResources s) T V storage path where
  witness := same.same ▸ evidence.evidence

end LeanDb.Native
