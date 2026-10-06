import LeanDb.Model.Metadata

/-! # Storage resource families

A storage request carries typed evidence for what it touches: the entity's storage, the
index of a declared unique constraint, a declared link, a column. A backend chooses what
that evidence is. The portable family (`portableStorage`) carries none (`PUnit`); LeanDB's
native family carries the schema's own dictionaries (`LeanDb.Native.storageResources`).

Model code is written once against `portableStorage`; `LeanDb.Model.Requirements`
generalizes a definition's body over the family, so the same program runs on any backend
that supplies the evidence it demands.

An operation layer extends the family with its own slots
(`structure Resources extends StorageResources where auth : …`) and embeds the storage
requests unchanged. -/

namespace LeanDb.Model
open Ontology

/-- A backend's typed storage capabilities. Portable declarations never import a backend. -/
structure StorageResources where
  /-- The storage of one entity (LeanDB: `EntityStorage s T`, the schema's dictionaries). -/
  entity : Type → Type 1
  /-- Evidence for one declared unique constraint, anchored to the exact entity storage
  (LeanDB: `UniqueStorage`, the typed index whose key agrees with `UniqueKey.key`). -/
  unique : {T K : Type} → entity T → UniqueKey T K → Type 1 := fun _ _ => PUnit
  /-- Evidence for a join through edge entity `E` (LeanDB: `LinkEvidence`). -/
  link : {E P T : Type} → entity E → LinkKey E P T → Type 1 := fun _ _ => PUnit
  /-- Evidence that one column of `T` holds the field at `path` (LeanDB: `ColumnEvidence`). -/
  column : {T V : Type} → entity T → FieldPath T V → Type 1 := fun _ _ => PUnit

/-- The storage of entity `T` in family `family`. -/
class HasEntityResource (family : StorageResources) (T : Type) where
  witness : family.entity T

/-- Typed lookup evidence for one declared unique constraint on the exact entity storage. -/
class HasUniqueResource (family : StorageResources) (T K : Type) (storage : family.entity T)
    (key : UniqueKey T K) where
  witness : family.unique storage key

/-- Typed join evidence for one declared `LinkKey` on the exact edge storage. -/
class HasLinkResource (family : StorageResources) (E P T : Type) (storage : family.entity E)
    (key : LinkKey E P T) where
  witness : family.link storage key

/-- Typed column evidence for one field path on the exact entity storage. -/
class HasColumnResource (family : StorageResources) (T V : Type) (storage : family.entity T)
    (path : FieldPath T V) where
  witness : family.column storage path

/-- The portable family: no evidence. `DB` and `Query` are written against it. -/
def portableStorage : StorageResources := {
  entity := fun _ => PUnit
  unique := fun _ _ => PUnit
  link := fun _ _ => PUnit
  column := fun _ _ => PUnit
}

/- The portable instances are named: `LeanDb.Model.Requirements` abstracts exactly these
constants (and `portableStorage`, `OpScope`) to obtain a resource-generic body. -/
instance portableEntity : HasEntityResource portableStorage T := ⟨PUnit.unit⟩
instance portableUnique (storage : portableStorage.entity T) (key : UniqueKey T K) :
    HasUniqueResource portableStorage T K storage key := ⟨PUnit.unit⟩
instance portableLink (storage : portableStorage.entity E) (key : LinkKey E P T) :
    HasLinkResource portableStorage E P T storage key := ⟨PUnit.unit⟩
instance portableColumn (storage : portableStorage.entity T) (path : FieldPath T V) :
    HasColumnResource portableStorage T V storage path := ⟨PUnit.unit⟩

end LeanDb.Model
