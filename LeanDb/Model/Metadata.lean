import LeanOntology

/-! # Data-model metadata

What `deriving Domain` / `deriving Entity` record about an authored type: its wire name,
its fields and their kinds, field paths and lawful lenses, and the descriptors of declared
constraints and links. Portable: this module imports `LeanOntology` and Lean only. -/

namespace LeanDb.Model
open Ontology

/- The checked value types and references of `LeanOntology`, with their parsers, so
`open LeanDb.Model` is enough for model code. (An exported type does not export its
namespace: each function used as `Name.parse` is listed.) -/
export Ontology (
  Ref Ref.parse Name Name.parse Title Title.parse Text Text.parse Email Email.parse
  Password Password.parse PasswordHash Session Session.profile
  Instant Instant.ofEpochSeconds Instant.parse Instant.format Instant.rfc3339)

/-- A UTC instant. (Entity identities are `Ref T`; there is no `Id` alias, because core `Id`
is the identity monad.) -/
abbrev Time : Type := Instant

/-- Readable UTC display text, `YYYY-MM-DD HH:MM UTC` (`:SS` only when nonzero). The wire
form is RFC 3339 (`Instant.rfc3339`). -/
def Time.format (time : Time) : String := Instant.format time

inductive FieldKind where
  | scalar | value | reference (target : TypeId)
  deriving Repr, BEq

/-- A hint for form generators; storage never reads it. -/
inductive EditorKind where
  | text | email | password | instant | boolean | number | choices | none
  deriving Repr, BEq

structure EditorMetadata where
  kind : EditorKind := .text
  required : Bool := true
  deriving Repr, BEq

structure FieldMetadata where
  name : String
  kind : FieldKind
  editor : EditorMetadata := {}
  hasDefault : Bool := false
  defaultDeclaration : Option String := none
  deriving Repr, BEq

class FieldType (T : Type) where
  kind : FieldKind
  editor : EditorMetadata := {}

instance [HasTypeId T] : FieldType (Ref T) := ⟨.reference (HasTypeId.typeId (α := T)), ⟨.none, false⟩⟩
instance : FieldType Name := ⟨.scalar, ⟨.text, true⟩⟩
instance : FieldType Title := ⟨.scalar, ⟨.text, true⟩⟩
instance : FieldType Text := ⟨.scalar, ⟨.text, false⟩⟩
instance : FieldType Email := ⟨.scalar, ⟨.email, true⟩⟩
instance : FieldType Password := ⟨.scalar, ⟨.password, true⟩⟩
instance : FieldType Instant := ⟨.scalar, ⟨.instant, true⟩⟩
instance : FieldType String := ⟨.scalar, ⟨.text, false⟩⟩
instance : FieldType Bool := ⟨.scalar, ⟨.boolean, false⟩⟩
instance : FieldType Nat := ⟨.scalar, ⟨.number, true⟩⟩
instance : FieldType Int := ⟨.scalar, ⟨.number, true⟩⟩
instance : FieldType PasswordHash := ⟨.scalar, ⟨.none, false⟩⟩
instance [FieldType T] : FieldType (List T) := ⟨.value, ⟨.none, false⟩⟩
instance [FieldType T] : FieldType (Disclosure T) := ⟨.value, ⟨.none, false⟩⟩

class Domain (T : Type) extends HasTypeId T where
  isEntity : Bool := false
  fields : List FieldMetadata := []
  cases : List String := []

instance [Domain T] : FieldType T := ⟨.value, ⟨if (Domain.cases (T := T)).isEmpty then .none else .choices, true⟩⟩

/-- A stored record type. Storage identity alone never grants publication. -/
class Entity (T : Type) extends Domain T where
  /-- The row representation (each field through its `StorageCodec`); never registered as `Wire`. -/
  recordRepresentation : Codec T
  entityOnly : isEntity = true

/-- A single-field unique constraint (`constraint T.c : unique field`), as the native schema reads it. -/
structure Unique (T Value : Type) where
  identity : String
  field : FieldPath T Value

/-- How an entity field is stored. Wire values store as their wire form; server-only values
(`PasswordHash`) have a storage codec and no `Wire`, so they can be columns but never output. -/
class StorageCodec (α : Type) where
  codec : Codec α
instance (priority := low) [Wire α] : StorageCodec α := ⟨Wire.codec⟩
instance : StorageCodec PasswordHash := ⟨PasswordHash.storageCodec⟩

/-- A join through an edge entity `E` that references a parent `P` and a target `T` (e.g. a
`Loan` between a `Book` and a `Member`). `identity` is `"<E>.<parentField>.<targetField>"`.
Declared by `link E.parentField E.targetField` as `E.link.<parentField>.<targetField>`. -/
structure LinkKey (E P T : Type) where
  identity : String
  parent : E → Ref P
  target : E → Ref T

/-- A declared unique constraint as a storage request carries it: its identity, its fields,
and the value it is reported as when it is violated. -/
structure Constraint (Error : Type) where
  identity : String
  fields : List String
  publicFailure : Error

/-- Domain records reuse Ontology's typed getter/path surface. -/
class HasRecord (T : Type) where
  record : RecordDescriptor T
  fieldMetadata : List FieldMetadata := []
  defaultValues : List (String × Lean.Json) := []

class EditableField (T : Type) (field : String) (V : outParam Type) where
  lens : Lens T V
  laws : lens.Laws

class NamedField (T : Type) (name : String) [HasRecord T] where
  field : (HasRecord.record (T := T)).Field

/-- A selective field patch assembled only from generated lawful lenses. -/
structure Change (T : Type) where
  private mk ::
  apply : T → T
  fields : List String

def Change.set [EditableField T field V] (value : V) : Change T :=
  ⟨fun current => (EditableField.lens (T := T) (field := field)).set current value, [field]⟩

def Change.andThen (a b : Change T) : Change T :=
  ⟨fun value => b.apply (a.apply value), a.fields ++ b.fields⟩

/-- Whole-record replacement used by plain `T.update`; every declared field may change.
Interpreters check only constraints whose fields actually differ (touched-field rule). -/
def Change.replace [Domain T] (value : T) : Change T :=
  ⟨fun _ => value, (Domain.fields (T := T)).map (·.name)⟩

/-- A declared unique constraint over one or more fields of `T`, keyed by `K`.
`identity` is the qualified constraint name (e.g. `Customer.uniqueEmail`); `fields` are the
declared field names in order; `key` projects the constrained value. -/
structure UniqueKey (T K : Type) where
  identity : String
  fields : List String
  key : T → K
  equal : K → K → Bool

/-- No failure fallback: generated fields have already passed a declaration-time name check. -/
def recordCodec (identity : TypeId) (fields : RecordFields T T) : Codec T where
  schema := .named identity "1" (.record fields.schema)
  encode value := .mkObj (fields.encode value)
  decode value := do
    JsonWire.object (fields.schema.map Prod.fst) value
    fields.decode value

/-- Avoid Lean 4.33 specialization of closed enum encoders while preserving their exact codec. -/
@[noinline, nospecialize] def encodeDefault (codec : Codec V) (value : V) : Lean.Json := codec.encode value

/-- Closed payload-free enums; other inductives need a checked representation adapter (`represent`). -/
def enumCodec (identity : TypeId) (cases : List (String × T)) (tag : T → String) : Codec T where
  schema := .named identity "1" (.variant (cases.map (fun c => (c.1, .unit))))
  -- A bare string; the older `{"tag","value":null}` form still decodes.
  encode value := .str (tag value)
  decode value := do
    let name ← match value with
      | .str name => pure name
      | _ => do
        JsonWire.object ["tag", "value"] value
        let _ ← Codec.field "value" Codec.unit value
        JsonWire.stringField "tag" value
    match cases.find? (fun c => c.1 == name) with
    | some c => pure c.2
    | none => Validation.fail "decode.unknown_tag" [.key "tag"] [("actual", name)]

/-- One constructor of a closed variant: its tag, its named payload fields (empty for a
payload-free constructor), and the decoder of its payload record. -/
structure VariantCase (T : Type) where
  tag : String
  fields : List (String × WireSchema) := []
  decode : Lean.Json → Validation T

/-- Closed variants with named payload fields: the bare string `"ctor"` for a payload-free
constructor (the older `{"tag": ctor, "value": null}` still decodes),
`{"tag": ctor, "value": {field: …}}` otherwise. -/
def variantCodec (identity : TypeId) (cases : List (VariantCase T)) (encode : T → String × Option Lean.Json) :
    Codec T where
  schema := .named identity "1" (.variant (cases.map fun c => (c.tag, if c.fields.isEmpty then .unit else .record c.fields)))
  encode value := match encode value with
    | (tag, none) => .str tag
    | (tag, some payload) => JsonWire.tagged tag payload
  decode value := do
    if let .str name := value then
      match cases.find? (fun c => c.tag == name && c.fields.isEmpty) with
      | some c => return ← c.decode .null
      | none => Validation.fail "decode.unknown_tag" [] [("actual", name)]
    JsonWire.object ["tag", "value"] value
    let name ← JsonWire.stringField "tag" value
    match cases.find? (fun c => c.tag == name) with
    | none => Validation.fail "decode.unknown_tag" [.key "tag"] [("actual", name)]
    | some c =>
      if c.fields.isEmpty then
        let _ ← Codec.field "value" Codec.unit value
        c.decode .null
      else
        let payload ← JsonWire.get "value" value
        JsonWire.object (c.fields.map Prod.fst) payload
        c.decode payload

end LeanDb.Model
