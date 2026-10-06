import LeanDb.Model.Metadata
import LeanDb.Typed.Constraint
import LeanDb.Migrate

/-! # Native columns for model values

How the values of `LeanDb.Model` entities are stored in SQLite: the checked scalars as
TEXT/INTEGER through their own parsers (decoded on every read, so no invalid value acquires
`Checked` evidence), `Ref T` as the native integer id, `PasswordHash` as its sealed text,
and every structured value (a list, a record, a variant, a represented type) as ONE TEXT
column of its canonical JSON (`storageColCodec`). -/

namespace LeanDb.Native

private def validationMessage (errors : Ontology.ValidationErrors) : String :=
  String.intercalate ", " (errors.toList.map (·.code))

/-- The portable parser is used on decode AND checked encode. No invalid or
    noncanonical scalar can acquire `Checked` storage evidence. -/
def textCodec {α} [BEq α] (parse : String → Ontology.Validation α)
    (value : α → String) : ColCodec α where
  sqlType := .text
  toCol := fun v => .text (value v)
  fromCol := fun col => do
    let text ← fromCol (α := String) col
    (parse text).mapError validationMessage
  toSql? := fun v =>
    match parse (value v) with
    | .ok checked => if checked == v then some (.text (value v)) else none
    | .error _ => none

instance : ColCodec Ontology.Name := textCodec Ontology.Name.parse Ontology.Name.value
instance : ColCodec Ontology.Title := textCodec Ontology.Title.parse Ontology.Title.value
instance : ColCodec Ontology.Text := textCodec Ontology.Text.parse Ontology.Text.value
instance : ColCodec Ontology.Email := textCodec Ontology.Email.parse Ontology.Email.value
-- Passwords intentionally have no storage instance. Credential storage uses
-- the existing native password-hash type; descriptors do not publish secrets.

theorem textCodec_roundTrip {α} [BEq α] (parse : String → Ontology.Validation α)
    (value : α → String) (law : ∀ x, parse (value x) = .ok x) (x : α) :
    @ColCodec.fromCol α (textCodec parse value) (@ColCodec.toCol α (textCodec parse value) x) = .ok x := by
  change (parse (value x)).mapError validationMessage = .ok x
  rw [law x]
  rfl

instance : LawfulColCodec Ontology.Name where
  roundTrip := textCodec_roundTrip _ _ Ontology.Name.parse_value
instance : LawfulColCodec Ontology.Title where
  roundTrip := textCodec_roundTrip _ _ Ontology.Title.parse_value
instance : LawfulColCodec Ontology.Text where
  roundTrip := textCodec_roundTrip _ _ Ontology.Text.parse_value
instance : LawfulColCodec Ontology.Email where
  roundTrip := textCodec_roundTrip _ _ Ontology.Email.parse_value

instance : Ord Ontology.Name := ⟨fun a b => compare a.value b.value⟩
instance : Ord Ontology.Title := ⟨fun a b => compare a.value b.value⟩
instance : Ord Ontology.Text := ⟨fun a b => compare a.value b.value⟩
instance : Ord Ontology.Email := ⟨fun a b => compare a.value b.value⟩
instance : SqlOrd Ontology.Name := ⟨⟩
instance : SqlOrd Ontology.Title := ⟨⟩
instance : SqlOrd Ontology.Text := ⟨⟩
instance : SqlOrd Ontology.Email := ⟨⟩
instance : LawfulSqlOrd Ontology.Name where
  order_toCol _ _ := rfl
instance : LawfulSqlOrd Ontology.Title where
  order_toCol _ _ := rfl
instance : LawfulSqlOrd Ontology.Text where
  order_toCol _ _ := rfl
instance : LawfulSqlOrd Ontology.Email where
  order_toCol _ _ := rfl

instance : ColCodec Ontology.Instant where
  sqlType := .integer
  toCol := fun value => .int (Int64.ofInt value.value)
  fromCol := fun col => do
    let value ← fromCol (α := Int64) col
    (Ontology.Instant.ofEpochSeconds value.toInt).mapError validationMessage
  toSql? := fun value =>
    if value.value < Ontology.int64Min || value.value > Ontology.int64Max then none
    else some (.int (Int64.ofInt value.value))

instance : LawfulColCodec Ontology.Instant where
  roundTrip := fun value => by
    have range : -9223372036854775808 ≤ value.value ∧ value.value ≤ 9223372036854775807 := value.valid
    have encode : (Int64.ofInt value.value).toInt = value.value :=
      Int64.toInt_ofInt_of_le (by change -9223372036854775808 ≤ value.value; exact range.1)
        (by change value.value < 9223372036854775808; omega)
    change (Ontology.Instant.ofEpochSeconds (Int64.ofInt value.value).toInt).mapError validationMessage = .ok value
    rw [encode, Ontology.Instant.ofEpochSeconds_value]
    rfl

/-- One-schema storage scope for the first milestone. Reject another identity
    scope instead of silently collapsing distinct nominal references. -/
def refToId [Ontology.HasTypeId T] (ref : Ontology.Ref T) : Except String (LeanDb.Id T) := do
  let _ ← (Ontology.Ref.parse (T := T) ref.key ref.scope.value).mapError validationMessage
  if ref.scope.value != "default" then throw "identity.storage_scope_mismatch"
  let some value := ref.key.toInt? | throw "identity.invalid_key"
  return ⟨Int64.ofInt value⟩

def idToRef [Ontology.HasTypeId T] (id : LeanDb.Id T) : Except String (Ontology.Ref T) :=
  (Ontology.Ref.parse (T := T) (toString id.toInt64.toInt)).mapError validationMessage

instance [Ontology.HasTypeId T] : ColCodec (Ontology.Ref T) where
  sqlType := .integer
  -- `toSql?` gates writes; invalid values cannot be Checked.
  toCol := fun ref => .int (Int64.ofInt (ref.key.toInt?.getD 0))
  fromCol := fun col => do idToRef ⟨← fromCol (α := Int64) col⟩
  toSql? := fun ref => (refToId ref).toOption.map (fun id => .int id.toInt64)

@[reducible] instance [Ontology.HasTypeId T] : LeanDb.ReferenceValue (Ontology.Ref T) where
  Target := T
  -- Only checked values reach FK checking; decode uses Ref.parse too.
  id := fun ref => ⟨Int64.ofInt (ref.key.toInt?.getD 0)⟩

instance [Ontology.HasTypeId T] [LeanDb.Entity T] : RefTarget (Ontology.Ref T) where
  target := some (LeanDb.Entity.tableName T)

/-- A structured portable value (a list, a record, a variant with payloads, a
    represented type) stored as ONE TEXT column holding the canonical JSON of its
    `StorageCodec`. Every read decodes through the same codec, including its
    checks; a stored text that is not JSON, or that the codec refuses, is a typed
    `decode` failure naming the table and column (a `DbFault.corruption` for a
    read), never a substitute value. The schema is recorded as the column's
    `wire:` shape, so a changed schema changes the fingerprint and a migration
    over it is refused by name. No SQL `CHECK` is declared: the codec's decode is
    the authoritative check, and a `json_valid` CHECK would only catch a subset. -/
@[reducible] def storageColCodec (α : Type) [codec : LeanDb.Model.StorageCodec α] : ColCodec α where
  sqlType := .text
  toCol := fun value => .text (codec.codec.encode value).compress
  fromCol := fun col => do
    let text ← fromCol (α := String) col
    let json ← (Lean.Json.parse text).mapError fun why => s!"stored value is not JSON: {why}"
    (codec.codec.decode json).mapError validationMessage
  shape := some (externalShapePrefix ++ codec.codec.schema.toJson.compress)

/-- A `PasswordHash` column (e.g. `Credential.hash`): TEXT, the hash's sealed storage text
    (`Trusted.passwordHashText`/`passwordHash`, the adapter boundary). A
    `PasswordHash` has no `Wire`, and `native_schema%` generates no column or
    projection evidence for a field without `Wire`, so no portable read can
    select it. -/
instance : ColCodec Ontology.PasswordHash where
  sqlType := .text
  toCol := fun hash => .text (Ontology.Trusted.passwordHashText hash)
  fromCol := fun col => do
    let text ← fromCol (α := String) col
    return Ontology.Trusted.passwordHash text

/-- Stored hashes read back as exactly the hash written. -/
instance : LawfulColCodec Ontology.PasswordHash where
  roundTrip := fun _ => rfl

/-- Canonicalization migration preflight delegates to the exact shared Email
    parser and reports every row that needs resolution before a unique index. -/
def emailPreflight (rows : List (Int64 × String)) : CanonicalPreflight Ontology.Email :=
  canonicalizationPreflight (fun value => (Ontology.Email.parse value).mapError validationMessage) rows

end LeanDb.Native
