import LeanApp.Domain.Metadata
import LeanDb.Typed.Members
import LeanDb.Typed.Constraint

/-! Optional portable/native storage bridge. Build with BOTH packages on the
    import path; core LeanDB does not depend on LeanApp or the browser compiler.
    No application rows, scalar parsers, portable vocabulary, or auth engine. -/

namespace LeanDb.Domain

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

instance : ColCodec LeanApp.Domain.Name := textCodec LeanApp.Domain.Name.parse LeanApp.Domain.Name.value
instance : ColCodec LeanApp.Domain.Title := textCodec LeanApp.Domain.Title.parse LeanApp.Domain.Title.value
instance : ColCodec LeanApp.Domain.Text := textCodec LeanApp.Domain.Text.parse LeanApp.Domain.Text.value
instance : ColCodec LeanApp.Domain.Email := textCodec LeanApp.Domain.Email.parse LeanApp.Domain.Email.value
-- Passwords intentionally have no storage instance. Credential storage uses
-- the existing native password-hash type; descriptors do not publish secrets.

theorem textCodec_roundTrip {α} [BEq α] (parse : String → Ontology.Validation α)
    (value : α → String) (law : ∀ x, parse (value x) = .ok x) (x : α) :
    @ColCodec.fromCol α (textCodec parse value) (@ColCodec.toCol α (textCodec parse value) x) = .ok x := by
  change (parse (value x)).mapError validationMessage = .ok x
  rw [law x]
  rfl

instance : LawfulColCodec LeanApp.Domain.Name where
  roundTrip := textCodec_roundTrip _ _ LeanApp.Domain.Name.parse_value
instance : LawfulColCodec LeanApp.Domain.Title where
  roundTrip := textCodec_roundTrip _ _ LeanApp.Domain.Title.parse_value
instance : LawfulColCodec LeanApp.Domain.Text where
  roundTrip := textCodec_roundTrip _ _ LeanApp.Domain.Text.parse_value
instance : LawfulColCodec LeanApp.Domain.Email where
  roundTrip := textCodec_roundTrip _ _ LeanApp.Domain.Email.parse_value

instance : Ord LeanApp.Domain.Name := ⟨fun a b => compare a.value b.value⟩
instance : Ord LeanApp.Domain.Title := ⟨fun a b => compare a.value b.value⟩
instance : Ord LeanApp.Domain.Text := ⟨fun a b => compare a.value b.value⟩
instance : Ord LeanApp.Domain.Email := ⟨fun a b => compare a.value b.value⟩
instance : SqlOrd LeanApp.Domain.Name := ⟨⟩
instance : SqlOrd LeanApp.Domain.Title := ⟨⟩
instance : SqlOrd LeanApp.Domain.Text := ⟨⟩
instance : SqlOrd LeanApp.Domain.Email := ⟨⟩
instance : LawfulSqlOrd LeanApp.Domain.Name where
  order_toCol _ _ := rfl
instance : LawfulSqlOrd LeanApp.Domain.Title where
  order_toCol _ _ := rfl
instance : LawfulSqlOrd LeanApp.Domain.Text where
  order_toCol _ _ := rfl
instance : LawfulSqlOrd LeanApp.Domain.Email where
  order_toCol _ _ := rfl

instance : ColCodec LeanApp.Domain.Instant where
  sqlType := .integer
  toCol := fun value => .int (Int64.ofInt value.value)
  fromCol := fun col => do
    let value ← fromCol (α := Int64) col
    (LeanApp.Domain.Instant.ofEpochSeconds value.toInt).mapError validationMessage
  toSql? := fun value =>
    if value.value < LeanApp.Domain.int64Min || value.value > LeanApp.Domain.int64Max then none
    else some (.int (Int64.ofInt value.value))

instance : LawfulColCodec LeanApp.Domain.Instant where
  roundTrip := fun value => by
    have range : -9223372036854775808 ≤ value.value ∧ value.value ≤ 9223372036854775807 := value.valid
    have encode : (Int64.ofInt value.value).toInt = value.value :=
      Int64.toInt_ofInt_of_le (by change -9223372036854775808 ≤ value.value; exact range.1)
        (by change value.value < 9223372036854775808; omega)
    change (LeanApp.Domain.Instant.ofEpochSeconds (Int64.ofInt value.value).toInt).mapError validationMessage = .ok value
    rw [encode, LeanApp.Domain.Instant.ofEpochSeconds_value]
    rfl

/-- One-schema storage scope for the first milestone. Reject another identity
    scope instead of silently collapsing distinct nominal references. -/
def refToId [Ontology.HasTypeId T] (ref : LeanApp.Domain.Ref T) : Except String (LeanDb.Id T) := do
  let _ ← (LeanApp.Domain.Ref.parse (T := T) ref.key ref.scope.value).mapError validationMessage
  if ref.scope.value != "default" then throw "identity.storage_scope_mismatch"
  let some value := ref.key.toInt? | throw "identity.invalid_key"
  return ⟨Int64.ofInt value⟩

def idToRef [Ontology.HasTypeId T] (id : LeanDb.Id T) : Except String (LeanApp.Domain.Ref T) :=
  (LeanApp.Domain.Ref.parse (T := T) (toString id.toInt64.toInt)).mapError validationMessage

instance [Ontology.HasTypeId T] : ColCodec (LeanApp.Domain.Ref T) where
  sqlType := .integer
  -- `toSql?` gates writes; invalid values cannot be Checked.
  toCol := fun ref => .int (Int64.ofInt (ref.key.toInt?.getD 0))
  fromCol := fun col => do idToRef ⟨← fromCol (α := Int64) col⟩
  toSql? := fun ref => (refToId ref).toOption.map (fun id => .int id.toInt64)

@[reducible] instance [Ontology.HasTypeId T] : LeanDb.ReferenceValue (LeanApp.Domain.Ref T) where
  Target := T
  -- Only checked values reach FK checking; decode uses Ref.parse too.
  id := fun ref => ⟨Int64.ofInt (ref.key.toInt?.getD 0)⟩

instance [Ontology.HasTypeId T] [LeanDb.Entity T] : RefTarget (LeanApp.Domain.Ref T) where
  target := some (LeanDb.Entity.tableName T)

/-- A `PasswordHash` column (e.g. `Credential.hash`): TEXT, the hash's sealed storage text
    (`Trusted.passwordHashText`/`passwordHash`, the adapter boundary). A
    `PasswordHash` has no `Wire`, and `native_schema%` generates no column or
    projection evidence for a field without `Wire`, so no portable read can
    select it. -/
instance : ColCodec LeanApp.Domain.PasswordHash where
  sqlType := .text
  toCol := fun hash => .text (LeanApp.Domain.Trusted.passwordHashText hash)
  fromCol := fun col => do
    let text ← fromCol (α := String) col
    return LeanApp.Domain.Trusted.passwordHash text

/-- Stored hashes read back as exactly the hash written. -/
instance : LawfulColCodec LeanApp.Domain.PasswordHash where
  roundTrip := fun _ => rfl

@[reducible] instance : LeanDb.MemberDeclaration (LeanApp.Domain.Members T) where
  Target := T
  empty := {}

/-- Canonicalization migration preflight delegates to the exact shared Email
    parser and reports every row that needs resolution before a unique index. -/
def emailPreflight (rows : List (Int64 × String)) : CanonicalPreflight LeanApp.Domain.Email :=
  canonicalizationPreflight (fun value => (LeanApp.Domain.Email.parse value).mapError validationMessage) rows

end LeanDb.Domain
