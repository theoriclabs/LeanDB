namespace LeanDb

/-! # Core typed values

The scalar layer: how a Lean value lives in a SQL column, with typed errors.
No domain knowledge lives here; entity structure lives in `LeanDb.Entity`.
-/

/-- A SQL storage class. LeanDB v1 uses INTEGER, TEXT, and REAL. -/
inductive SqlType where
  | integer
  | text
  | real
  deriving Repr, DecidableEq, Inhabited

def SqlType.render : SqlType → String
  | .integer => "INTEGER"
  | .text => "TEXT"
  | .real => "REAL"

/-- A value in a SQL column. -/
inductive Col where
  | int (v : Int64)
  | text (v : String)
  | real (v : Float)
  | null
  deriving Repr, Inhabited, BEq

def Col.describe : Col → String
  | .int v => s!"INTEGER {v}"
  | .text v => s!"TEXT {String.quote v}"
  | .real v => s!"REAL {v}"
  | .null => "NULL"

/-- Drop trailing `'0'`s of a fraction; exact (see `renderRealExact`). -/
private def trimTrailingZeros (l : List Char) : List Char := go l.length
where
  /-- The first `n` chars of `l`, minus any trailing `'0'`s. -/
  go : Nat → List Char
    | 0 => []
    | n + 1 =>
        match l[n]? with
        | some '0' => go n
        | _ => l.take (n + 1)

/-- The exact decimal expansion of a finite `Float`, rendered as a plain
    numeric literal. Why not `Float.toString` (or any shortest-repr): it is
    `printf %f` on this toolchain — six decimals — so a REAL default or a
    frozen migration snapshot silently records a different value (a default
    below 5e-7 collapses to `0.000000`, `1/3` loses all but six digits).
    This decodes the IEEE-754 bits into `m * 2^e`; for `e ≥ 0` the value is
    the exact integer `m * 2^e`, for `e < 0` it is `m * 5^(-e)` with the
    decimal point shifted `(-e)` digits left — `Nat` is arbitrary-precision,
    so no digit is ever rounded away. Trailing zeros of the fractional part
    are dropped (they multiply out exactly); nothing else is trimmed, and
    the result parses back to the very same double. Non-finite values have
    no decimal form and no SQL literal: an error, so callers refuse loudly
    instead of emitting `inf`/`NaN` into DDL. -/
def renderRealExact (v : Float) : Except String String :=
  if v.isNaN then .error "REAL value is NaN: NaN has no exact decimal literal"
  else if v.isInf then .error "REAL value is infinite: infinities have no exact decimal literal"
  else
    let bits := v.toBits.toNat
    let sign := bits >>> 63 != 0
    let biased := (bits >>> 52) &&& 0x7FF
    let mant := bits &&& ((1 <<< 52) - 1)
    let (m, e) : Nat × Int :=
      if biased == 0 then (mant, -1074) else ((1 <<< 52) + mant, (biased : Int) - 1075)
    let body : String :=
      if e >= 0 then
        toString (m * 2 ^ e.toNat)
      else
        let d := (-e).toNat
        let digits := (toString (m * 5 ^ d)).toList
        let (intL, fracL) : List Char × List Char :=
          if digits.length > d then
            (digits.take (digits.length - d), digits.drop (digits.length - d))
          else
            (['0'], List.replicate (d - digits.length) '0' ++ digits)
        let int := String.ofList intL
        match trimTrailingZeros fracL with
        | [] => int
        | frac => int ++ "." ++ String.ofList frac
    .ok (if sign then "-" ++ body else body)

/-- Typed database errors. Constructors are the machine-readable codes;
    the `String` fields are diagnostics, never identity. -/
inductive DbError where
  /-- A stored value failed to decode as its column's Lean type. -/
  | decode (table field message : String)
  /-- Row addressed by id does not exist. -/
  | notFound (table : String) (id : Int64)
  /-- Compare-and-swap `update` lost a race: the row no longer equals `old`. -/
  | stale (table : String) (id : Int64)
  /-- Delete refused because other rows reference this one (FK RESTRICT). -/
  | restricted (table : String) (id : Int64)
  /-- An insert/update points a `Ref` at a row that does not exist. -/
  | missingRef (table : String)
  /-- A uniqueness constraint rejected the write. -/
  | duplicate (table detail : String)
  /-- The instance's schema fingerprint does not match the code's. -/
  | schemaMismatch (expected actual : String)
  /-- The code supplied an internally inconsistent or reserved schema. -/
  | schemaInvalid (message : String)
  /-- A stored value is outside its column's closed world — the vocabulary
      moved without a migration. -/
  | enumDrift (table column value : String)
  /-- A migration was refused or failed; the message says why. -/
  | migrate (message : String)
  /-- The instance's schema is at a fingerprint the base's migration chain
      never produced: it was not created by this base's history. -/
  | unknownLineage (instanceFp : String) (known : List String)
  /-- Raw SQLite error that no typed constructor claims. -/
  | sqlite (message : String)
  /-- A remote client transport failed before a typed server response arrived. -/
  | transport (message : String)
  /-- A failed `ROLLBACK` left the connection's transaction state unknown:
      every later verb is refused until the connection is reopened. -/
  | poisoned (message : String)
  /-- A write verb ran on a connection opened read-only (LDB-09). -/
  | readOnly (verb : String)
  /-- A value read or about to be written fails its entity's declared
      invariant (LDB-16). It is never handed out, and never stored. -/
  | invariant (table name : String)
  /-- `append` was given a child list that does not continue the stored
      one (LDB-15). That is an `update`. -/
  | notAppend (table detail : String)
  deriving Repr

def DbError.code : DbError → String
  | .decode .. => "decode"
  | .notFound .. => "not_found"
  | .stale .. => "stale"
  | .restricted .. => "restricted"
  | .missingRef .. => "missing_ref"
  | .duplicate .. => "duplicate"
  | .schemaMismatch .. => "schema_mismatch"
  | .schemaInvalid .. => "schema"
  | .enumDrift .. => "enum_drift"
  | .migrate .. => "migrate"
  | .unknownLineage .. => "unknown_lineage"
  | .sqlite .. => "sqlite"
  | .transport .. => "transport"
  | .poisoned .. => "poisoned"
  | .readOnly .. => "read_only"
  | .invariant .. => "invariant"
  | .notAppend .. => "not_append"

def DbError.message : DbError → String
  | .decode table field msg => s!"{table}.{field}: {msg}"
  | .notFound table id => s!"{table}: no row with id {id}"
  | .stale table id => s!"{table}: row {id} changed since it was read"
  | .restricted table id => s!"{table}: row {id} is referenced by other rows"
  | .missingRef table => s!"{table}: a referenced row does not exist"
  | .duplicate table detail => s!"{table}: {detail}"
  | .schemaMismatch expected actual =>
      s!"schema fingerprint mismatch: code has {expected}, instance has {actual}"
  | .schemaInvalid msg => s!"invalid schema: {msg}"
  | .enumDrift table column value =>
      s!"{table}.{column}: stored value {String.quote value} is not in the closed world"
  | .migrate msg => msg
  | .unknownLineage fp known =>
      s!"the instance is at schema {fp}, which is not in this base's migration chain {known}: \
it was not created by this base's history (restore a known version, or migrate by hand)"
  | .sqlite msg => msg
  | .transport msg => msg
  | .poisoned msg => s!"connection poisoned: {msg}"
  | .readOnly verb => s!"{verb}: connection is read-only"
  | .invariant table name => s!"{table}: row does not satisfy the invariant {name}"
  | .notAppend table detail => s!"{table}: not an append: {detail}"

instance : ToString DbError := ⟨fun e => s!"[{e.code}] {e.message}"⟩

/-- Process exit code for a failed command (plan.md §4.5): fingerprint
    drift is 4, every other typed error is 2. Matching on the constructor,
    not the code string — strings are diagnostics, never identity. -/
def DbError.exitCode : DbError → UInt32
  | .schemaMismatch .. | .unknownLineage .. => 4
  | _ => 2

/-- Typed row identity: `Id User` and `Id Ticket` are distinct types. -/
structure Id (α : Type) where
  toInt64 : Int64
  deriving DecidableEq, Repr, Hashable

instance : BEq (Id α) := ⟨fun a b => a.toInt64 == b.toInt64⟩
-- manual: the derived instance would demand `Ord α` for a phantom parameter
instance : Ord (Id α) := ⟨fun a b => compare a.toInt64 b.toInt64⟩

/-- Issued AUTOINCREMENT ids are ≥ 1. The type still admits any `Int64`;
    `Table.idsOk` / `Table.refsOk` are the well-formedness clauses. -/
def Id.positive (id : Id α) : Bool := (0 : Int64) < id.toInt64

/-- The `Nat` of an id. For issued (positive) ids this does not clamp. -/
def Id.toNat (id : Id α) : Nat := id.toInt64.toNatClampNeg

/-- A foreign reference to a row of `α`. Definitionally an `Id α`, so a
    `Ref` field compares directly against a fetched row's id. -/
abbrev Ref (α : Type) := Id α

/-- A row as it exists in the database: its identity plus its value. -/
structure Stored (α : Type) where
  id : Id α
  val : α
  deriving Repr

/-- The reference other rows use to point at this row. -/
abbrev Stored.ref (s : Stored α) : Ref α := s.id

/-- How a scalar type lives in one SQL column. Decoding is total over
    honest data and *typed-fails* over anything else — a value that does
    not pass its type's validation never enters the program. -/
class ColCodec (α : Type) where
  sqlType : SqlType
  nullable : Bool := false
  toCol : α → Col
  fromCol : Col → Except String α
  /-- The declared shape of the value when the column holds JSON
      (`ColCodec.json` sets it from the type's `JsonShape`); `none` for a
      scalar codec. A property of the *codec*, not of the type: a `String`
      column and a JSON column whose shape is `String` are different
      things, and only the latter is part of the fingerprint. -/
  shape : Option String := none
  /-- `true` only for the `Bool` codec (and `Option Bool`). INTEGER
      columns otherwise look identical at the spec layer; JSON `true`/`false`
      is accepted only when this is set, so `insert {"qty": false}` on a
      `Nat` cannot silently store 0. Not DDL and not part of the
      fingerprint or schema JSON. -/
  boolCodec : Bool := false
  /-- Encode a value SQLite can store. `none` means it is outside the
      column's SQL range: for `Nat`, larger than `Int64.maxValue`. Ordered
      and equality leaves then become tautologies or contradictions so a
      comparison like `n < 2^64` agrees with its Lean meaning (LDB-18). -/
  toSql? : α → Option Col := fun a => some (toCol a)

export ColCodec (toCol fromCol toSql?)

/-- Round-trip of `toCol` / `fromCol`. A custom codec may omit this
    instance: it still typechecks, but cannot be used where a proof needs
    the round trip (QUERIES.md §3.11, BOUNDARIES §3.2). -/
class LawfulColCodec (α : Type) [ColCodec α] : Prop where
  roundTrip : ∀ v : α, fromCol (α := α) (toCol (α := α) v) = .ok v

/-- Marker for column types whose Lean ordering is preserved by SQLite's
    ordering of their encoded values. The planner only pushes `<`/`≤`/`>`/`≥`
    for these types; equality is pushable for every codec. Custom codecs
    may opt in when their encoding is order-preserving. -/
class SqlOrd (α : Type) : Prop where

/-- Build a codec for a validated newtype from the codec of its raw
    representation and its smart constructor. -/
@[reducible] def ColCodec.via [ColCodec β] (enc : α → β) (dec : β → Except String α) : ColCodec α where
  sqlType := ColCodec.sqlType β
  nullable := ColCodec.nullable β
  toCol a := toCol (enc a)
  fromCol c := do dec (← fromCol c)
  shape := ColCodec.shape β
  boolCodec := false
  toSql? a := ColCodec.toSql? (enc a)

private def expected (want : String) (got : Col) : Except String α :=
  .error s!"expected {want}, found {got.describe}"

instance : ColCodec Int64 where
  sqlType := .integer
  toCol := .int
  fromCol
    | .int v => .ok v
    | c => expected "INTEGER" c

instance : LawfulColCodec Int64 where
  roundTrip _ := rfl

instance : SqlOrd Int64 where

/-- Largest `Nat` a SQLite INTEGER column can hold. -/
def natSqlMax : Nat := Int64.maxValue.toNatClampNeg

/-- Issued id 1 round-trips through `toNat` (AUTOINCREMENT starts at 1). -/
theorem Id.toNat_one {α} : Id.toNat (⟨1⟩ : Id α) = 1 := rfl

/-- `Int64.ofNat` then `toNat` for a value SQLite can store as INTEGER. Closed
    cases (`1`, `2`, …) reduce by `rfl`; the general inequality is `n ≤ natSqlMax`. -/
theorem Id.toNat_ofNat_1 {α} : Id.toNat (⟨Int64.ofNat 1⟩ : Id α) = 1 := rfl

/-- `some` iff `n` fits in a SQLite INTEGER (`0 … Int64.maxValue`). -/
def natToSql (n : Nat) : Option Int64 :=
  if n > natSqlMax then none else some (Int64.ofNat n)

/-- `Nat` stores as INTEGER. Values above `Int64.maxValue` are not
    representable: writes refuse them, and a comparison bound that does
    not fit becomes a tautology or contradiction rather than wrapping
    (so `n < 2^64` agrees with its meaning; LDB-18). -/
instance : ColCodec Nat where
  sqlType := .integer
  toCol n := .int ((natToSql n).getD Int64.maxValue)
  toSql? n := (natToSql n).map .int
  fromCol
    | .int v => if v < 0 then .error s!"expected Nat, found {v}" else .ok v.toNatClampNeg
    | c => expected "INTEGER" c

/-- `Nat` above `Int64.maxValue` encodes by clamping, so there is no
    `LawfulColCodec Nat`. In range the round trip holds, and `SqlOrd Nat`
    is sound on the same bound (`LawfulSqlOrd` in `Pred.lean`). -/
theorem natSqlMax_lt_two_pow_63 : natSqlMax < 2 ^ 63 :=
  Int64.toNatClampNeg_lt Int64.maxValue

theorem nat_lt_two_pow_63_of_le_max {n : Nat} (h : n ≤ natSqlMax) : n < 2 ^ 63 :=
  Nat.lt_of_le_of_lt h natSqlMax_lt_two_pow_63

theorem natToSql_of_le {n : Nat} (h : n ≤ natSqlMax) :
    natToSql n = some (Int64.ofNat n) := by
  unfold natToSql
  split
  · next hgt => exact absurd h (Nat.not_le_of_gt hgt)
  · rfl

theorem fromCol_toCol_nat (n : Nat) (h : n ≤ natSqlMax) :
    fromCol (α := Nat) (toCol n) = Except.ok n := by
  have hn : n < 2 ^ 63 := nat_lt_two_pow_63_of_le_max h
  have henc : toCol (α := Nat) n = Col.int (Int64.ofNat n) := by
    change Col.int ((natToSql n).getD Int64.maxValue) = Col.int (Int64.ofNat n)
    rw [natToSql_of_le h]
    rfl
  rw [henc]
  have hnn : ¬ (Int64.ofNat n < (0 : Int64)) :=
    Int64.not_lt.mpr (Int64.zero_le_ofNat_of_lt hn)
  dsimp [fromCol]
  simp [hnn, Int64.toNatClampNeg_ofNat_of_lt hn]

instance : SqlOrd Nat where

/-- Round-trip of `ColCodec.via` when the decoder inverts the encoder. -/
theorem ColCodec.via_roundTrip {α β : Type} [ColCodec β] [LawfulColCodec β]
    (enc : α → β) (dec : β → Except String α)
    (hdec : ∀ a, dec (enc a) = Except.ok a) (a : α) :
    @fromCol α (ColCodec.via enc dec) (@toCol α (ColCodec.via enc dec) a) = Except.ok a := by
  change (fromCol (α := β) (toCol (enc a)) >>= dec) = Except.ok a
  rw [LawfulColCodec.roundTrip (α := β)]
  exact hdec a

instance : ColCodec UInt32 := ColCodec.via (β := Int64) (fun n => Int64.ofNat n.toNat)
  (fun v => if 0 ≤ v && v < Int64.ofNat UInt32.size then .ok (UInt32.ofNat v.toNatClampNeg)
            else .error s!"UInt32 out of range: {v}")
instance : SqlOrd UInt32 where

private theorem uint32_toNat_lt_two_pow_63 (n : UInt32) : n.toNat < 2 ^ 63 :=
  Nat.lt_trans n.toNat_lt (by decide : UInt32.size < 2 ^ 63)

private theorem uint32_dec_enc (n : UInt32) :
    (fun v : Int64 =>
      if 0 ≤ v && v < Int64.ofNat UInt32.size then
        Except.ok (UInt32.ofNat v.toNatClampNeg)
      else Except.error s!"UInt32 out of range: {v}") (Int64.ofNat n.toNat) = Except.ok n := by
  have hn : n.toNat < 2 ^ 63 := uint32_toNat_lt_two_pow_63 n
  have hsz : UInt32.size < 2 ^ 63 := by decide
  have hge : (0 : Int64) ≤ Int64.ofNat n.toNat := Int64.zero_le_ofNat_of_lt hn
  have hlt : Int64.ofNat n.toNat < Int64.ofNat UInt32.size :=
    (Int64.ofNat_lt_iff_lt hn hsz).mpr n.toNat_lt
  simp [hge, hlt, Int64.toNatClampNeg_ofNat_of_lt hn, UInt32.ofNat_toNat]

instance : LawfulColCodec UInt32 where
  roundTrip n :=
    ColCodec.via_roundTrip (fun n => Int64.ofNat n.toNat)
      (fun v => if 0 ≤ v && v < Int64.ofNat UInt32.size then
          .ok (UInt32.ofNat v.toNatClampNeg)
        else .error s!"UInt32 out of range: {v}")
      uint32_dec_enc n

instance : ColCodec UInt16 := ColCodec.via (β := Int64) (fun n => Int64.ofNat n.toNat)
  (fun v => if 0 ≤ v && v < Int64.ofNat UInt16.size then .ok (UInt16.ofNat v.toNatClampNeg)
            else .error s!"UInt16 out of range: {v}")
instance : SqlOrd UInt16 where

private theorem uint16_toNat_lt_two_pow_63 (n : UInt16) : n.toNat < 2 ^ 63 :=
  Nat.lt_trans n.toNat_lt (by decide : UInt16.size < 2 ^ 63)

private theorem uint16_dec_enc (n : UInt16) :
    (fun v : Int64 =>
      if 0 ≤ v && v < Int64.ofNat UInt16.size then
        Except.ok (UInt16.ofNat v.toNatClampNeg)
      else Except.error s!"UInt16 out of range: {v}") (Int64.ofNat n.toNat) = Except.ok n := by
  have hn : n.toNat < 2 ^ 63 := uint16_toNat_lt_two_pow_63 n
  have hsz : UInt16.size < 2 ^ 63 := by decide
  have hge : (0 : Int64) ≤ Int64.ofNat n.toNat := Int64.zero_le_ofNat_of_lt hn
  have hlt : Int64.ofNat n.toNat < Int64.ofNat UInt16.size :=
    (Int64.ofNat_lt_iff_lt hn hsz).mpr n.toNat_lt
  simp [hge, hlt, Int64.toNatClampNeg_ofNat_of_lt hn, UInt16.ofNat_toNat]

instance : LawfulColCodec UInt16 where
  roundTrip n :=
    ColCodec.via_roundTrip (fun n => Int64.ofNat n.toNat)
      (fun v => if 0 ≤ v && v < Int64.ofNat UInt16.size then
          .ok (UInt16.ofNat v.toNatClampNeg)
        else .error s!"UInt16 out of range: {v}")
      uint16_dec_enc n

instance : ColCodec Bool where
  sqlType := .integer
  toCol b := .int (if b then 1 else 0)
  fromCol
    | .int 0 => .ok false
    | .int 1 => .ok true
    | .int v => .error s!"expected 0 or 1, found {v}"
    | c => expected "INTEGER" c
  boolCodec := true
instance : SqlOrd Bool where

instance : LawfulColCodec Bool where
  roundTrip
    | false => rfl
    | true => rfl

instance : ColCodec String where
  sqlType := .text
  toCol := .text
  fromCol
    | .text v => .ok v
    | c => expected "TEXT" c
instance : SqlOrd String where

instance : LawfulColCodec String where
  roundTrip _ := rfl

instance : ColCodec Float where
  sqlType := .real
  toCol := .real
  fromCol
    -- a non-finite REAL cannot round-trip as a REAL (the JSON surfaces
    -- render it as the string "Infinity"/"NaN"); refuse it like any
    -- other value outside the column's closed world
    | .real v => if v.isNaN || v.isInf then .error s!"expected a finite REAL, found {v}" else .ok v
    | .int v => .ok v.toFloat
    | c => expected "REAL" c

/-- Finite floats round-trip; NaN/Inf are refused by `fromCol`. No
    `LawfulColCodec Float` because those values inhabit `Float`. -/
theorem fromCol_toCol_float (v : Float) (h : v.isNaN = false ∧ v.isInf = false) :
    fromCol (α := Float) (toCol v) = Except.ok v := by
  change (if v.isNaN || v.isInf then
      Except.error s!"expected a finite REAL, found {v}" else Except.ok v) = Except.ok v
  simp [h.1, h.2]

instance : ColCodec (Id α) := ColCodec.via (β := Int64) Id.toInt64 (fun v => .ok ⟨v⟩)
instance : SqlOrd (Id α) where

instance : LawfulColCodec (Id α) where
  roundTrip v :=
    ColCodec.via_roundTrip Id.toInt64 (fun x => Except.ok ⟨x⟩) (fun _ => rfl) v

instance [ColCodec α] : ColCodec (Option α) where
  sqlType := ColCodec.sqlType α
  nullable := true
  shape := ColCodec.shape α
  boolCodec := ColCodec.boolCodec α
  toCol
    | none => .null
    | some a => toCol a
  fromCol
    | .null => .ok none
    | c => .some <$> fromCol (α := α) c
  toSql?
    | none => some .null
    | some a => ColCodec.toSql? a

/-- Inner `toCol` never produces NULL, so `Option` does not collapse
    `some none` with `none`. Nullable codecs (`Option` itself) omit this. -/
class NonNullCodec (α : Type) [ColCodec α] : Prop where
  toCol_ne_null : ∀ a : α, toCol (α := α) a ≠ Col.null

instance : NonNullCodec Int64 where
  toCol_ne_null _ h := nomatch h

instance : NonNullCodec Nat where
  toCol_ne_null n h := by
    change Col.int _ = Col.null at h
    nomatch h

instance : NonNullCodec Bool where
  toCol_ne_null _ h := nomatch h

instance : NonNullCodec String where
  toCol_ne_null _ h := nomatch h

instance : NonNullCodec Float where
  toCol_ne_null _ h := nomatch h

instance : NonNullCodec (Id α) where
  toCol_ne_null _ h := nomatch h

instance : NonNullCodec UInt16 where
  toCol_ne_null _ h := nomatch h

instance : NonNullCodec UInt32 where
  toCol_ne_null _ h := nomatch h

instance [ColCodec α] [LawfulColCodec α] [NonNullCodec α] : LawfulColCodec (Option α) where
  roundTrip
    | none => rfl
    | some a => by
        have hn : toCol (α := α) a ≠ Col.null := NonNullCodec.toCol_ne_null a
        have hr : fromCol (α := α) (toCol (α := α) a) = Except.ok a :=
          LawfulColCodec.roundTrip a
        cases hC : toCol (α := α) a with
        | null => exact (hn hC).elim
        | int v =>
            simp [fromCol, hC] at hr ⊢
            rw [hr]
            rfl
        | text v =>
            simp [fromCol, hC] at hr ⊢
            rw [hr]
            rfl
        | real v =>
            simp [fromCol, hC] at hr ⊢
            rw [hr]
            rfl

/-- A closed world: a payload-free inductive whose constructors are the
    complete vocabulary. Instances come from `deriving LeanDb.ClosedEnum`.
    Closed types are not entities — they have no table of their own to
    insert into or delete from; changing the vocabulary is a code change. -/
class ClosedEnum (α : Type) where
  variants : Array String
  /-- Every value of the closed world, in declaration order — quantify
      over the vocabulary (consistency checks, listings) without leaving
      the total-function discipline. -/
  all : Array α
  encodeName : α → String
  decodeName : String → Option α

/-- `decodeName ∘ encodeName = some`. Derived closed enums satisfy this
    by construction; a custom instance without it still typechecks. -/
class LawfulClosedEnum (α : Type) [ClosedEnum α] : Prop where
  decode_encode : ∀ a : α,
    ClosedEnum.decodeName (α := α) (ClosedEnum.encodeName a) = some a

/-- Closed enums store as TEXT constructor names, guarded by a CHECK
    constraint in the DDL and a drift scan at open. -/
instance [ClosedEnum α] : ColCodec α where
  sqlType := .text
  toCol a := .text (ClosedEnum.encodeName a)
  fromCol
    | .text s =>
        match ClosedEnum.decodeName (α := α) s with
        | some a => .ok a
        | none => .error s!"{String.quote s} is not in the closed world"
    | c => expected "TEXT" c

instance [ClosedEnum α] [LawfulClosedEnum α] : LawfulColCodec α where
  roundTrip a := by
    have h : ClosedEnum.decodeName (α := α) (ClosedEnum.encodeName a) = some a :=
      LawfulClosedEnum.decode_encode a
    change (match ClosedEnum.decodeName (α := α) (ClosedEnum.encodeName a) with
      | some b => Except.ok b
      | none => Except.error s!"{String.quote (ClosedEnum.encodeName a)} is not in the closed world")
      = Except.ok a
    rw [h]

instance [ClosedEnum α] : NonNullCodec α where
  toCol_ne_null _ h := nomatch h

/-- Closed-world metadata for a column type, for CHECK generation and the
    open-time drift scan. -/
class ColEnum (α : Type) where
  variants : Option (Array String) := none

instance (priority := 50) : ColEnum α := ⟨none⟩
instance [ColEnum α] : ColEnum (Option α) := ⟨ColEnum.variants α⟩
instance (priority := 100) [ClosedEnum α] : ColEnum α := ⟨some (ClosedEnum.variants α)⟩

/-- A set over a closed world as an INTEGER bitmask (LEP-0003 A): bit `k`
    is variant `k` in declaration order (`ClosedEnum.variants`, which
    `all` agrees with). At most 62 variants, so every legal mask is a
    positive `Int64`; a larger world is refused at the column boundary
    (`fromCol`, `validateSchema`) — the in-memory operations wrap above
    bit 63 and are only meaningful under that bound. The DDL carries
    `CHECK ((col & ~mask) = 0)`, the open-time drift scan the same test,
    and `Pred.bit` pushes membership as `(col & bit) != 0`. -/
structure EnumSet (α : Type) [ClosedEnum α] where
  bits : UInt64
  deriving DecidableEq, Repr

/-- The all-variants mask of a world of `n` variants — also the CHECK
    bound. Saturates at 64 bits (a world that size is refused anyway). -/
def enumSetMask (n : Nat) : UInt64 :=
  if n ≥ 64 then (0 : UInt64) - 1 else ((1 : UInt64) <<< n.toUInt64) - 1

/-- The most variants an `EnumSet` column admits. -/
def EnumSet.maxVariants : Nat := 62

namespace EnumSet

variable {α : Type} [ClosedEnum α]

/-- A variant's position in declaration order — its bit index. -/
def index (a : α) : Nat :=
  ((ClosedEnum.variants α).findIdx? (· == ClosedEnum.encodeName a)).getD 0

/-- The single-bit mask of a variant. -/
def bitOf (a : α) : UInt64 := (1 : UInt64) <<< (index a).toUInt64

/-- All-variants mask; also the CHECK bound. -/
def mask (α : Type) [ClosedEnum α] : UInt64 := enumSetMask (ClosedEnum.variants α).size

def empty : EnumSet α := ⟨0⟩
def full : EnumSet α := ⟨mask α⟩
def contains (s : EnumSet α) (a : α) : Bool := (s.bits &&& bitOf a) != 0
def insert (s : EnumSet α) (a : α) : EnumSet α := ⟨s.bits ||| bitOf a⟩
def erase (s : EnumSet α) (a : α) : EnumSet α := ⟨s.bits &&& ~~~ bitOf a⟩
def ofList (as : List α) : EnumSet α := as.foldl insert empty
/-- The members, in declaration order. -/
def toList (s : EnumSet α) : List α := (ClosedEnum.all (α := α)).toList.filter s.contains
def size (s : EnumSet α) : Nat := s.toList.length
/-- The members' names, in declaration order (row JSON, diagnostics). -/
def names (s : EnumSet α) : List String := s.toList.map ClosedEnum.encodeName

instance : BEq (EnumSet α) := ⟨fun a b => a.bits == b.bits⟩
instance : Inhabited (EnumSet α) := ⟨empty⟩
instance : EmptyCollection (EnumSet α) := ⟨empty⟩
instance : Membership α (EnumSet α) := ⟨fun s a => s.contains a = true⟩
instance (a : α) (s : EnumSet α) : Decidable (a ∈ s) :=
  inferInstanceAs (Decidable (s.contains a = true))

/-- Index of the lowest set bit (64 when none). -/
def lowestBit (x : UInt64) : Nat := Id.run do
  for k in [0:64] do
    if (x >>> k.toUInt64) &&& 1 != 0 then return k
  return 64

end EnumSet

/-- An `EnumSet` stores as an INTEGER bitmask. Decoding refuses a bit
    outside the world by index, and a world of more than 62 variants
    outright — the same refusal `validateSchema` makes before any file
    is opened. -/
instance [ClosedEnum α] : ColCodec (EnumSet α) where
  sqlType := .integer
  toCol s := .int (Int64.ofNat s.bits.toNat)
  fromCol
    | .int v =>
        let n := (ClosedEnum.variants α).size
        if n > EnumSet.maxVariants then
          .error s!"closed world has {n} variants; EnumSet supports at most {EnumSet.maxVariants}"
        else if v < 0 then .error s!"expected a bitmask of {n} bits, found {v}"
        else
          let bits := v.toNatClampNeg.toUInt64
          let stray := bits &&& ~~~ EnumSet.mask α
          if stray != 0 then
            .error s!"bit {EnumSet.lowestBit stray} is not in the closed world ({n} variants)"
          else .ok ⟨bits⟩
    | c => expected "INTEGER" c

/-- Bitmask-world metadata for a column type, in the `ColEnum` pattern:
    the variant names of an `EnumSet` column, for the CHECK bound, row
    JSON, the fingerprint and the drift scan. -/
class ColEnumSet (α : Type) where
  variants : Option (Array String) := none

instance (priority := 50) : ColEnumSet α := ⟨none⟩
instance [ColEnumSet α] : ColEnumSet (Option α) := ⟨ColEnumSet.variants α⟩
instance (priority := 100) [ClosedEnum α] : ColEnumSet (EnumSet α) :=
  ⟨some (ClosedEnum.variants α)⟩

/-- Foreign-key metadata for a column type. The catch-all instance says
    "not a reference"; `LeanDb.Entity` provides the `Id β` instance. -/
class RefTarget (α : Type) where
  target : Option String := none

instance (priority := 50) : RefTarget α := ⟨none⟩
instance [RefTarget α] : RefTarget (Option α) := ⟨RefTarget.target α⟩

/-- The declared *shape* of a JSON-encoded value type: a canonical,
    deterministic description of what its JSON looks like, so the schema
    fingerprint and `migrate` can see a change inside a JSON column.
    Instances come from `deriving LeanDb.DbJson` (see `LeanDb.Derive`);
    primitives and containers are declared below. A shape reaches a
    column only through `ColCodec.json` (`ColCodec.shape`) — having a
    `JsonShape` does not make a type's columns JSON columns.

    The grammar (parsed back by `LeanDb.Migrate`):
    - `Nat`, `String`, … — a primitive, by name; also a recursive
      reference to the type being described;
    - `Name{f:S,g:S=}` — a structure; `=` marks a field with a default;
    - `Name(c1|c2{k:S,d:S}|c3[S,S])` — an inductive: constructors with a
      named payload (an object), a positional one (an array), or none;
    - `<a|b|c>` — a closed enum, by its variants;
    - `[S]` — a list or array; `S?` — an option; `(S,S)` — a pair. -/
class JsonShape (α : Type) where
  shape : String

namespace JsonShape

def list (s : String) : String := "[" ++ s ++ "]"
def option (s : String) : String := s ++ "?"
def pair (a b : String) : String := "(" ++ a ++ "," ++ b ++ ")"
def closed (variants : Array String) : String :=
  "<" ++ String.intercalate "|" variants.toList ++ ">"

/-- `Name{f:S,g:S=}`; the `Bool` is "has a default". -/
def struct (name : String) (fields : List (String × String × Bool)) : String :=
  name ++ "{" ++ String.intercalate "," (fields.map fun (f, s, d) =>
    f ++ ":" ++ s ++ (if d then "=" else "")) ++ "}"

/-- One constructor's payload: nothing, a named record, or positional. -/
inductive Payload where
  | none
  | named (fields : List (String × String))
  | positional (tys : List String)

def Payload.render : Payload → String
  | .none => ""
  | .named fs => "{" ++ String.intercalate "," (fs.map fun (f, s) => f ++ ":" ++ s) ++ "}"
  | .positional ts => "[" ++ String.intercalate "," ts ++ "]"

/-- `Name(c1|c2{k:S}|c3[S,S])`. -/
def inductive' (name : String) (ctors : List (String × Payload)) : String :=
  name ++ "(" ++ String.intercalate "|" (ctors.map fun (c, p) => c ++ p.render) ++ ")"

end JsonShape

instance : JsonShape Nat := ⟨"Nat"⟩
instance : JsonShape Int := ⟨"Int"⟩
instance : JsonShape String := ⟨"String"⟩
instance : JsonShape Bool := ⟨"Bool"⟩
instance : JsonShape Float := ⟨"Float"⟩
instance : JsonShape UInt8 := ⟨"UInt8"⟩
instance : JsonShape UInt16 := ⟨"UInt16"⟩
instance : JsonShape UInt32 := ⟨"UInt32"⟩
instance : JsonShape UInt64 := ⟨"UInt64"⟩
instance : JsonShape Int64 := ⟨"Int64"⟩
instance : JsonShape Unit := ⟨"Unit"⟩
instance [JsonShape α] : JsonShape (List α) := ⟨JsonShape.list (JsonShape.shape α)⟩
instance [JsonShape α] : JsonShape (Array α) := ⟨JsonShape.list (JsonShape.shape α)⟩
instance [JsonShape α] : JsonShape (Option α) := ⟨JsonShape.option (JsonShape.shape α)⟩
instance [JsonShape α] [JsonShape β] : JsonShape (α × β) :=
  ⟨JsonShape.pair (JsonShape.shape α) (JsonShape.shape β)⟩

/-- Identity marker for a *derived* field: a structure field whose
    default is `derived <expression over earlier fields>` is recomputed by
    `Entity.encode` and checked by `Entity.decode` (see `LeanDb.Derive`).
    Lean does not allow attributes on structure fields, so the mark lives
    in the default itself. -/
@[inline] def derived (a : α) : α := a

/-- One column of a table, fully described. Derived from types — never
    written by hand outside the deriving machinery. -/
structure ColumnSpec where
  name : String
  sqlType : SqlType
  nullable : Bool
  fkTable : Option String
  enum : Option (Array String) := none
  /-- The variant names of an `EnumSet` column (LEP-0003 A): the CHECK is
      `(col & ~mask) = 0` with `mask` over their count, row JSON renders
      the set as an array of these names, and the fingerprint hashes
      them. A column carries `enum` or `enumSet`, never both. -/
  enumSet : Option (Array String) := none
  /-- Declared default, as an evaluated column value — emitted as a SQL
      `DEFAULT`, used when incoming JSON omits the field, and what lets a
      migration add a NOT NULL column to existing rows. -/
  dflt : Option Col := none
  /-- The declared shape of a JSON column's value (`ColCodec.shape`, set
      by `ColCodec.json` from the type's `JsonShape`); `none` for scalars.
      Not DDL — the column is TEXT either way — but part of the
      fingerprint and of what `migrate` diffs. -/
  shape : Option String := none
  /-- The parent field this column was flattened out of (LEP-0003 C): a
      field `launch : LaunchConfig` of an `Inline` type contributes the
      columns `launch_block`, `launch_smemBytes`, … each with
      `group := some "launch"`. Row JSON nests them back under that key;
      `schema` JSON shows it. Not DDL and not part of the fingerprint —
      the table has plain columns either way. -/
  group : Option String := none
  /-- A foreign key that cascades on delete (LEP-0003 D): the `parent`
      column of a generated child table, whose rows are *part of the
      parent's value*, not references to it. The one cascade in the
      engine; every other `Ref` column RESTRICTs. DDL and the fingerprint
      see it; `schema` JSON carries it. -/
  cascade : Bool := false
  /-- Live decode hint: this INTEGER column is a `Bool`. Not serialized
      in `schema_json` and not part of `BEq` — stored schemas from older
      engines stay identical, and `migrate` must not see a phantom change. -/
  boolCodec : Bool := false
  deriving Repr, Inhabited

instance : BEq ColumnSpec where
  beq a b :=
    a.name == b.name && a.sqlType == b.sqlType && a.nullable == b.nullable &&
    a.fkTable == b.fkTable && a.enum == b.enum && a.enumSet == b.enumSet &&
    a.dflt == b.dflt && a.shape == b.shape && a.group == b.group &&
    a.cascade == b.cascade

/-- The single way a `ColumnSpec` is made: from a field's type. -/
def columnSpec (name : String) (α : Type) (dflt : Option Col := none)
    [ColCodec α] [RefTarget α] [ColEnum α] [ColEnumSet α]
    (group : Option String := none) (cascade : Bool := false) : ColumnSpec where
  name := name
  sqlType := ColCodec.sqlType α
  nullable := ColCodec.nullable α
  fkTable := RefTarget.target α
  enum := ColEnum.variants α
  enumSet := ColEnumSet.variants α
  dflt := dflt
  shape := ColCodec.shape α
  group := group
  cascade := cascade
  boolCodec := ColCodec.boolCodec α

/-- A declared index or composite UNIQUE (LDB-03). -/
structure IndexSpec where
  unique : Bool := false
  columns : Array String
  partialWhere : Option String := none
  name : Option String := none
  deriving Repr, BEq

def IndexSpec.resolvedName (table : String) (ix : IndexSpec) : String :=
  match ix.name with
  | some n => n
  | none =>
      (if ix.unique then "uq_" else "ix_") ++ table ++ "_" ++
        String.intercalate "_" ix.columns.toList

structure TableSpec where
  name : String
  columns : Array ColumnSpec
  indexes : Array IndexSpec := #[]
  /-- The name of the entity's declared invariant (LDB-16), if any. The
      check itself is a Lean function on the entity; its name is what the
      schema records, so declaring or renaming it is a migration. -/
  invariant : Option String := none
  deriving Repr, BEq

/-- An auxiliary object next to the fingerprinted schema (LDB-11). -/
inductive Auxiliary where
  | fts5 (name : String) (contentTable : String) (columns : Array String)
      (tokenizer : String := "unicode61")
  deriving Repr, BEq

/-- SQLite `PRAGMA synchronous` (LDB-02). Default `.full` matches today. -/
inductive Synchronous where
  | off | normal | full | extra
  deriving Repr, DecidableEq

def Synchronous.toSql : Synchronous → String
  | .off => "OFF"
  | .normal => "NORMAL"
  | .full => "FULL"
  | .extra => "EXTRA"

def Synchronous.ofString? : String → Option Synchronous
  | "off" | "OFF" | "0" => some .off
  | "normal" | "NORMAL" | "1" => some .normal
  | "full" | "FULL" | "2" => some .full
  | "extra" | "EXTRA" | "3" => some .extra
  | _ => none

/-- Open-time pragmas (LDB-02). Defaults are byte-identical to 0.3.x. -/
structure OpenConfig where
  busyTimeoutMs : Nat := 5000
  synchronous : Synchronous := .full
  cacheSizeKiB : Option Nat := none
  mmapBytes : Option Nat := none
  walAutocheckpoint : Option Nat := none
  tempStoreMemory : Bool := false
  extraPragmas : List (String × String) := []
  deriving Repr

def OpenConfig.allowedPragmas : List String :=
  ["optimize", "analysis_limit", "secure_delete", "threads", "recursive_triggers",
   "cache_spill", "hard_heap_limit", "soft_heap_limit"]

def OpenConfig.checkExtra (c : OpenConfig) : Except String Unit := do
  for (name, _) in c.extraPragmas do
    unless OpenConfig.allowedPragmas.contains name.toLower do
      throw s!"PRAGMA {name} is not allowlisted (allowed: {OpenConfig.allowedPragmas})"

/-- Audit-log verb policy (LDB-05). `.all` is the CLI default. -/
inductive LogVerbs where
  | all
  | failuresAndPlans
  | failuresOnly
  | none
  deriving Repr, DecidableEq

def LogVerbs.ofString? : String → Option LogVerbs
  | "all" => some .all
  | "failuresAndPlans" | "failures_and_plans" => some .failuresAndPlans
  | "failuresOnly" | "failures_only" => some .failuresOnly
  | "none" => some .none
  | _ => none

/-- Decode one column, attaching table/field context to failures. -/
def decodeField (table field : String) (α : Type) [ColCodec α] (c : Col) : Except DbError α :=
  match fromCol c with
  | .ok a => .ok a
  | .error msg => .error (.decode table field msg)

/-- `decodeField` for a value that has no table of its own (an `Inline`
    structure's field): the failure is a `String` of the form
    `"<field>: <message>"`, which the parent entity's `decode` turns into
    `DbError.decode table "<parent>_<field>"` (`inlineDecodeError`). -/
def decodeFieldStr (field : String) (α : Type) [ColCodec α] (c : Col) : Except String α :=
  match fromCol c with
  | .ok a => .ok a
  | .error msg => .error s!"{field}: {msg}"

end LeanDb
