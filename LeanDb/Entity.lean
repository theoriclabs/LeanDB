import LeanDb.Core

namespace LeanDb

/-! # Entities

An entity is a flat structure whose fields are `ColCodec` scalars, `Option`s
of them, `Ref`s to other entities, `Inline` structures (flattened into
sibling columns, LEP-0003 C) or `List`s of `Inline` records (child tables,
LEP-0003 D). Instances are produced by `deriving LeanDb.Entity` (see
`LeanDb.Derive`) — the types are the schema's single source of truth, so
nothing here is ever written by hand.

Each entity also gets a generated *field symbol* type (`Ticket.Field`),
which is how the engine names a column; the column's string name is
derived from the symbol (`Entity.fieldSpec`), never the reverse.
-/

/-- A child table of an entity (LEP-0003 D): the generated entity
    `Parent.Ins` behind a field `ins : List R` of `Parent`, seen from the
    parent's side. Everything is typed by the parent value and encoded
    columns — no SQL, no monad — so the executor (`LeanDb.Db`) and the JSON
    boundary (`LeanDb.Json`) share one description of what a child list
    is. The child's first two columns are always `parent` (the FK, `ON
    DELETE CASCADE`) and `position` (list order); the rest are the
    record's columns, as its `Inline` instance encodes them. -/
structure ChildLink (α : Type) where
  /-- The parent's field name (`"ins"`): the key in row JSON. -/
  field : String
  /-- The child table's name (`"<parent_table>_<field>"`). -/
  table : String
  /-- The child table's spec: `parent`, `position`, then the record's columns. -/
  spec : TableSpec
  /-- Every child row's record columns (after `parent` and `position`), in
      list order: the record's `Inline.encode`. -/
  rows : α → Array (Array Col)
  /-- Attach the list read back from the child table — `(position, record
      columns)` pairs already filtered to this parent and sorted by
      position — and *check* every derived column that is computed from
      this list against its recomputation (the read-side half of a
      derived column, which `decode` could not do without the list). -/
  attach : Array (Nat × Array Col) → α → Except DbError α
  /-- `attach` for the JSON boundary: derived columns computed from this
      list are *recomputed* rather than checked (`decodeRecomputing` ran
      with the list empty). -/
  attachRecomputing : Array (Nat × Array Col) → α → Except DbError α

/-- The record columns of a child table: everything after `parent` and
    `position`. -/
def ChildLink.recordColumns (l : ChildLink α) : Array ColumnSpec :=
  l.spec.columns.extract 2 l.spec.columns.size

class Entity (α : Type) where
  /-- The field symbols: a generated inductive with one constructor per
      declared field, in declaration order (`Ticket.Field.title`). Column
      identity inside the engine is one of these, never a string. -/
  Field : Type
  /-- The declared Lean type of a field. -/
  fieldTy : Field → Type
  /-- Read a field off a value. -/
  get : (f : Field) → α → fieldTy f
  /-- The field type's own codec, reachable from the symbol. -/
  codec : (f : Field) → ColCodec (fieldTy f)
  /-- The column as DDL/JSON/migrations see it. The ONLY place a field's
      name is a string; everything else reaches it through the symbol. -/
  fieldSpec : Field → ColumnSpec
  /-- Every symbol, in declaration order. -/
  fields : Array Field
  tableName : String
  /-- The Lean name of the entity type (`Tickets.Ticket`), for generated
      source that must refer to it (`migrate freeze`). -/
  typeName : String := ""
  /-- Field values in declaration order, id excluded. -/
  encode : α → Array Col
  /-- Inverse of `encode` over honest data; typed failure otherwise. A
      derived column (`LeanDb.derived` in its default) is decoded AND
      recomputed from its sources; disagreement is a `decode` error naming
      the column — a raw-SQL write cannot desynchronize it unnoticed. -/
  decode : Array Col → Except DbError α
  /-- Is this field derived from earlier fields? `encode` recomputes such
      a column from its sources; JSON input may omit it. -/
  isDerived : Field → Bool
  /-- `decode` for a JSON boundary: derived columns are recomputed from
      their sources rather than read, so the input may omit them or carry
      a stale value (an `update` that changes the source). -/
  decodeRecomputing : Array Col → Except DbError α
  /-- Child tables (LEP-0003 D): one per `List R` field with `R` an
      `Inline` record — the generated child entity's table and spec, and
      how to read the list off a value and attach it back. `decode`
      leaves every child list empty; the executor attaches them. -/
  children : List (ChildLink α) := []
  /-- A condition every stored value satisfies (LDB-16): its name, as the
      schema records it, and the check. The executor checks it after the
      child lists are attached on every read, and before every write. -/
  invariant : Option (String × (α → Bool)) := none
  /-- Whether every column of `v` fits in its SQLite encoding (`toSql?`).
      Derived instances generate a conjunction of `toSql?.isSome` so a
      `Nat` above `Int64.maxValue` is not `Checked`. The default is `true`
      (no columns). -/
  rangeOk : α → Bool := fun _ => true

/- Instance lookup reduces types only at reducible transparency, so a type
   stated through a class projection (`SqlOrd (Entity.fieldTy f)`,
   `OfNat (Entity.fieldTy f) 40`) is found only if the projection and the
   instance both unfold there. The derived instances are `@[reducible]`;
   these are the projections that appear in types. -/
attribute [reducible] Entity.Field Entity.fieldTy Entity.codec Entity.rangeOk

/-! ## Inline structures (LEP-0003 C)

A small flat structure (`LaunchConfig`) stored *inside* an entity's row
as one column per field, not in a table of its own. `deriving
LeanDb.Inline` generates the `Entity` surface minus the table; the
entity that holds a field of an `Inline` type flattens it at derive time
into columns `<field>_<sub>` with one symbol per column
(`Kernel.Field.launch_smemBytes`), so the planner, DDL, migrations and
`rows --eq` see plain columns. Row JSON nests them back under the field
name (`ColumnSpec.group`). An `Inline` type is not an entity: no id, no
table, no `Ref` to it. -/

class Inline (α : Type) where
  /-- The field symbols, one per field in declaration order. -/
  Field : Type
  fieldTy : Field → Type
  get : (f : Field) → α → fieldTy f
  codec : (f : Field) → ColCodec (fieldTy f)
  /-- The column as it would stand alone (name = the field name, no
      group); the parent renames it `<field>_<sub>` and sets the group. -/
  fieldSpec : Field → ColumnSpec
  fields : Array Field
  /-- Field values in declaration order. -/
  encode : α → Array Col
  /-- Inverse of `encode` over honest data. Failure is a `String` of the
      form `"<sub>: <message>"` (`"*: …"` for an arity mismatch): the
      value has no table, so the parent supplies that context. -/
  decode : Array Col → Except String α

attribute [reducible] Inline.Field Inline.fieldTy Inline.codec

/-- The symbol type of an `Inline` structure determines it — the
    `FieldOf` of inline types, generated with every `deriving
    LeanDb.Inline`. (`FieldOf` itself is keyed on `Entity`, and an inline
    type is not one.) -/
class Inline.FieldOf (F : Type) (α : outParam Type) [Inline α] where
  sym : F → Inline.Field α

attribute [reducible] Inline.FieldOf.sym

/-- The stand-alone column specs of an inline structure, in declaration order. -/
def Inline.columns (α : Type) [Inline α] : Array ColumnSpec :=
  (Inline.fields (α := α)).map fun f => Inline.fieldSpec f

/-- The stand-alone column name of an inline field symbol. -/
def Inline.fieldName [Inline α] (f : Inline.Field α) : String :=
  (Inline.fieldSpec f).name

/-- The `Inline.decode` failure of the value in field `field` of `table`,
    as the parent's typed error: `"<sub>: <message>"` names the column
    `<field>_<sub>`, anything else the whole group `<field>_*`. -/
def inlineDecodeError (table field : String) (msg : String) : DbError :=
  match msg.splitOn ": " with
  | sub :: rest@(_ :: _) =>
      let sub := if sub == "*" || sub.isEmpty then "*" else sub
      .decode table s!"{field}_{sub}" (String.intercalate ": " rest)
  | _ => .decode table s!"{field}_*" msg

/-- The symbol type determines its entity. Unification cannot invert
    `Entity.Field ?α =?= Ticket.Field`, so a column reference written from
    the symbol alone (`Col.here Ticket.Field.title`) recovers the entity
    through this class instead; `sym` is the identity, generated with
    every `deriving LeanDb.Entity`. -/
class FieldOf (F : Type) (α : outParam Type) [Entity α] where
  sym : F → Entity.Field α

attribute [reducible] FieldOf.sym

/-- An abstract entity's own symbol type. A boundary that resolved a column
    name through `fieldOfName?` holds an `Entity.Field α` for an `α` it
    knows only through its instance, and can still name the column
    (`Col.here f`). Low priority and keyed on `Entity.Field ?α`, so the
    generated instances — keyed on the concrete symbol type — are found
    first and this one never competes with them. -/
@[reducible] instance (priority := low) instFieldOfEntityField [Entity α] :
    FieldOf (Entity.Field α) α := ⟨id⟩

/-- The column specs, in declaration order — computed from the symbols,
    so the string is derived from the symbol and never the other way. -/
def Entity.columns (α : Type) [Entity α] : Array ColumnSpec :=
  (Entity.fields (α := α)).map fun f => Entity.fieldSpec f

/-- The column name of a field symbol (render-only: SQL, JSON, diagnostics). -/
def Entity.fieldName [Entity α] (f : Entity.Field α) : String :=
  (Entity.fieldSpec f).name

/-- Parse a column name at a boundary (argv, JSON, a stored plan) into the
    symbol; `none` names no column of `α`. -/
def Entity.fieldOfName? (α : Type) [Entity α] (s : String) : Option (Entity.Field α) :=
  (Entity.fields (α := α)).find? fun f => Entity.fieldName f == s

/-- A `Ref β` (= `Id β`) column is a foreign key onto `β`'s table. -/
instance [Entity β] : RefTarget (Id β) := ⟨some (Entity.tableName β)⟩

/-- Declared indexes for an entity (LDB-03). The low-priority default is
    empty; a more specific `instance : Indexes α` wins. -/
class Indexes (α : Type) where
  indexes : Array IndexSpec

instance (priority := low) {α : Type} : Indexes α := ⟨#[]⟩

def Entity.spec (α : Type) [Entity α] [Indexes α] : TableSpec :=
  { name := Entity.tableName α, columns := Entity.columns α,
    indexes := Indexes.indexes α,
    invariant := (Entity.invariant (α := α)).map (·.1) }

/-- Every table an entity contributes: its own, then its child tables
    (LEP-0003 D) in field order. Child tables get `(parent, position)
    UNIQUE` automatically. -/
def Entity.specs (α : Type) [Entity α] [Indexes α] : List TableSpec :=
  let parent := Entity.spec α
  let kids := (Entity.children (α := α)).map fun l =>
    let ix : IndexSpec := { unique := true, columns := #["parent", "position"] }
    { l.spec with indexes :=
        if l.spec.indexes.any (fun i => i.columns == #["parent", "position"]) then
          l.spec.indexes
        else l.spec.indexes.push ix }
  parent :: kids

/-- The generated child entity's name for a parent's child-list field:
    `Kernel.Ins` for `Kernel.ins` — the field capitalized, because the
    field's own name is its projection function. Shared by the derive
    (which declares it) and the plan tactic (which resolves `k.val.ins.all
    …` to it). -/
def childTypeName (parent field : Lean.Name) : Lean.Name :=
  match field with
  | .str _ s => parent ++ Lean.Name.mkSimple s.capitalize
  | _ => parent ++ field

/-- The `Inline.decode` failure of a child record, as the child table's
    typed error: `"<sub>: <message>"` names the column `<sub>`, anything
    else the whole row (`"*"`). -/
def childDecodeError (table : String) (msg : String) : DbError :=
  match msg.splitOn ": " with
  | sub :: rest@(_ :: _) =>
      let sub := if sub.isEmpty then "*" else sub
      .decode table sub (String.intercalate ": " rest)
  | _ => .decode table "*" msg

/-- A column value as a SQL literal (for `DEFAULT` clauses). REAL values
    render exactly (`renderRealExact`): `toString` would print six decimals
    and silently record a different default. A non-finite REAL has no SQL
    literal — `validateSchema` refuses it before any DDL is built, so
    meeting one here is a caller bug; panic rather than emit invalid SQL. -/
def Col.sqlLit : Col → String
  | .int v => toString v
  | .real v =>
      match renderRealExact v with
      | .ok s => s
      | .error msg => panic! msg
  | .text v => "'" ++ (v.replace "'" "''") ++ "'"
  | .null => "NULL"

/-- Quote a SQLite identifier, including embedded double quotes. Entity
    and field names normally come from Lean identifiers, but escaped Lean
    names can contain punctuation and must remain valid SQL. -/
def quoteIdent (s : String) : String :=
  "\"" ++ s.replace "\"" "\"\"" ++ "\""

/-- One column's DDL fragment (shared by CREATE TABLE and ALTER ADD). -/
def ColumnSpec.ddlFragment (c : ColumnSpec) : String :=
  let base := s!"{quoteIdent c.name} {c.sqlType.render}"
  let base := if c.nullable then base else base ++ " NOT NULL"
  let base := match c.dflt with
    | some v => base ++ s!" DEFAULT {v.sqlLit}"
    | none => base
  let base := match c.enum with
    | some vs =>
        let names := String.intercalate ", " (vs.toList.map fun v => (Col.text v).sqlLit)
        base ++ s!" CHECK ({quoteIdent c.name} IN ({names}))"
    | none => base
  -- an EnumSet column: no bit outside the world (`~mask` is the literal, so
  -- growing the world changes the DDL and thus the fingerprint)
  let base := match c.enumSet with
    | some vs => base ++ s!" CHECK (({quoteIdent c.name} & ~{enumSetMask vs.size}) = 0)"
    | none => base
  match c.fkTable with
  | some fk =>
      let onDelete := if c.cascade then "CASCADE" else "RESTRICT"
      base ++ s!" REFERENCES {quoteIdent fk}(id) ON DELETE {onDelete} ON UPDATE RESTRICT"
  | none => base

/-- CREATE TABLE DDL under an explicit table name (migration rebuilds
    create under a scratch name, then rename). -/
def TableSpec.ddlNamed (t : TableSpec) (name : String) (ifNotExists : Bool := true) : String :=
  let cols := t.columns.toList.map ColumnSpec.ddlFragment
  let body := String.intercalate ", " ("id INTEGER PRIMARY KEY AUTOINCREMENT" :: cols)
  let guard := if ifNotExists then " IF NOT EXISTS" else ""
  s!"CREATE TABLE{guard} {quoteIdent name} ({body})"

/-- Rendered DDL for one entity. Every table gets a rowid-backed `id`
    primary key; references RESTRICT on delete — destruction is loud —
    except a child table's `parent` (LEP-0003 D), which CASCADEs: its rows
    are part of the parent's value. -/
def TableSpec.ddl (t : TableSpec) : String := t.ddlNamed t.name

/-- `CREATE [UNIQUE] INDEX` statements for this table's declared indexes.
    `ix.collate` (LDB-14) appends `COLLATE <k>` to every column — a
    `NOCASE` index is what lets SQLite use a pushed `prefix`
    (`LIKE 'x%' ESCAPE '\'`) as an index range. -/
def TableSpec.indexDdl (t : TableSpec) : Array String :=
  t.indexes.map fun ix =>
    let col (c : String) : String :=
      quoteIdent c ++
        match ix.collate with
        | some k => s!" COLLATE {k.toSql}"
        | none => ""
    let cols := String.intercalate ", " (ix.columns.toList.map col)
    let kind := if ix.unique then "UNIQUE INDEX" else "INDEX"
    let where? := match ix.partialWhere with
      | some w => s!" WHERE {w}"
      | none => ""
    s!"CREATE {kind} IF NOT EXISTS {quoteIdent (ix.resolvedName t.name)} ON {quoteIdent t.name} ({cols}){where?}"

/-- Table DDL plus every index, joined for fingerprinting. -/
def TableSpec.fullDdl (t : TableSpec) : String :=
  String.intercalate ";\n" (t.ddl :: t.indexDdl.toList)

/-- Two table names collide: same spelling, or the same letters ignoring
    case (SQLite's default folding, and `tableNameOf`'s snake_case). -/
private def namesCollide (a b : String) : Bool :=
  a == b || a.toLower == b.toLower

/-- A later spec that shares a name with an earlier one but is not the
    same table — the silent-dedup case (`UserProfile` vs `userProfile`,
    or a user entity claiming a child-table name). Equal repeats (parent
    listed with its own child `CliTable`) are not a collision. -/
def collidingTable? (specs : List TableSpec) : Option (String × String) := Id.run do
  let mut seen : List TableSpec := []
  for s in specs do
    if let some prev := seen.find? (fun p => namesCollide p.name s.name) then
      unless prev == s do
        return some (prev.name, s.name)
    else
      seen := s :: seen
  return none

/-- Validate cross-table invariants that individual derived `Entity`
    instances cannot see. This runs before opening or migrating a file. -/
def validateSchema (specs : List TableSpec) : Except DbError Unit := do
  if let some (a, b) := collidingTable? specs then
    throw (.schemaInvalid s!"table {String.quote b} collides with {String.quote a} \
(duplicate or case-folded name); the second entity would have been silently dropped")
  let tableNames := specs.map (·.name)
  unless tableNames.eraseDups.length == tableNames.length do
    throw (.schemaInvalid "table names must be unique")
  for spec in specs do
    if spec.name.startsWith "_leandb_" then
      throw (.schemaInvalid s!"table {String.quote spec.name} uses the reserved _leandb_ prefix")
    let columnNames := spec.columns.toList.map (·.name)
    if columnNames.contains "id" then
      throw (.schemaInvalid s!"table {String.quote spec.name} declares reserved column \"id\"")
    unless columnNames.eraseDups.length == columnNames.length do
      throw (.schemaInvalid s!"table {String.quote spec.name} has duplicate column names")
    for col in spec.columns do
      if let some target := col.fkTable then
        unless tableNames.contains target do
          throw (.schemaInvalid s!"{spec.name}.{col.name} references missing table {String.quote target}")
      if let some (.real v) := col.dflt then
        unless v.isFinite do
          throw (.schemaInvalid s!"{spec.name}.{col.name}: REAL default is not finite \
(NaN and infinities have no exact SQL literal)")
      if let some vs := col.enumSet then
        if vs.size > EnumSet.maxVariants then
          throw (.schemaInvalid s!"{spec.name}.{col.name}: closed world has {vs.size} variants; \
EnumSet supports at most {EnumSet.maxVariants}")
    for ix in spec.indexes do
      if ix.columns.isEmpty then
        throw (.schemaInvalid s!"table {String.quote spec.name} declares an index with no columns")
      for col in ix.columns do
        unless col == "id" || columnNames.contains col do
          throw (.schemaInvalid s!"table {String.quote spec.name}: index {ix.resolvedName spec.name} \
names unknown column {String.quote col}")

/-- Schema fingerprint: a hash of the rendered DDL of every table, in
    declaration order, followed by the declared shape of every JSON
    column (`table.column=shape`, one per line) and the variant list of
    every `EnumSet` column (`table.column=<a|b|c>` — the DDL sees only
    the mask, and a renamed or reordered variant changes what a stored
    bit *means*), then the name of every declared invariant
    (`table:invariant=<name>`, LDB-16). A schema with none of these hashes
    exactly its DDL, as it always has. Checked against `_leandb_meta` at open. -/
def fingerprint (specs : List TableSpec) : String :=
  let ddl := String.intercalate ";\n" (specs.map (·.fullDdl))
  let shapes := specs.flatMap fun t => t.columns.toList.filterMap fun c =>
    (c.shape.map fun s => s!"{t.name}.{c.name}={s}") <|>
      (c.enumSet.map fun vs => s!"{t.name}.{c.name}={JsonShape.closed vs}")
  let shapes := shapes ++ specs.filterMap fun t => t.invariant.map fun n => s!"{t.name}:invariant={n}"
  toString <| hash <| if shapes.isEmpty then ddl else ddl ++ "\n" ++ String.intercalate "\n" shapes

end LeanDb
