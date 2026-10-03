import LeanDb.Migration
import LeanDb.Typed.Schema
import LeanDb.Typed.Constraint

/-! # Schema changes wait for a migration (DDD-LDB-07)

An app opens its database through the gate. The gate compares the compiled
schema's fingerprint with the one the database records. Equal: nothing to
do. Different: every difference must be one LeanDB can make without
inventing data (a new table, an optional or defaulted column, a grown closed
world, a new non-unique index), or one a *declared migration* covers. A
migration is an ordinary Lean value,

```lean
def addShipping := SchemaMigration.addField Order Order.Field.shipping (fill := .standard)
```

or, with the `T.addField` spelling and recorded under its own name,

```lean
migration% addShipping := Order.addField shipping (fill := .standard)
```

`fill` has the field's type; the compiler checks it. Anything else (a new
required field nobody fills, a dropped or retyped field) refuses, naming
every table and field, and changes nothing. Adding a unique constraint runs
a preflight first: every group of existing rows that would collide is
reported, no survivor is picked, and nothing is applied. A covered change is
applied in one transaction by the existing engine (`Migration.applyOn`),
journaled in `_leandb_migrations`, and each declared migration it used is
recorded by name in `_leandb_applied_migrations`.

`Gate.command?` gives an app executable `migrate --check` and `migrate`.
-/

namespace LeanDb

open Lean (Json)

/-- The last component of a Lean name (`Shop.Order` ↦ `Order`), for
    messages. -/
def shortTypeName (full : String) : String :=
  match (full.splitOn ".").getLast? with
  | some last => if last.isEmpty then full else last
  | none => full

/-- One declared change. Build these with the typed constructors below; the
    data form exists so one list can hold migrations of different entities. -/
inductive SchemaMigration.Change where
  /-- Existing rows of `table` take `fill` in the new column `column`. -/
  | addField (table column entity : String) (fill : Col)
  /-- A read-only preflight over one stored column: one line per refused
      row or group of rows; empty means the data passes. -/
  | preflight (table column entity : String) (describe : String)
      (check : List (Int64 × Col) → List String)

/-- A declared schema migration: a name and what it does. -/
structure SchemaMigration where
  name : String
  changes : List SchemaMigration.Change

namespace SchemaMigration

/-- Existing rows get `fill` in the new field. `fill` has the field's own
    type, so a wrong value is a compile error, and it is stored through the
    field's codec, exactly as an insert would store it. The entity is
    explicit so the field's type is known while `fill` elaborates
    (`(fill := .everyone)` resolves against it). -/
def addField (α : Type) [Entity α] (field : Entity.Field α) (fill : Entity.fieldTy field) :
    SchemaMigration :=
  let column := Entity.fieldName field
  let entity := shortTypeName (Entity.typeName α)
  { name := s!"{entity}.addField {column}"
    changes := [.addField (Entity.tableName α) column entity (@toCol _ (Entity.codec field) fill)] }

/-- Before a canonicalizing unique constraint is added: run the shared
    canonicalization preflight (`canonicalizationPreflight`, the same parser
    the codec uses) over the stored values. Every invalid row and every group
    of rows that collapse to one canonical key is reported; none is chosen. -/
def checkCanonical (α : Type) [Entity α] (field : Entity.Field α) {κ : Type} [BEq κ]
    (parse : String → Except String κ) : SchemaMigration :=
  let column := Entity.fieldName field
  let entity := shortTypeName (Entity.typeName α)
  let check : List (Int64 × Col) → List String := fun rows =>
    let texts := rows.filterMap fun (id, c) => match c with
      | .text v => some (id, v)
      | _ => none
    let raw : Int64 → String := fun id => (texts.lookup id).getD "?"
    let nonText := rows.filterMap fun (id, c) => match c with
      | .text _ | .null => none
      | other => some s!"row {id}: stored {other.describe}, not text"
    let report := canonicalizationPreflight parse texts
    nonText ++
      report.invalid.map (fun (id, why) => s!"row {id}: {String.quote (raw id)} is invalid: {why}") ++
      report.conflicts.map fun group =>
        s!"rows {group.rows} collide after canonicalization: \
{String.intercalate ", " (group.rows.map fun id => String.quote (raw id))}"
  { name := s!"{entity}.checkCanonical {column}"
    changes := [.preflight (Entity.tableName α) column entity s!"canonical {entity}.{column}" check] }

end SchemaMigration

/-- `migration% addShipping := Order.addField shipping (fill := .standard)`
    declares `def addShipping : SchemaMigration`, recorded under its own
    name. `T.addField f (fill := v)` and `T.checkCanonical f parse` name the
    field by name (no `T.addField` constant is generated; when the
    author has defined one, it is used as written). Any other right-hand
    side is an ordinary `SchemaMigration` term. -/
syntax (name := migrationCmd) (Lean.Parser.Command.docComment)? "migration% " ident " := " term : command

open Lean Elab Command Meta in
private def migrationField (entityIdent : Ident) (field : Ident) : CommandElabM (Ident × Ident) := do
  let entity ← liftTermElabM <| realizeGlobalConstNoOverloadWithInfo entityIdent
  let symbols ← liftTermElabM do
    let ty := mkConst entity
    let inst ← synthInstance (mkApp (mkConst ``LeanDb.Entity) ty)
    let .const symbols _ ← whnf (mkApp2 (mkConst ``LeanDb.Entity.Field) ty inst)
      | throwError "migration%: {entity} has no declared field symbols"
    pure symbols
  let symbol := symbols ++ field.getId
  unless (← getEnv).contains symbol do
    throwErrorAt field "migration%: {entity} has no stored field '{field.getId}'"
  return (mkIdent (`_root_ ++ entity), mkIdent (`_root_ ++ symbol))

open Lean Elab Command in
@[command_elab migrationCmd]
def elabMigration : CommandElab := fun stx => do
  let `($[$doc?:docComment]? migration% $name:ident := $rhs) := stx | throwUnsupportedSyntax
  let isSugar (fn : Ident) (verb : String) : CommandElabM Bool := do
    let n := fn.getId
    if n.isAnonymous || n.getPrefix.isAnonymous then return false
    unless n.getString! == verb do return false
    -- An author-defined `T.addField` is an ordinary function call.
    let resolved ← liftTermElabM do
      try return some (← realizeGlobalConstNoOverloadWithInfo fn) catch _ => return none
    return resolved.isNone
  let body ← match rhs with
    | `($fn:ident $field:ident (fill := $fill)) =>
        if ← isSugar fn "addField" then
          let (entity, symbol) ← migrationField (mkIdent fn.getId.getPrefix) field
          `(LeanDb.SchemaMigration.addField $entity $symbol (fill := $fill))
        else pure rhs
    | `($fn:ident $field:ident $parse:term) =>
        if ← isSugar fn "checkCanonical" then
          let (entity, symbol) ← migrationField (mkIdent fn.getId.getPrefix) field
          `(LeanDb.SchemaMigration.checkCanonical $entity $symbol $parse)
        else pure rhs
    | _ => pure rhs
  let label : Term := ⟨Syntax.mkStrLit name.getId.toString⟩
  elabCommand (← `($[$doc?:docComment]? def $name : LeanDb.SchemaMigration :=
      { ($body : LeanDb.SchemaMigration) with name := $label }))

namespace Gate

/-- What the gate knows about the code's schema. -/
structure Target where
  specs : List TableSpec
  /-- The entity a table stores, for messages (`order` ↦ `Order`). -/
  entityOf : String → Option String := fun _ => none

/-- The schema `s`, with entity names taken from its packed entities. -/
def Target.ofSchema (s : Type) [i : IsSchema s] : Target where
  specs := IsSchema.specs s
  entityOf := fun table => i.tables.toList.findSome? fun t =>
    let p := i.pack t
    if @Entity.tableName p.ty p.entity == table then
      some (shortTypeName (@Entity.typeName p.ty p.entity))
    else none

def Target.entity (target : Target) (table : String) : String :=
  (target.entityOf table).getD table

/-- Existing rows that share one key of a new unique constraint. -/
structure DuplicateGroup where
  key : List (String × Col)
  rows : List Int64
  deriving Repr

/-- Why the gate refuses. -/
inductive Finding where
  /-- A new required field with no default that no declared migration fills. -/
  | missingFill (entity table column : String)
  /-- A difference the gate never makes on its own (data would be dropped
      or reinterpreted). -/
  | unsupported (subject : String) (why : String)
  /-- Existing rows that would collide under a new unique constraint. -/
  | duplicates (entity table index : String) (columns : Array String) (groups : List DuplicateGroup)
  /-- A declared preflight refused rows. -/
  | preflight (migration subject : String) (problems : List String)
  /-- The database's own schema record cannot be read. -/
  | unreadable (why : String)
  deriving Inhabited

private def renderKey (key : List (String × Col)) : String :=
  String.intercalate ", " (key.map fun (c, v) => s!"{c} = {v.sqlLit}")

def Finding.render : Finding → String
  | .missingFill entity table column =>
      s!"{entity}.{column} (table \"{table}\", column \"{column}\"): new required field with no \
default, and existing rows have no value for it. Declare a migration that fills it, e.g.\n      \
migration% add_{column} := {entity}.addField {column} (fill := …)"
  | .unsupported subject why => s!"{subject}: {why}"
  | .duplicates entity table index columns groups =>
      let n := groups.foldl (init := 0) fun n g => n + g.rows.length
      let header := s!"{entity} unique ({String.intercalate ", " columns.toList}), index \"{index}\" on \
table \"{table}\": {n} existing rows in {groups.length} group(s) share a key. No row is picked \
as a survivor; resolve them, then start again."
      String.intercalate "\n      " (header :: groups.map fun g =>
        s!"{renderKey g.key}: rows {String.intercalate ", " (g.rows.map toString)}")
  | .preflight migration subject problems =>
      String.intercalate "\n      "
        (s!"{subject} (migration {migration}): the preflight refused {problems.length} row(s) or group(s):" ::
          problems)
  | .unreadable why => s!"the database's schema record is unreadable: {why}"

/-- A covered change, ready to apply. -/
structure Plan where
  storedFingerprint : String
  fingerprint : String
  fromVersion : Nat
  /-- The schema the database is at. -/
  old : List TableSpec
  /-- Declared migrations this change uses, by name. -/
  migrations : List String
  /-- Tables rewritten by declared fills: column ↦ fill. -/
  fills : List (String × List (String × Col))
  /-- What will be applied, readable. -/
  steps : List String
  notes : List String
  /-- Preflights that ran and passed. -/
  checked : List String

inductive Status where
  /-- No schema recorded yet; `Conn.verify` creates the tables. -/
  | fresh
  | upToDate
  | pending (plan : Plan)
  | refused (findings : List Finding)

def Status.render : Status → String
  | .fresh => "status: fresh — the database records no schema yet; the tables will be created."
  | .upToDate => "status: up to date — the database is at the compiled schema."
  | .pending plan =>
      String.intercalate "\n" <|
        s!"status: pending — the schema changed and every difference is covered (version {plan.fromVersion} → {plan.fromVersion + 1}):" ::
        (plan.steps.map ("  apply: " ++ ·) ++ plan.checked.map ("  checked: " ++ ·) ++
          plan.notes.map ("  note: " ++ ·))
  | .refused findings =>
      String.intercalate "\n" <|
        s!"status: refused — LeanDB will not open this database until a migration covers these \
changes. Nothing was changed." :: findings.map ("  - " ++ ·.render)

/-- What `apply` did. -/
inductive Outcome where
  | fresh
  | upToDate
  | applied (plan : Plan) (report : MigrateReport)

def Outcome.render : Outcome → String
  | .fresh => Status.render .fresh
  | .upToDate => Status.render .upToDate
  | .applied plan report =>
      String.intercalate "\n" <|
        s!"status: migrated — version {plan.fromVersion} → {plan.fromVersion + 1}:" ::
        report.applied.map ("  applied: " ++ ·)

structure Options where
  /-- Run the duplicate and declared preflights. Always on in production.
      Off, the database's own index build still refuses a duplicate inside
      the migration transaction; tests use that to check atomicity. -/
  preflight : Bool := true
  /-- A full backup before applying (`VACUUM INTO`), as `migrate` takes. -/
  backup : Option System.FilePath := none

/-! ## Classifying the difference -/

private def fillFor (migrations : List SchemaMigration) (table column : String) :
    Option (Col × String) :=
  migrations.findSome? fun m => m.changes.findSome? fun
    | .addField t c _ fill => if t == table && c == column then some (fill, m.name) else none
    | .preflight .. => none

/-- Why a same-named column's change is not one the gate makes on its own,
    or `none` when copying the stored values is exact: a grown closed world,
    a changed default or delete action, optional-ization. -/
private def unsafeChange (old new : ColumnSpec) : Option String :=
  let problems : List String :=
    (if old.sqlType != new.sqlType then
      [s!"type {old.sqlType.render} → {new.sqlType.render}"] else []) ++
    (if old.fkTable != new.fkTable then
      [s!"reference {old.fkTable.getD "none"} → {new.fkTable.getD "none"}"] else []) ++
    (if old.nullable && !new.nullable then ["optional → required"] else []) ++
    (match old.enum, new.enum with
      | some a, some b =>
          let lost := a.toList.filter (!b.contains ·)
          if lost.isEmpty then [] else [s!"closed world loses {lost}"]
      | none, some _ => ["now a closed world; stored values are unchecked"]
      | _, _ => []) ++
    (match old.enumSet, new.enumSet with
      | some a, some b =>
          let common := min a.size b.size
          if a.extract 0 common == b.extract 0 common then []
          else [s!"EnumSet variant order {a} → {b}"]
      | none, some _ => ["now an EnumSet"]
      | some _, none => ["no longer an EnumSet"]
      | none, none => [])
  if problems.isEmpty then none else some (String.intercalate ", " problems)

private structure Diff where
  findings : Array Finding := #[]
  fills : Array (String × List (String × Col)) := #[]
  used : Array String := #[]
  /-- New unique indexes on tables the database already has. -/
  uniques : Array (TableSpec × TableSpec × IndexSpec) := #[]

private def classify (target : Target) (old new : List TableSpec)
    (migrations : List SchemaMigration) : Diff := Id.run do
  let mut d : Diff := {}
  for spec in new do
    let some o := old.find? (·.name == spec.name) | continue
    let entity := target.entity spec.name
    let mut tableFills : List (String × Col) := []
    for c in spec.columns do
      match o.columns.find? (·.name == c.name) with
      | none =>
          match fillFor migrations spec.name c.name with
          | some (fill, m) =>
              tableFills := tableFills ++ [(c.name, fill)]
              unless d.used.contains m do d := { d with used := d.used.push m }
          | none =>
              unless c.nullable || c.dflt.isSome do
                d := { d with findings := d.findings.push (.missingFill entity spec.name c.name) }
      | some oc =>
          if let some why := unsafeChange oc c then
            d := { d with findings := d.findings.push (.unsupported s!"{entity}.{c.name} \
(table \"{spec.name}\")" s!"field changed ({why}); the gate does not reinterpret stored values. \
Migrate by hand (`leandb migrate`)") }
    for oc in o.columns do
      unless spec.columns.any (·.name == oc.name) do
        d := { d with findings := d.findings.push (.unsupported s!"{entity}.{oc.name} \
(table \"{spec.name}\")" "field removed; the gate never drops stored data. Migrate by hand \
(`leandb migrate apply --allow-destructive`)") }
    unless tableFills.isEmpty do
      d := { d with fills := d.fills.push (spec.name, tableFills) }
    for ix in spec.indexes do
      if ix.unique && !(o.indexes.any (· == ix)) then
        d := { d with uniques := d.uniques.push (o, spec, ix) }
  for o in old do
    unless new.any (·.name == o.name) do
      d := { d with findings := d.findings.push (.unsupported s!"{target.entity o.name} (table \"{o.name}\")"
        "table removed; the gate never drops stored data. Migrate by hand") }
  return d

/-! ## Preflights (read-only) -/

/-- Every group of rows that would collide under unique index `ix` once the
    change is applied: stored values for existing columns, the declared fill
    (or the default, or NULL) for added ones. NULL never collides, exactly as
    in a SQLite unique index; the index's collation and partial `WHERE` are
    honoured. `none` when a key column has no value yet (already a finding). -/
private def duplicateGroups (db : SQLite) (old new : TableSpec) (ix : IndexSpec)
    (fills : List (String × Col)) : IO (Option (List DuplicateGroup)) := do
  let mut exprs : Array String := #[]
  for col in ix.columns do
    if col == "id" || old.columns.any (·.name == col) then
      exprs := exprs.push (quoteIdent col)
    else
      match fills.lookup col, new.columns.find? (·.name == col) with
      | some fill, _ => exprs := exprs.push fill.sqlLit
      | none, some c =>
          match c.dflt with
          | some d => exprs := exprs.push d.sqlLit
          | none => if c.nullable then exprs := exprs.push "NULL" else return none
      | none, none => return none
  let keys := (List.range exprs.size).map fun i => s!"k{i}"
  let inner := String.intercalate ", " ("id" :: (exprs.toList.zip keys).map fun (e, k) => s!"{e} AS {k}")
  let partial? := match ix.partialWhere with
    | some w => s!" WHERE {w}"
    | none => ""
  let collate := match ix.collate with
    | some k => s!" COLLATE {k.toSql}"
    | none => ""
  let notNull := String.intercalate " AND " (keys.map (· ++ " IS NOT NULL"))
  let partition := String.intercalate ", " (keys.map (· ++ collate))
  let sql := s!"SELECT id, g, {String.intercalate ", " keys} FROM (\
SELECT id, {String.intercalate ", " keys}, COUNT(*) OVER w AS n, MIN(id) OVER w AS g FROM (\
SELECT {inner} FROM {quoteIdent old.name}{partial?}) WHERE {notNull} WINDOW w AS (PARTITION BY {partition})\
) WHERE n > 1 ORDER BY g, id"
  let stmt ← db.prepare sql
  let mut groups : Array (Int64 × DuplicateGroup) := #[]
  repeat
    if ← stmt.step then
      let id ← stmt.columnInt64 0
      let g ← stmt.columnInt64 1
      let mut key : List (String × Col) := []
      for i in [0:exprs.size] do
        let v := (← readCol stmt (Int32.ofNat (i + 2))).getD .null
        key := key ++ [(ix.columns[i]!, v)]
      match groups.back? with
      | some (g', group) =>
          if g' == g then
            groups := groups.pop.push (g, { group with rows := group.rows ++ [id] })
          else groups := groups.push (g, { key, rows := [id] })
      | none => groups := groups.push (g, { key, rows := [id] })
    else break
  return some (groups.toList.map (·.2))

private def readColumn (db : SQLite) (table column : String) : IO (List (Int64 × Col)) := do
  let stmt ← db.prepare s!"SELECT id, {quoteIdent column} FROM {quoteIdent table} ORDER BY id"
  let mut out : Array (Int64 × Col) := #[]
  repeat
    if ← stmt.step then
      out := out.push (← stmt.columnInt64 0, (← readCol stmt 1).getD .null)
    else break
  return out.toList

/-! ## Check and apply -/

/-- Read-only: what opening this database with `target` would do. -/
def check (conn : Conn) (target : Target) (migrations : List SchemaMigration)
    (opts : Options := {}) : IO (Except DbError Status) := do
  if let .error e := validateSchema target.specs then return .error e
  try
    let db := conn.raw
    let some stored ← readMeta db "schema_fingerprint" | return .ok .fresh
    let fp := fingerprint target.specs
    if stored == fp then return .ok .upToDate
    let old ← match ← readStoredSchemaChecked conn with
      | .ok (some old) => pure old
      | .ok none => return .ok (.refused [.unreadable "a fingerprint is recorded but no schema"])
      | .error why => return .ok (.refused [.unreadable why])
    let fromVersion := ((← readMeta db "schema_version").bind (·.toNat?)).getD 1
    let d := classify target old target.specs migrations
    let mut findings := d.findings
    let mut checked : Array String := #[]
    let mut used := d.used
    if opts.preflight then
      for (o, spec, ix) in d.uniques do
        let fills := (d.fills.toList.lookup spec.name).getD []
        let entity := target.entity spec.name
        let index := ix.resolvedName spec.name
        try
          match ← duplicateGroups db o spec ix fills with
          | none => pure ()
          | some [] =>
              checked := checked.push s!"{entity} unique ({String.intercalate ", " ix.columns.toList}) \
\"{index}\": no existing rows collide"
          | some groups =>
              findings := findings.push (.duplicates entity spec.name index ix.columns groups)
        catch e =>
          findings := findings.push (.unsupported s!"{entity} unique \"{index}\""
            s!"cannot preflight the new constraint: {e}")
      for m in migrations do
        for change in m.changes do
          if let .preflight table column entity describe run := change then
            -- Only data the database already has can be checked; a column
            -- that is new holds one fill for every row.
            let some o := old.find? (·.name == table) | continue
            unless o.columns.any (·.name == column) do continue
            let problems := run (← readColumn db table column)
            unless used.contains m.name do used := used.push m.name
            if problems.isEmpty then
              checked := checked.push s!"{describe} (migration {m.name}): every stored row passes"
            else
              findings := findings.push (.preflight m.name s!"{entity}.{column}" problems)
    unless findings.isEmpty do return .ok (.refused findings.toList)
    -- Every difference is covered. The existing engine plans the rest.
    match planMigration old target.specs (d.fills.toList.map (·.1)) with
    | .error why => return .ok (.refused [.unsupported "schema" why])
    | .ok plan =>
        let fillSteps := d.fills.toList.flatMap fun (table, cols) =>
          cols.map fun (col, fill) =>
            s!"{target.entity table}.{col} := {fill.sqlLit} for every existing row of \"{table}\""
        let mechanical := plan.steps.filterMap fun step =>
          match step with
          | .rebuildTable spec _ => if d.fills.any (·.1 == spec.name) then none else some step.describe
          | _ => some step.describe
        return .ok (.pending {
          storedFingerprint := stored, fingerprint := fp, fromVersion, old
          migrations := used.toList, fills := d.fills.toList
          steps := fillSteps ++ mechanical
          notes := plan.notes
          checked := checked.toList })
  catch e =>
    return .error (.sqlite (toString e))

/-- The bookkeeping table of declared migrations, by name. -/
def appliedDdl : String :=
  "CREATE TABLE IF NOT EXISTS _leandb_applied_migrations (idx INTEGER PRIMARY KEY AUTOINCREMENT, \
name TEXT NOT NULL, from_fingerprint TEXT NOT NULL, to_fingerprint TEXT NOT NULL, \
from_version INTEGER NOT NULL, to_version INTEGER NOT NULL, applied_at INTEGER NOT NULL)"

/-- Declared migrations recorded as applied, oldest first. -/
def appliedMigrations (conn : Conn) : IO (List String) := do
  conn.raw.exec appliedDdl
  let stmt ← conn.raw.prepare "SELECT name FROM _leandb_applied_migrations ORDER BY idx"
  let mut out : Array String := #[]
  repeat
    if ← stmt.step then out := out.push (← stmt.columnText 0) else break
  return out.toList

/-- Rewrite a covered table: carry stored columns by name, take declared
    fills for new ones, then defaults, then NULL for optional ones. -/
private def fillStep (target : Target) (table : String) (fills : List (String × Col)) : Step :=
  .transform table
    s!"fill {String.intercalate ", " (fills.map fun (c, v) => s!"{target.entity table}.{c} := {v.sqlLit}")}"
    fun old new cols => do
      let get : String → Option Col := fun n => do
        let i ← old.columns.findIdx? (·.name == n)
        cols[i]?
      let out ← new.columns.toList.mapM fun c =>
        match fills.lookup c.name with
        | some v => Except.ok v
        | none =>
            match get c.name with
            | some v => Except.ok v
            | none =>
                match c.dflt with
                | some v => Except.ok v
                | none =>
                    if c.nullable then Except.ok .null
                    else Except.error s!"column \"{c.name}\" has no stored value and no fill"
      return out.toArray

/-- Apply what `check` found, atomically: every rewrite, index and journal
    entry commits together or not at all. Refusal is an error naming every
    finding; nothing is changed. -/
def apply (conn : Conn) (target : Target) (migrations : List SchemaMigration)
    (opts : Options := {}) : IO (Except DbError Outcome) := do
  match ← check conn target migrations opts with
  | .error e => return .error e
  | .ok .fresh => return .ok .fresh
  | .ok .upToDate => return .ok .upToDate
  | .ok (status@(.refused _)) => return .error (.migrate status.render)
  | .ok (.pending plan) =>
      let toVersion := plan.fromVersion + 1
      let record : Step := .custom s!"record {plan.migrations}" fun c => do
        c.raw.exec appliedDdl
        let now ← unixNow c
        for name in plan.migrations do
          let stmt ← c.raw.prepare "INSERT INTO _leandb_applied_migrations \
(name, from_fingerprint, to_fingerprint, from_version, to_version, applied_at) VALUES (?, ?, ?, ?, ?, ?)"
          stmt.bindText 1 name
          stmt.bindText 2 plan.storedFingerprint
          stmt.bindText 3 plan.fingerprint
          stmt.bindInt64 4 (Int64.ofNat plan.fromVersion)
          stmt.bindInt64 5 (Int64.ofNat toVersion)
          stmt.bindInt64 6 (Int64.ofNat now)
          stmt.exec
      let migration : Migration := {
        fromFingerprint := plan.storedFingerprint
        toFingerprint := plan.fingerprint
        snapshot := target.specs
        steps := plan.fills.map (fun (table, fills) => fillStep target table fills) ++
          (if plan.migrations.isEmpty then [] else [record])
        note := String.intercalate ", " plan.migrations }
      match ← Migration.applyOn conn plan.old migration toVersion (allowDestructive := false) opts.backup with
      | .error e => return .error e
      | .ok report => return .ok (.applied plan report)

/-- Open the database at `path` for `target`: gate it (applying a covered
    change), then `Conn.verify`. A refused change is an error that names every
    table and field; the file is left as it was. -/
def openDb (path : System.FilePath) (target : Target) (migrations : List SchemaMigration)
    (opts : Options := {}) : IO (Except DbError (Conn × Outcome)) := do
  match ← openDbRaw path with
  | .error e => return .error e
  | .ok conn =>
      match ← apply conn target migrations opts with
      | .error e => return .error e
      | .ok outcome =>
          match ← conn.verify target.specs with
          | .error e => return .error e
          | .ok () => return .ok (conn, outcome)

/-- For an app that opens its own connections afterwards (e.g. a server's
    writer and readers): gate the file once, then let it open as usual. -/
def ensure (path : System.FilePath) (target : Target) (migrations : List SchemaMigration)
    (opts : Options := {}) : IO (Except DbError Outcome) := do
  match ← openDb path target migrations opts with
  | .error e => return .error e
  | .ok (_, outcome) => return .ok outcome

/-- Exit code of a refused change (`migrate --check`, `migrate`, startup). -/
def refusedExit : UInt32 := 3

/-- The app executable's `migrate` commands; `none` for any other arguments.
    `migrate --check` is read-only: exit 0 when the app would start (up to
    date, fresh, or a covered change it will apply), `refusedExit` when it
    would refuse, 1 on any other error. `migrate` applies now. -/
def command? (path : System.FilePath) (target : Target) (migrations : List SchemaMigration)
    (args : List String) (opts : Options := {}) : IO (Option UInt32) := do
  match args with
  | ["migrate", "--check"] =>
      unless ← path.pathExists do
        IO.println (Status.render .fresh)
        return some 0
      match ← openDbRaw path (readOnly := true) with
      | .error e =>
          IO.eprintln s!"migrate --check: {e}"
          return some 1
      | .ok conn =>
          match ← check conn target migrations opts with
          | .error e =>
              IO.eprintln s!"migrate --check: {e}"
              return some 1
          | .ok status =>
              IO.println status.render
              return some (match status with
                | .refused _ => refusedExit
                | _ => 0)
  | ["migrate"] =>
      match ← ensure path target migrations opts with
      | .error (.migrate why) =>
          IO.eprintln why
          return some refusedExit
      | .error e =>
          IO.eprintln s!"migrate: {e}"
          return some 1
      | .ok outcome =>
          IO.println outcome.render
          return some 0
  | _ => return none

end Gate

end LeanDb
