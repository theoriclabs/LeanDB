import LeanDb.Db
import LeanDb.Json

namespace LeanDb

/-! # Migrations v1: additive auto-migration, loud destruction

The instance remembers the schema it was last shaped to (`schema_json` in
`_leandb_meta`). `planMigration` diffs that against the code's specs and
produces steps:

- new table → `CREATE TABLE`;
- new column → `ALTER TABLE ADD COLUMN` — the column must be nullable
  (`Option`), because existing rows need a value and v1 refuses to invent
  one (backfills are a judgment call, per plan.md §6);
- changed column (type, nullability, FK target, or a changed closed world)
  → table rebuild: create under a scratch name with the new DDL, copy the
  surviving columns, drop, rename. A *shrunk* closed world hits the new
  CHECK during the copy and aborts the transaction — vocabulary can only
  shrink through a migration, and only when the data already conforms;
- dropped column/table → destructive, refused unless explicitly allowed;
- a JSON column whose declared *shape* changed (LEP-0003 B2): additive
  with defaults (fields added, each with a default; constructors or
  variants added) → `restampShape`, a step with no SQL that exists so
  the change is journaled; anything else (a field removed or retyped, a
  constructor renamed or removed, a nested closed world shrunk) is
  refused by name — a typed value transformation is not yet available.

Everything applies in one transaction with a foreign-key check before
commit. `openDb` still refuses fingerprint drift; `migrate` is the one
explicit gate through which schemas move.
-/

inductive MigStep where
  | createTable (spec : TableSpec)
  | addColumn (table : String) (col : ColumnSpec)
  | dropColumn (table col : String)
  | dropTable (name : String)
  /-- Rebuild `spec.name` under the new spec, copying `copyCols`. -/
  | rebuildTable (spec : TableSpec) (copyCols : List String)
  | restampShape (table col : String)
  | addIndex (table : String) (ix : IndexSpec)
  | dropIndex (table : String) (ix : IndexSpec)
  /-- The declared invariant changed (LDB-16). No SQL: the check is Lean
      code, and every row is checked again when it is read. -/
  | restampInvariant (table : String) (old new : Option String)
  deriving Repr

def MigStep.describe : MigStep → String
  | .createTable spec => s!"create table \"{spec.name}\""
  | .addColumn t c => s!"add column \"{t}\".\"{c.name}\""
  | .dropColumn t c => s!"DROP column \"{t}\".\"{c}\""
  | .dropTable t => s!"DROP table \"{t}\""
  | .rebuildTable spec cols =>
      s!"rebuild table \"{spec.name}\" (copying {cols.length} columns)"
  | .restampShape t c => s!"restamp shape of \"{t}\".\"{c}\""
  | .addIndex t ix => s!"add index \"{ix.resolvedName t}\""
  | .dropIndex t ix => s!"drop index \"{ix.resolvedName t}\""
  | .restampInvariant t old new =>
      let render := fun (n : Option String) => n.getD "(none)"
      s!"invariant of \"{t}\": {render old} → {render new}"

def MigStep.destructive : MigStep → Bool
  | .dropColumn .. | .dropTable .. => true
  | _ => false

def MigStep.sql : MigStep → List String
  | .createTable spec => spec.ddl :: spec.indexDdl.toList
  | .addColumn t c => [s!"ALTER TABLE {quoteIdent t} ADD COLUMN {c.ddlFragment}"]
  | .dropColumn t c => [s!"ALTER TABLE {quoteIdent t} DROP COLUMN {quoteIdent c}"]
  | .dropTable t => [s!"DROP TABLE {quoteIdent t}"]
  | .rebuildTable spec copyCols =>
      let tmp := s!"_leandb_new_{spec.name}"
      let cols := String.intercalate ", " ("id" :: copyCols.map quoteIdent)
      [ spec.ddlNamed tmp (ifNotExists := false),
        s!"INSERT INTO {quoteIdent tmp} ({cols}) SELECT {cols} FROM {quoteIdent spec.name}",
        s!"DROP TABLE {quoteIdent spec.name}",
        s!"ALTER TABLE {quoteIdent tmp} RENAME TO {quoteIdent spec.name}" ]
      ++ spec.indexDdl.toList
  | .restampShape .. => []
  | .addIndex t ix =>
      ({ name := t, columns := #[], indexes := #[ix] } : TableSpec).indexDdl.toList
  | .dropIndex t ix => [s!"DROP INDEX IF EXISTS {quoteIdent (ix.resolvedName t)}"]
  | .restampInvariant .. => []

/-! ## Shapes

`JsonShape.shape` strings (grammar documented on the class) parsed back
into a tree, so two schemas' shapes can be *compared*, not just found
unequal. -/

/-- A parsed shape. An inductive constructor's payload is `(named, fields)`:
    a named record (object encoding), or positional (`named = false`, the
    field names empty; array encoding), or nothing (`fields = []`). -/
inductive Shape where
  | prim (name : String)
  | struct (name : String) (fields : List (String × Shape × Bool))
  | ind (name : String) (ctors : List (String × Bool × List (String × Shape)))
  | closed (variants : List String)
  | list (of : Shape)
  | option (of : Shape)
  | pair (a b : Shape)
  deriving Repr, Inhabited

/-- Back to the canonical string (diagnostics). -/
partial def Shape.render : Shape → String
  | .prim n => n
  | .struct n fs => JsonShape.struct n (fs.map fun (f, s, d) => (f, s.render, d))
  | .ind n cs => JsonShape.inductive' n (cs.map fun (c, named, fs) =>
      (c, if fs.isEmpty then .none
          else if named then .named (fs.map fun (f, s) => (f, s.render))
          else .positional (fs.map fun (_, s) => s.render)))
  | .closed vs => JsonShape.closed vs.toArray
  | .list s => JsonShape.list s.render
  | .option s => JsonShape.option s.render
  | .pair a b => JsonShape.pair a.render b.render

namespace Shape

private def isDelim (c : Char) : Bool :=
  c == '{' || c == '}' || c == '(' || c == ')' || c == '<' || c == '>' ||
  c == '[' || c == ']' || c == ',' || c == '|' || c == ':' || c == '?' || c == '='

private def takeName (cs : List Char) : Except String (String × List Char) :=
  let name := cs.takeWhile (!isDelim ·)
  if name.isEmpty then .error s!"expected a name at {String.ofList (cs.take 12)}"
  else .ok (String.ofList name, cs.drop name.length)

private def expect (c : Char) (cs : List Char) : Except String (List Char) :=
  match cs with
  | d :: rest => if d == c then .ok rest else .error s!"expected '{c}', found '{d}'"
  | [] => .error s!"expected '{c}', found end of shape"

private def suffix (s : Shape) : List Char → Shape × List Char
  | '?' :: r => suffix (.option s) r
  | r => (s, r)

private partial def variants (acc : List String) (r : List Char) :
    Except String (List String × List Char) := do
  let (v, r) ← takeName r
  match r with
  | '|' :: r => variants (acc ++ [v]) r
  | '>' :: r => return (acc ++ [v], r)
  | _ => throw "expected '|' or '>' in a closed world"

mutual
  private partial def parseShape (cs : List Char) : Except String (Shape × List Char) := do
    let (base, rest) ← parseAtom cs
    return suffix base rest

  private partial def parseAtom (cs : List Char) : Except String (Shape × List Char) := do
    match cs with
    | '[' :: r =>
        let (s, r) ← parseShape r
        return (.list s, ← expect ']' r)
    | '(' :: r =>
        let (a, r) ← parseShape r
        let r ← expect ',' r
        let (b, r) ← parseShape r
        return (.pair a b, ← expect ')' r)
    | '<' :: r =>
        let (vs, r) ← variants [] r
        return (.closed vs, r)
    | _ =>
        let (name, r) ← takeName cs
        match r with
        | '{' :: '}' :: r => return (.struct name [], r)
        | '{' :: r =>
            let (fs, r) ← parseFields '}' [] r
            return (.struct name fs, r)
        | '(' :: r =>
            let (cs, r) ← parseCtors [] r
            return (.ind name cs, r)
        | _ => return (.prim name, r)

  /-- `f:S=,g:S` up to `close`; the `Bool` is the `=` marker. -/
  private partial def parseFields (close : Char) (acc : List (String × Shape × Bool)) (cs : List Char) :
      Except String (List (String × Shape × Bool) × List Char) := do
    let (f, r) ← takeName cs
    let r ← expect ':' r
    let (s, r) ← parseShape r
    let (d, r) := match r with | '=' :: r => (true, r) | r => (false, r)
    let acc := acc ++ [(f, s, d)]
    match r with
    | ',' :: r => parseFields close acc r
    | c :: r => if c == close then return (acc, r) else throw s!"expected ',' or '{close}', found '{c}'"
    | [] => throw "unterminated field list"

  private partial def parsePositional (acc : List (String × Shape)) (r : List Char) :
      Except String (List (String × Shape) × List Char) := do
    let (s, r) ← parseShape r
    let acc := acc ++ [("", s)]
    match r with
    | ',' :: r => parsePositional acc r
    | ']' :: r => return (acc, r)
    | _ => throw "expected ',' or ']' in a positional payload"

  private partial def parseCtors (acc : List (String × Bool × List (String × Shape))) (cs : List Char) :
      Except String (List (String × Bool × List (String × Shape)) × List Char) := do
    let (c, r) ← takeName cs
    let (entry, r) ← match r with
      | '{' :: r => do
          let (fs, r) ← parseFields '}' [] r
          pure ((c, true, fs.map fun (f, s, _) => (f, s)), r)
      | '[' :: r => do
          let (fs, r) ← parsePositional [] r
          pure ((c, false, fs), r)
      | r => pure ((c, true, []), r)
    let acc := acc ++ [entry]
    match r with
    | '|' :: r => parseCtors acc r
    | ')' :: r => return (acc, r)
    | _ => throw "expected '|' or ')' after a constructor"
end

/-- Parse a `JsonShape` string. -/
def parse (s : String) : Except String Shape := do
  let (shape, rest) ← parseShape s.toList
  unless rest.isEmpty do throw s!"trailing input in shape: {String.ofList rest}"
  return shape

/-- Is `new` an *additive-with-defaults* change from `old` — every value
    encoded under `old` still decodes under `new`? `.ok` if so; otherwise
    the first change that breaks it, named. Type names of structures and
    inductives are informational (a rename changes no data); everything
    that changes an encoding is a refusal. -/
partial def additive (old new : Shape) : Except String Unit := do
  match old, new with
  | .prim a, .prim b =>
      unless a == b do throw s!"type changed from `{a}` to `{b}`"
  | .struct on ofs, .struct nn nfs =>
      for (f, os, _) in ofs do
        match nfs.find? (·.1 == f) with
        | none => throw s!"field `{f}` removed from `{on}`"
        | some (_, ns, _) => additive os ns |>.mapError fun m => s!"field `{f}` of `{on}`: {m}"
      for (f, _, d) in nfs do
        if (ofs.find? (·.1 == f)).isNone && !d then
          throw s!"field `{f}` added to `{nn}` without a default"
  | .ind on ocs, .ind _ ncs =>
      for (c, onamed, ofs) in ocs do
        match ncs.find? (·.1 == c) with
        | none => throw s!"constructor `{c}` renamed/removed from `{on}`"
        | some (_, nnamed, nfs) =>
            unless onamed == nnamed && ofs.length == nfs.length do
              throw s!"payload of constructor `{c}` of `{on}` changed"
            for ((of', os), (nf, ns)) in ofs.zip nfs do
              unless of' == nf do
                throw s!"payload field `{of'}` of constructor `{c}` of `{on}` renamed to `{nf}`"
              additive os ns |>.mapError fun m => s!"constructor `{c}` of `{on}`: {m}"
  | .closed ovs, .closed nvs =>
      for v in ovs do
        unless nvs.contains v do
          throw s!"variant `{v}` removed from the closed world {new.render}"
  | .list a, .list b => additive a b |>.mapError fun m => s!"list element: {m}"
  | .option a, .option b => additive a b
  | a, .option b => additive a b   -- a value of `a` is a value of `a?`
  | .pair a b, .pair c d =>
      additive a c |>.mapError fun m => s!"first of pair: {m}"
      additive b d |>.mapError fun m => s!"second of pair: {m}"
  | a, b => throw s!"type changed from `{a.render}` to `{b.render}`"

end Shape

/-- Classify one column's shape change: `.ok ()` means restamp. -/
private def shapeChange (table col : String) (old new : Option String) : Except String Unit := do
  match old, new with
  | some o, some n =>
      let os ← Shape.parse o |>.mapError fun m =>
        s!"table \"{table}\": stored shape of column \"{col}\" is unreadable: {m}"
      let ns ← Shape.parse n |>.mapError fun m =>
        s!"table \"{table}\": declared shape of column \"{col}\" is unreadable: {m}"
      Shape.additive os ns |>.mapError fun m =>
        s!"table \"{table}\": column \"{col}\" changed shape — {m}. Existing values \
would not decode under the new type; a typed value transformation is not yet available, \
so this migration is refused. Migrate by hand."
  | _, _ => pure ()   -- a shape declared (or dropped) where there was none: nothing to compare

structure MigPlan where
  steps : List MigStep := []
  notes : List String := []
  /-- Set by `migrate` from `destructiveAgainst` — step kinds alone miss
      rebuilds that drop columns. -/
  isDestructive : Bool := false
  deriving Repr

/-- Diff two schemas into a plan. Errors are refusals with reasons —
    never a silent guess. A table in `covered` has a declared typed
    transform (`LeanDb.Step`) that rewrites its rows: it is rebuilt
    without the refusals that exist because no value could be invented. -/
def planMigration (old new : List TableSpec) (covered : List String := []) :
    Except String MigPlan := do
  let mut steps : List MigStep := []
  let mut notes : List String := []
  -- new and changed tables
  for spec in new do
    match old.find? (·.name == spec.name) with
    | none => steps := steps ++ [.createTable spec]
    | some oldSpec =>
        if oldSpec == spec then continue
        if oldSpec.invariant != spec.invariant then
          steps := steps ++ [.restampInvariant spec.name oldSpec.invariant spec.invariant]
          if spec.invariant.isSome then
            notes := notes ++ [s!"\"{spec.name}\" declares invariant {spec.invariant.get!}: \
existing rows are checked when read, and a row that fails it is refused, not returned"]
          if { oldSpec with invariant := spec.invariant } == spec then continue
        if covered.contains spec.name then
          notes := notes ++ [s!"\"{spec.name}\" is rewritten by a typed transform"]
          steps := steps ++ [.rebuildTable spec (spec.columns.toList.filterMap fun c =>
            if (oldSpec.columns.find? (·.name == c.name)).isSome then some c.name else none)]
          continue
        let added := spec.columns.toList.filter fun c =>
          (oldSpec.columns.find? (·.name == c.name)).isNone
        let dropped := oldSpec.columns.toList.filter fun c =>
          (spec.columns.find? (·.name == c.name)).isNone
        -- shape changes: additive → restamp, anything else → refused by name
        let reshaped := spec.columns.toList.filter fun c =>
          match oldSpec.columns.find? (·.name == c.name) with
          | some o => o.shape != c.shape
          | none => false
        for c in reshaped do
          if let some o := oldSpec.columns.find? (·.name == c.name) then
            shapeChange spec.name c.name o.shape c.shape
        -- EnumSet worlds: bit k means variant k, so only a change that keeps
        -- every surviving variant at its bit — append, or truncate — is a
        -- migration of the data. Anything else silently re-labels stored
        -- bits; refused by name.
        for c in spec.columns do
          if let some o := oldSpec.columns.find? (·.name == c.name) then
            if let (some ovs, some nvs) := (o.enumSet, c.enumSet) then
              let common := min ovs.size nvs.size
              unless ovs.extract 0 common == nvs.extract 0 common do
                throw s!"table \"{spec.name}\": EnumSet column \"{c.name}\" changed its variant \
order ({ovs} → {nvs}) — stored bits would change meaning. Append or truncate \
variants only, or migrate by hand."
        -- DDL-level changes, the shape aside
        let changed := spec.columns.toList.filter fun c =>
          match oldSpec.columns.find? (·.name == c.name) with
          | some o => { o with shape := c.shape } != c
          | none => false
        steps := steps ++ (reshaped.filter fun c => !(changed.any (·.name == c.name))).map
          fun c => .restampShape spec.name c.name
        for c in added do
          unless c.nullable || c.dflt.isSome do
            throw s!"table \"{spec.name}\": new column \"{c.name}\" is NOT NULL with no \
default — existing rows have no value for it. Make it `Option`, or give it a \
`:= default` (existing rows take the default), or migrate by hand."
        if changed.isEmpty then
          steps := steps ++ added.map (.addColumn spec.name ·)
            ++ dropped.map (.dropColumn spec.name ·.name)
        else
          -- rebuild carries adds and drops along
          let copyCols := spec.columns.toList.filterMap fun c =>
            if (oldSpec.columns.find? (·.name == c.name)).isSome then some c.name else none
          for c in changed do
            notes := notes ++ [s!"\"{spec.name}\".\"{c.name}\" changed shape → table rebuild"]
          unless dropped.isEmpty do
            notes := notes ++ [s!"rebuild of \"{spec.name}\" DROPS columns {dropped.map (·.name)}"]
          for c in added do
            unless c.nullable || c.dflt.isSome do
              throw s!"table \"{spec.name}\": new column \"{c.name}\" must be nullable or \
carry a default (rebuild)"
          steps := steps ++ [.rebuildTable spec copyCols]
        if changed.isEmpty then
          for ix in spec.indexes do
            unless oldSpec.indexes.any (· == ix) do
              steps := steps ++ [.addIndex spec.name ix]
          for ix in oldSpec.indexes do
            unless spec.indexes.any (· == ix) do
              steps := steps ++ [.dropIndex spec.name ix]
  -- dropped tables
  for oldSpec in old do
    if (new.find? (·.name == oldSpec.name)).isNone then
      steps := steps ++ [.dropTable oldSpec.name]
  return { steps, notes }

/-- Is this plan destructive? dropTable/dropColumn, or a rebuild whose copy
    list is shorter than the old table's columns. -/
def MigPlan.destructiveAgainst (p : MigPlan) (old : List TableSpec) : Bool :=
  p.steps.any fun s =>
    s.destructive ||
      match s with
      | .rebuildTable spec copyCols =>
          match old.find? (·.name == spec.name) with
          | some o => copyCols.length < o.columns.size
          | none => false
      | _ => false

structure MigrateReport where
  applied : List String
  notes : List String
  fingerprint : String
  /-- The versions moved between, when a migration was applied. -/
  fromVersion : Option Nat := none
  toVersion : Option Nat := none
  /-- The backup taken before applying, when one was. -/
  backup : Option String := none
  deriving Repr

open Lean (Json) in
def MigrateReport.toJson (r : MigrateReport) : Json :=
  Json.mkObj <| [("ok", Json.bool true),
    ("applied", Json.arr (r.applied.map Json.str).toArray),
    ("notes", Json.arr (r.notes.map Json.str).toArray),
    ("fingerprint", Json.str r.fingerprint)] ++
    (match r.fromVersion, r.toVersion with
      | some f, some t => [("from_version", Lean.toJson f), ("to_version", Lean.toJson t)]
      | _, _ => []) ++
    (match r.backup with
      | some b => [("backup", Json.str b)]
      | none => [])

/-- How to migrate: report only, or apply; whether drops are allowed;
    and where to put the full backup taken before applying (`none` =
    no backup). -/
structure MigrateOpts where
  apply : Bool := false
  allowDestructive : Bool := false
  backup : Option System.FilePath := none

private def readStoredSchemaRaw (db : SQLite) : IO (Except String (Option (List TableSpec))) := do
  let stmt ← db.prepare "SELECT value FROM _leandb_meta WHERE key = 'schema_json'"
  if ← stmt.step then
    let raw ← stmt.columnText 0
    match Lean.Json.parse raw >>= specsFromJson? with
    | .ok specs => return .ok (some specs)
    | .error e => return .error s!"stored schema metadata is invalid: {e}"
  else
    return .ok none

/-- The schema the instance was last shaped to, if readable. -/
def readStoredSchema (conn : Conn) : IO (Option (List TableSpec)) := do
  match ← readStoredSchemaRaw conn.raw with
  | .ok s => return s
  | .error _ => return none

private def writeStoredSchema (db : SQLite) (specs : List TableSpec) : IO Unit := do
  let stmt ← db.prepare "INSERT OR REPLACE INTO _leandb_meta (key, value) VALUES (?, ?)"
  stmt.bindText 1 "schema_json"
  stmt.bindText 2 (specsToJson specs).compress
  stmt.exec
  stmt.reset
  stmt.clearBindings
  stmt.bindText 1 "schema_fingerprint"
  stmt.bindText 2 (fingerprint specs)
  stmt.exec

/-- Plan (and optionally apply) the migration from an instance's stored
    schema to the code's schema, on an open connection (`openDbRaw` is
    enough — the connection need not verify). `apply := false` only
    reports. -/
def migrateOn (conn : Conn) (specs : List TableSpec) (opts : MigrateOpts) :
    IO (Except DbError (Option MigPlan × Option MigrateReport)) := do
  let apply := opts.apply
  let allowDestructive := opts.allowDestructive
  if let .error e := validateSchema specs then return .error e
  try
    let db := conn.raw
    db.exec "PRAGMA foreign_keys = ON"
    db.exec "CREATE TABLE IF NOT EXISTS _leandb_meta (key TEXT PRIMARY KEY, value TEXT NOT NULL)"
    db.exec migrationsDdl
    ensureColumns db "_leandb_migrations" journalColumns
    let old? ← match ← readStoredSchemaRaw db with
      | .ok old? => pure old?
      | .error msg => return .error (.migrate msg)
    let old := old?.getD []
    match planMigration old specs with
    | .error msg => return .error (.migrate msg)
    | .ok plan =>
        let plan := { plan with isDestructive := plan.destructiveAgainst old }
        if plan.steps.isEmpty then
          if apply then writeStoredSchema db specs
          return .ok (some plan, some { applied := [], notes := ["schema already up to date"], fingerprint := fingerprint specs })
        if !apply then
          return .ok (some plan, none)
        if plan.isDestructive && !allowDestructive then
          return .error (.migrate
            "plan is destructive (drops tables or columns); pass --allow-destructive")
        -- the full backup precedes the transaction: VACUUM INTO cannot run
        -- inside one, and the file it writes is what `migrate rollback` restores
        if let some dest := opts.backup then
          backupTo conn dest
        let fromVer := ((← readMeta db "schema_version").bind (·.toNat?)).getD 0
        let toVer := fromVer + 1
        db.exec "PRAGMA foreign_keys = OFF"
        -- a rebuild renames the scratch table over the old one; an adopted file may
        -- carry views over it (uncarried by the importer), which the modern rename
        -- check rejects — the legacy behaviour is the one the swap needs
        db.exec "PRAGMA legacy_alter_table = ON"
        db.exec "BEGIN"
        try
          for step in plan.steps do
            for sql in step.sql do
              db.exec sql
          -- referential integrity must survive the migration
          let stmt ← db.prepare "PRAGMA foreign_key_check"
          if ← stmt.step then
            let t ← stmt.columnText 0
            throw <| IO.userError s!"foreign_key_check failed on table {t}"
          writeStoredSchema db specs
          -- version bump + journal, atomic with the migration itself
          writeMeta db "schema_version" (toString toVer)
          let j ← db.prepare
            "INSERT INTO _leandb_migrations (steps, fingerprint, ok, from_version, to_version, backup) \
VALUES (?, ?, 1, ?, ?, ?)"
          j.bindText 1 (Lean.Json.arr
            (plan.steps.map (Lean.Json.str ·.describe)).toArray).compress
          j.bindText 2 (fingerprint specs)
          j.bindInt64 3 (Int64.ofNat fromVer)
          j.bindInt64 4 (Int64.ofNat toVer)
          match opts.backup with
          | some dest => j.bindText 5 dest.toString
          | none => j.bindNull 5
          j.exec
          db.exec "COMMIT"
        catch e =>
          db.exec "ROLLBACK"
          db.exec "PRAGMA legacy_alter_table = OFF"
          db.exec "PRAGMA foreign_keys = ON"
          return .error (.migrate (toString e))
        db.exec "PRAGMA legacy_alter_table = OFF"
        db.exec "PRAGMA foreign_keys = ON"
        let report : MigrateReport := {
          applied := plan.steps.map (·.describe)
          notes := plan.notes
          fingerprint := fingerprint specs
          fromVersion := some fromVer
          toVersion := some toVer
          backup := opts.backup.map (·.toString) }
        return .ok (some plan, some report)
  catch e =>
    return .error (.sqlite (toString e))

/-- `migrateOn` against a file: the one-shot form for scripts and tests. -/
def migrate (path : System.FilePath) (specs : List TableSpec)
    (apply : Bool) (allowDestructive : Bool := false) :
    IO (Except DbError (Option MigPlan × Option MigrateReport)) := do
  match ← openDbRaw path with
  | .error e => return .error e
  | .ok conn => migrateOn conn specs { apply, allowDestructive }

/-- The last applied migration that has a backup to return to:
    `(journal idx, from_version, backup path)`. Migration rows carry no
    `note`; rollback/restore events do (`journalEvent`), and are not
    themselves restorable. -/
def lastRestorable (conn : Conn) : IO (Option (Nat × Option Nat × String)) := do
  let stmt ← conn.raw.prepare
    "SELECT idx, from_version, backup FROM _leandb_migrations \
WHERE ok = 1 AND backup IS NOT NULL AND note IS NULL ORDER BY idx DESC LIMIT 1"
  if ← stmt.step then
    let from? ← do
      if (← stmt.columnType 1) == .null then pure none
      else pure (some (← stmt.columnInt64 1).toNatClampNeg)
    return some ((← stmt.columnInt64 0).toNatClampNeg, from?, ← stmt.columnText 2)
  else return none

/-- Journal an event that is not a schema migration (a rollback, a
    restore): the steps name it, `ok` records the outcome. -/
def journalEvent (conn : Conn) (steps : List String) (ok : Bool)
    (fromVer toVer : Option Nat) (backup : Option String) (note : String) : IO Unit := do
  let fp := (← readMeta conn.raw "schema_fingerprint").getD ""
  let j ← conn.raw.prepare
    "INSERT INTO _leandb_migrations (steps, fingerprint, ok, from_version, to_version, backup, note) \
VALUES (?, ?, ?, ?, ?, ?, ?)"
  j.bindText 1 (Lean.Json.arr (steps.map Lean.Json.str).toArray).compress
  j.bindText 2 fp
  j.bindInt64 3 (if ok then 1 else 0)
  match fromVer with | some v => j.bindInt64 4 (Int64.ofNat v) | none => j.bindNull 4
  match toVer with | some v => j.bindInt64 5 (Int64.ofNat v) | none => j.bindNull 5
  match backup with | some b => j.bindText 6 b | none => j.bindNull 6
  j.bindText 7 note
  j.exec

/-- What an open instance says about itself, readable even when drifted:
    (fingerprint, schema_version). -/
def instanceInfoOn (conn : Conn) : IO (Option String × Option Nat) := do
  try
    let fp ← readMeta conn.raw "schema_fingerprint"
    let ver ← readMeta conn.raw "schema_version"
    return (fp, ver.bind (·.toNat?))
  catch _ =>
    return (none, none)

/-- `instanceInfoOn` against a file. `none` = file absent (nothing is
    created). -/
def instanceInfo (path : System.FilePath) : IO (Option (Option String × Option Nat)) := do
  if !(← path.pathExists) then return none
  try
    let db ← SQLite.open path
    return some (← instanceInfoOn (← Conn.ofRaw db))
  catch _ =>
    return some (none, none)

end LeanDb
