import LeanDb.Db
import LeanDb.Migrate

namespace LeanDb

/-! # Versioned, typed migrations

A base's schema history is a *chain*: the frozen origin snapshot (V0) and
one `Migration` per version after it, each carrying the schema it moves
to (as data) and the steps that move the rows. The mechanical steps are
diffed from the two snapshots exactly as `planMigration` does today; what
the diff cannot decide — a value for a new NOT NULL column, a shrunk
closed world, a changed JSON shape — is a `Step.transform`, an ordinary
Lean function from the *old* row type (a raw structure `migrate freeze`
generated from the snapshot) to the *new* entity type. Old versions live
on as types; the compiler checks the transform is total over them.

An instance names the snapshot it is at by fingerprint; `schema_version`
is its index in the chain. Applying moves it along the chain, one
migration per transaction, a backup first. -/

open Lean (Json)

/-- One judgment step of a migration. Rows of `table` are rewritten by
    `run`, which sees the old row's stored columns (old snapshot order,
    `id` excluded) and produces the new row's (new snapshot order). The
    typed constructors below are the way to build one. -/
inductive Step where
  | transform (table : String) (describe : String)
      (run : TableSpec → TableSpec → Array Col → Except String (Array Col))
  /-- Raw SQL, journaled by its description: the escape hatch. -/
  | custom (describe : String) (run : Conn → IO Unit)

def Step.describe : Step → String
  | .transform _ d _ => d
  | .custom d _ => d

def Step.table? : Step → Option String
  | .transform t _ _ => some t
  | .custom .. => none

/-- A typed row transform: decode each old row as `Old` (the frozen raw
    structure), map it, encode through the head entity `New`. The first
    failure aborts the migration naming the row. -/
def Step.transformT (Old New : Type) [Entity Old] [Entity New]
    (f : Old → Except String New) (describe : String := "")
    (table : String := Entity.tableName New) : Step :=
  .transform table
    (if describe.isEmpty then s!"transform rows of \"{table}\" ({Entity.typeName Old} → {Entity.typeName New})" else describe)
    fun _ _ cols => do
      let old ← (Entity.decode (α := Old) cols).mapError (·.message)
      let new ← f old
      return Entity.encode new

/-- Fill one column of every row from the old row's stored columns, by
    name (a new NOT NULL column without a default; a re-typed column).
    Every other column is carried by name; a column that no longer
    exists is dropped. -/
def Step.fill (table col : String) (f : (String → Option Col) → Except String Col) : Step :=
  .transform table s!"fill \"{table}\".\"{col}\"" fun old new cols => do
    let get : String → Option Col := fun n => do
      let i ← old.columns.findIdx? (·.name == n)
      cols[i]?
    let out ← new.columns.toList.mapM fun c =>
      if c.name == col then f get
      else match get c.name with
        | some v => Except.ok v
        | none => Except.error s!"column \"{c.name}\" has no old value and no fill"
    return out.toArray

/-- Re-label a closed world's stored values (a renamed or removed variant):
    values not in `map` pass through. -/
def Step.remapEnum (table col : String) (map : List (String × String)) : Step :=
  .fill table col fun get =>
    match get col with
    | some (.text v) => .ok (.text ((map.lookup v).getD v))
    | some other => .ok other
    | none => .error s!"column \"{col}\" has no old value"

structure Migration where
  /-- Fingerprint of the snapshot this migration starts from. -/
  fromFingerprint : String
  /-- Fingerprint of `snapshot`. -/
  toFingerprint : String
  /-- The schema after this migration, as data. -/
  snapshot : List TableSpec
  steps : List Step := []
  note : String := ""

/-- The frozen origin and every migration after it, in order. -/
structure Chain where
  origin : List TableSpec
  migrations : List Migration := []

/-- The schema at version `k` (0 = origin). -/
def Chain.at? (c : Chain) (k : Nat) : Option (List TableSpec) :=
  if k == 0 then some c.origin else c.migrations[k - 1]?.map (·.snapshot)

def Chain.headVersion (c : Chain) : Nat := c.migrations.length

def Chain.head (c : Chain) : List TableSpec :=
  (c.migrations.getLast?.map (·.snapshot)).getD c.origin

/-- Every version's fingerprint, index = version. -/
def Chain.fingerprints (c : Chain) : List String :=
  fingerprint c.origin :: c.migrations.map (·.toFingerprint)

/-- Which version an instance fingerprint is at. -/
def Chain.versionOf? (c : Chain) (fp : String) : Option Nat :=
  c.fingerprints.findIdx? (· == fp)

/-- The chain's internal consistency: links match, snapshots hash to
    their declared fingerprints, and the head is the code's schema. The
    message names the first thing wrong. -/
def Chain.check (c : Chain) (specs : List TableSpec) : Except String Unit := do
  let mut prev := fingerprint c.origin
  let mut k := 0
  for m in c.migrations do
    k := k + 1
    unless m.fromFingerprint == prev do
      throw s!"migration to V{k} starts from {m.fromFingerprint} but V{k-1} is {prev}"
    unless fingerprint m.snapshot == m.toFingerprint do
      throw s!"V{k}.schema hashes to {fingerprint m.snapshot}, not the declared {m.toFingerprint}"
    prev := m.toFingerprint
  unless fingerprint specs == prev do
    throw s!"the code's schema ({fingerprint specs}) is not the chain's head V{k} ({prev}): \
run `migrate freeze` to snapshot the change (or revert it)"

/-- Build-time form: fails the build when the chain does not end at the
    code's schema. `specs` must be pure data (`Entity.spec` lists, or the
    base's derived specs). -/
def Chain.assertHead (c : Chain) (specs : List TableSpec) : IO Unit := do
  match c.check specs with
  | .ok () => pure ()
  | .error m => throw <| IO.userError s!"leandb_check_head: {m}"

/-- `leandb_check_head chain specs` — the build fails until the schema is
    frozen. Put it in a module the base's executable does not import (its
    tests, which `defaultTargets` builds): then `lake build <base>` still
    produces the binary that runs `migrate freeze`, while the default
    build stays red until the change is snapshotted. -/
macro "leandb_check_head " c:term:max specs:term:max : command =>
  `(#eval LeanDb.Chain.assertHead $c $specs)

/-! ## Adopting an unstamped file

An imported base is *adopted*: the file has the tables, the engine has
never written to it. Unfrozen, the first open stamps it with the code's
schema — correct, because the importer generated the code from that very
file. With a chain, the file may be older than the head: the version
whose tables and columns it actually has is the one to stamp. -/

private def liveColumns (conn : Conn) (table : String) : IO (List (String × String × Bool)) := do
  let stmt ← conn.raw.prepare s!"PRAGMA table_info({quoteIdent table})"
  let mut out := []
  repeat
    if ← stmt.step then
      let name ← stmt.columnText 1
      let ty ← stmt.columnText 2
      let notnull := (← stmt.columnInt64 3) == 1
      if name != "id" then out := out ++ [(name, ty.toUpper, notnull)]
    else break
  return out

private def declaredType : SqlType → String
  | .integer => "INTEGER"
  | .text => "TEXT"
  | .real => "REAL"

/-- Does the file hold exactly this snapshot's tables (names, columns,
    declared types, nullability)? Tables the snapshot does not know are
    ignored, as adoption always has. -/
private def matchesSnapshot (conn : Conn) (specs : List TableSpec) : IO Bool := do
  for t in specs do
    let live ← liveColumns conn t.name
    if live.isEmpty then return false
    let want := t.columns.toList.map fun c => (c.name, declaredType c.sqlType, !c.nullable)
    -- SQLite reports the DECLARED type, which can be any of the affinity
    -- synonyms: BIGINT, SMALLINT and TINYINT are INTEGER affinity;
    -- VARCHAR, CHARACTER and CLOB are TEXT affinity. The snapshots record
    -- the canonical spelling, so the match must normalize the same way
    -- SQLite computes affinity (https://sqlite.org/datatype3.html §3.1) —
    -- otherwise a file whose columns are declared BIGINT or VARCHAR
    -- matches no version, `adopt` returns none, and `verify` stamps it at
    -- the head, silently skipping the migrations in between.
    let norm := fun (x : String × String × Bool) =>
      let (n, ty, nn) := x
      let aff := if ty.contains "INT" then "INTEGER"
        else if ty.contains "CHAR" || ty.contains "CLOB" || ty.contains "TEXT" then "TEXT"
        else if ty.isEmpty || ty.contains "BLOB" then "BLOB"
        else if ty.contains "REAL" || ty.contains "FLOA" || ty.contains "DOUB" then "REAL"
        else "NUMERIC"
      (n, aff, nn)
    if live.map norm != want then return false
  return true

/-- The version of the chain whose snapshot the unstamped file matches,
    newest first; `none` when the file has no tables of the origin (a
    fresh file) or matches no version. -/
def Chain.adoptVersion? (c : Chain) (conn : Conn) : IO (Option Nat) := do
  let mut k := c.headVersion
  repeat
    let some specs := c.at? k | break
    if ← matchesSnapshot conn specs then return some k
    if k == 0 then break
    k := k - 1
  return none

/-- Stamp an unstamped file at version `k` (no DDL runs). -/
def Chain.stamp (c : Chain) (conn : Conn) (k : Nat) : IO Unit := do
  let some specs := c.at? k | pure ()
  writeMeta conn.raw "schema_json" (specsToJson specs).compress
  writeMeta conn.raw "schema_fingerprint" (fingerprint specs)
  writeMeta conn.raw "schema_version" (toString k)

/-- Before verifying: an unstamped file with the origin's tables is stamped
    at the version it matches, so `migrate` can carry it forward instead
    of `verify` mislabeling it as the head. -/
def Chain.adopt (c : Chain) (conn : Conn) : IO (Option Nat) := do
  if (← readMeta conn.raw "schema_fingerprint").isSome then return none
  match ← c.adoptVersion? conn with
  | some k => c.stamp conn k; return some k
  | none => return none

/-! ## Executing a migration -/

/-- The mechanical plan of a migration, with the declared transforms
    taking over the tables they cover. -/
def Migration.plan (prev : List TableSpec) (m : Migration) : Except String MigPlan := do
  let covered := m.steps.filterMap (·.table?)
  planMigration prev m.snapshot covered

/-- Rewrite one table under a transform, inside the caller's transaction:
    the new table is created under a scratch name, every old row is read,
    transformed and inserted with its `id`, then the tables swap. -/
private def transformTable (conn : Conn) (old new : TableSpec)
    (run : TableSpec → TableSpec → Array Col → Except String (Array Col)) : IO Nat := do
  let db := conn.raw
  let tmp := s!"_leandb_new_{new.name}"
  db.exec (new.ddlNamed tmp (ifNotExists := false))
  let oldCols := String.intercalate ", " (old.columns.toList.map (quoteIdent ·.name))
  let sel ← db.prepare s!"SELECT id, {oldCols} FROM {quoteIdent old.name}"
  let newCols := String.intercalate ", " ("id" :: new.columns.toList.map (quoteIdent ·.name))
  let marks := String.intercalate ", " (List.replicate (new.columns.size + 1) "?")
  let ins ← db.prepare s!"INSERT INTO {quoteIdent tmp} ({newCols}) VALUES ({marks})"
  let mut n := 0
  repeat
    if ← sel.step then
      let id ← sel.columnInt64 0
      let cols ← match ← readRow sel 1 old.columns.size (fun i => (old.name, (old.columns[i]?.map (·.name)).getD "?")) with
        | .ok cols => pure cols
        | .error e => throw <| IO.userError s!"row {id} of \"{old.name}\": {e.message}"
      let out ← match run old new cols with
        | .ok out => pure out
        | .error msg => throw <| IO.userError s!"row {id} of \"{old.name}\": {msg}"
      unless out.size == new.columns.size do
        throw <| IO.userError s!"row {id} of \"{old.name}\": transform produced {out.size} columns, \"{new.name}\" has {new.columns.size}"
      ins.reset
      ins.clearBindings
      ins.bindInt64 1 id
      bindCols ins 2 out
      ins.exec
      n := n + 1
    else break
  db.exec s!"DROP TABLE {quoteIdent old.name}"
  db.exec s!"ALTER TABLE {quoteIdent tmp} RENAME TO {quoteIdent new.name}"
  return n

/-- Apply one migration to an instance known to be at `prev`, in one
    transaction after an optional backup. Returns the applied step
    descriptions. -/
def Migration.applyOn (conn : Conn) (prev : List TableSpec) (m : Migration)
    (toVersion : Nat) (allowDestructive : Bool) (backup : Option System.FilePath) :
    IO (Except DbError MigrateReport) := do
  let plan ← match m.plan prev with
    | .ok p => pure { p with isDestructive := p.destructiveAgainst prev }
    | .error msg => return .error (.migrate msg)
  if plan.isDestructive && !allowDestructive then
    return .error (.migrate "plan is destructive (drops tables or columns); pass --allow-destructive")
  let db := conn.raw
  try
    -- A same-second collision (#74) is resolved by `backupToUniquified`,
    -- so an immediate `migrate apply` retry never wedges on the clock.
    let backup ← match backup with
      | some dest => some <$> backupToUniquified conn dest
      | none => pure none
    db.exec "PRAGMA foreign_keys = OFF"
    -- a rebuild renames the scratch table over the old one; an adopted file may
    -- carry views over it (uncarried by the importer), which the modern rename
    -- check rejects — the legacy behaviour is the one the swap needs
    db.exec "PRAGMA legacy_alter_table = ON"
    db.exec "BEGIN"
    let mut applied : List String := []
    try
      for step in plan.steps do
        match step with
        | .rebuildTable spec _ =>
            match m.steps.find? (·.table? == some spec.name), prev.find? (·.name == spec.name) with
            | some (.transform _ d run), some old =>
                let n ← transformTable conn old spec run
                applied := applied ++ [s!"{d}: {n} rows"]
            | _, _ =>
                for sql in step.sql do db.exec sql
                applied := applied ++ [step.describe]
        | _ =>
            for sql in step.sql do db.exec sql
            applied := applied ++ [step.describe]
      for step in m.steps do
        if let .custom d run := step then
          run conn
          applied := applied ++ [d]
      let stmt ← db.prepare "PRAGMA foreign_key_check"
      if ← stmt.step then
        throw <| IO.userError s!"foreign_key_check failed on table {← stmt.columnText 0}"
      writeMeta db "schema_json" (specsToJson m.snapshot).compress
      writeMeta db "schema_fingerprint" m.toFingerprint
      writeMeta db "schema_version" (toString toVersion)
      let j ← db.prepare
        "INSERT INTO _leandb_migrations (steps, fingerprint, ok, from_version, to_version, backup) \
VALUES (?, ?, 1, ?, ?, ?)"
      j.bindText 1 (Json.arr (applied.map Json.str).toArray).compress
      j.bindText 2 m.toFingerprint
      j.bindInt64 3 (Int64.ofNat (toVersion - 1))
      j.bindInt64 4 (Int64.ofNat toVersion)
      match backup with
      | some dest => j.bindText 5 dest.toString
      | none => j.bindNull 5
      j.exec
      db.exec "COMMIT"
    catch e =>
      db.exec "ROLLBACK"
      db.exec "PRAGMA legacy_alter_table = OFF"
      db.exec "PRAGMA foreign_keys = ON"
      return .error (.migrate s!"V{toVersion}: {e}")
    db.exec "PRAGMA legacy_alter_table = OFF"
    db.exec "PRAGMA foreign_keys = ON"
    let report : MigrateReport := {
      applied
      notes := plan.notes
      fingerprint := m.toFingerprint
      fromVersion := some (toVersion - 1)
      toVersion := some toVersion
      backup := backup.map (·.toString) }
    return .ok report
  catch e =>
    return .error (.sqlite (toString e))

end LeanDb
