import LeanDb.Base
import LeanDb.Migrate
import LeanDb.Freeze

namespace LeanDb.Cli

/-! # The derived CLI

A base gets a machine-first CLI from its `LeanDb.Base` value; every
verb's behavior and JSON shape is derived from `Entity` instances. Exit
codes per plan.md §4.5: 0 ok, 2 typed `DbError` (JSON on stderr), 3 usage,
4 schema/version mismatch (`DbError.exitCode`).
The argv boundary is the one place strings are inherent; they are parsed
into types immediately and everything past this module is typed. The
instance is resolved from argv/environment (`Instance.resolve`), never
compiled into the base.
-/

open Lean (Json)

/-- How a CLI/serve argument string parses into a typed value. Closed
    enums parse by variant name for free; bases add instances for their
    newtypes. -/
class CliArg (α : Type) where
  parse : String → Except String α

instance : CliArg Nat := ⟨fun s => match s.toNat? with
  | some n => .ok n
  | none => .error s!"expected a natural number, got {String.quote s}"⟩

instance : CliArg Int64 := ⟨fun s => match s.toInt? with
  | some i =>
      if i < Int64.minValue.toInt || i > Int64.maxValue.toInt then
        .error s!"integer out of Int64 range: {s}"
      else .ok (Int64.ofInt i)
  | none => .error s!"expected an integer, got {String.quote s}"⟩

instance : CliArg String := ⟨.ok⟩

instance : CliArg (Id α) := ⟨fun s => do
  let n ← (CliArg.parse s : Except String Nat)
  if n > Int64.maxValue.toNatClampNeg then
    throw s!"row id out of Int64 range: {s}"
  return ⟨Int64.ofNat n⟩⟩

instance [ClosedEnum α] : CliArg α := ⟨fun s =>
  match ClosedEnum.decodeName s with
  | some a => .ok a
  | none => .error s!"{String.quote s} is not one of {ClosedEnum.variants α}"⟩

/-- How a query result renders as JSON. -/
class QueryOut (α : Type) where
  json : α → Json

instance [Entity α] : QueryOut (Stored α) := ⟨rowJson α⟩
instance [QueryOut α] [QueryOut β] : QueryOut (α × β) :=
  ⟨fun (a, b) => Json.arr #[QueryOut.json a, QueryOut.json b]⟩
instance [QueryOut α] : QueryOut (Array α) := ⟨fun xs => Json.arr (xs.map QueryOut.json)⟩
instance [QueryOut α] : QueryOut (List α) := ⟨fun xs => Json.arr (xs.map QueryOut.json).toArray⟩
instance [QueryOut α] : QueryOut (Option α) :=
  ⟨fun | none => Json.null | some a => QueryOut.json a⟩
instance : QueryOut Nat := ⟨Lean.toJson⟩
instance : QueryOut String := ⟨Json.str⟩
instance : QueryOut Bool := ⟨Json.bool⟩
instance : QueryOut Unit := ⟨fun _ => Json.null⟩
instance : QueryOut Json := ⟨id⟩

/-- Pop one typed positional argument (used by `query%`-derived handlers). -/
def popArg (α : Type) [CliArg α] (name : String) (args : List String) :
    DbM (α × List String) := do
  match args with
  | [] => throw (.decode "cli" name "missing argument")
  | a :: rest =>
      match CliArg.parse (α := α) a with
      | .ok v => return (v, rest)
      | .error m => throw (.decode "cli" name m)

def doneArgs : List String → DbM Unit
  | [] => pure ()
  | extra => throw (.decode "cli" "args" s!"unexpected extra arguments {extra}")

def okResult (j : Json) : Json := Json.mkObj [("ok", Json.bool true), ("result", j)]

/-- The `seed` verb's response, when the base declares a seed. -/
private def seedJson : Json := Json.mkObj [("ok", Json.bool true), ("seeded", Json.bool true)]

private def usageJson (b : Base) (inst : Instance) : Json :=
  Json.mkObj [
    ("ok", Json.bool true),
    ("base", Json.str b.name),
    ("instance", Json.str inst.path.toString),
    ("usage", Json.arr (#[
      Json.str "schema",
      Json.str "insert <table> <json>",
      Json.str "get <table> <id>",
      Json.str "update <table> <id> <partial-json>",
      Json.str "delete <table> <id>",
      Json.str "rows <table> [--eq col=value]... [--limit n]",
      Json.str "version",
      Json.str "query <name> [args...]"] ++
      (if b.seed.isSome then #[Json.str "seed"] else #[]) ++ #[
      Json.str "log [limit]",
      Json.str "log prune <keep>  (delete older audit entries; 0 clears the log)",
      Json.str "migrate status | apply [--allow-destructive] [--no-backup] | rollback | history [limit] | freeze [--module M]",
      Json.str "backup  (full copy under <instance dir>/backups)",
      Json.str "restore <file>  (refused while another writer holds the instance write \
lock; a writer that opens mid-swap still loses its post-swap writes)",
      Json.str "serve  (JSON-lines over stdio, persistent connection)",
      Json.str "serve --http <port> [--bind <host>] [--auth-token <t>]  (HTTP/1.1; every route is sugar over the CLI; $LEANDB_TOKEN also sets the token)",
      Json.str "serve --mcp  (Model Context Protocol over stdio; tools derived from tables and queries)",
      Json.str "--db <path>  (before the verb, or `$LEANDB_DB`, else the base default; `--` ends options)"])),
    ("tables", Json.arr (b.tables.map (Json.str ·.name)).toArray),
    ("queries", Json.arr (b.queries.map fun q =>
      Json.mkObj [("name", Json.str q.name),
        ("params", Json.arr (q.params.map fun (n, t) =>
          Json.mkObj [("name", Json.str n), ("type", Json.str t)]).toArray)]).toArray)]

private def parseId (s : String) : Except String Int64 :=
  match s.toNat? with
  | some n =>
      if n > Int64.maxValue.toNatClampNeg then
        .error s!"row id out of Int64 range: {s}"
      else .ok (Int64.ofNat n)
  | none => .error s!"expected a row id, got {String.quote s}"

/-- Parse a `log`/`history`/`--limit` count. Like row ids (`parseId`), a
    limit that exceeds `Int64` range is refused loudly: a bare
    `Int64.ofNat` would wrap `2^63` to a negative LIMIT, and SQLite reads
    a negative LIMIT as *no limit* — the caller's own cap silently gone. -/
def limitOf (s : String) : Except String Nat :=
  match s.toNat? with
  | some n =>
      if n > Int64.maxValue.toNatClampNeg then
        .error s!"limit out of Int64 range: {s}"
      else .ok n
  | none => .error s!"expected a limit, got {String.quote s}"

private def parseJson (s : String) : Except String Json := Json.parse s

private def table? (b : Base) (name : String) : Except String CliTable :=
  match b.tables.find? (·.name == name) with
  | some t => .ok t
  | none => .error s!"unknown table {String.quote name}; tables: {b.tables.map (·.name)}"

/-- Parse a `serve --http` port: a plain number in 1..65535. `Nat.toUInt16`
    reduces modulo 2^16, so an unguarded conversion silently binds an
    unintended port (`70000` → 4464) while the operator watches for 70000. -/
def portOf (s : String) : Except String UInt16 :=
  match s.toNat? with
  | some p =>
      if p == 0 || p > 65535 then .error s!"port out of range: {s} (expected 1..65535)"
      else .ok p.toUInt16
  | none => .error s!"expected a port, got {String.quote s}"

private def logJson (limit : Nat) : DbM Json := do
  let rows ← readLog limit
  return Json.mkObj [("ok", Json.bool true), ("count", Lean.toJson rows.size),
    ("entries", Json.arr rows)]

/-- `rows` flags: `--eq col=value`… `--limit n` (or a bare trailing limit). -/
private def parseRowFlags : List String → List (String × String) → Nat →
    Except String (List (String × String) × Nat)
  | [], eqs, limit => .ok (eqs.reverse, limit)
  | "--eq" :: kv :: rest, eqs, limit =>
      -- split at the first `=` only: a value may itself contain `=`
      -- (a canonical `M=4096,N=4096` binding, say)
      match kv.splitOn "=" with
      | k :: v :: vs => parseRowFlags rest ((k, String.intercalate "=" (v :: vs)) :: eqs) limit
      | _ => .error s!"--eq expects col=value, got {String.quote kv}"
  | "--limit" :: n :: rest, eqs, _ =>
      match limitOf n with
      | .ok limit => parseRowFlags rest eqs limit
      | .error m => .error m
  | [n], eqs, _ =>
      if n.toNat?.isNone then .error s!"unrecognized rows argument {String.quote n}"
      else do
        let limit ← limitOf n
        .ok (eqs.reverse, limit)
  | arg :: _, _, _ => .error s!"unrecognized rows argument {String.quote arg}"

private def queryNames (b : Base) : List String :=
  b.queries.map (·.name) ++ (if b.seed.isSome then ["seed"] else [])

/-- Resolve argv into one typed database action (or a usage error). -/
private def command (b : Base) : List String → Except String (DbM Json)
  | ["insert", t, j] => do pure ((← table? b t).insertJson (← parseJson j))
  | ["get", t, i] => do pure ((← table? b t).getJson (← parseId i))
  | ["update", t, i, j] => do
      pure ((← table? b t).updateJson (← parseId i) (← parseJson j))
  | ["delete", t, i] => do pure ((← table? b t).deleteRow (← parseId i))
  | ["log"] => .ok (logJson 50)
  | ["log", "prune", n] => do
      let some keep := n.toNat? | throw s!"expected a retention count, got {String.quote n}"
      if keep >= Int64.maxValue.toNatClampNeg then throw "log retention count is out of range"
      pure (do
        let deleted ← pruneLog keep
        return Json.mkObj [("ok", Json.bool true), ("deleted", Lean.toJson deleted),
          ("keep", Lean.toJson keep)])
  | ["log", n] => do
      pure (logJson (← limitOf n))
  | "rows" :: t :: flags => do
      let tbl ← table? b t
      let (eqs, limit) ← parseRowFlags flags [] 100
      pure (tbl.rowsWhere eqs limit)
  | ["seed"] | ["query", "seed"] =>
      match b.seed with
      | some s => .ok (do s; pure seedJson)
      | none => .error s!"this base has no seed; queries: {queryNames b}"
  | "query" :: name :: qargs =>
      match b.queries.find? (·.name == name) with
      | some q => .ok (q.run qargs)
      | none => .error s!"unknown query {String.quote name}; queries: {queryNames b}"
  | args => .error s!"unrecognized command {args}"

private def usageErr (m : String) : Json :=
  Json.mkObj [("ok", Json.bool false), ("code", Json.str "usage"), ("message", Json.str m)]

/-- The `version` report: code vs instance fingerprint, version, sync. -/
private def versionJson (b : Base) (info : Option (Option String × Option Nat)) : Json :=
  let codeFp := fingerprint b.specs
  let (instFp, instVer) := match info with
    | none => (Json.null, Json.null)
    | some (fp, ver) =>
        (fp.map Json.str |>.getD Json.null, (ver.map fun v => Lean.toJson v).getD Json.null)
  Json.mkObj [("ok", Json.bool true),
    ("code_fingerprint", Json.str codeFp),
    ("instance_fingerprint", instFp),
    ("schema_version", instVer),
    ("in_sync", Json.bool (instFp == Json.str codeFp))]

/-- An open instance as a server sees it: the connection, and a gate that
    is `none` when the base's verbs are admitted and `some e` while
    `Conn.verify` refuses them (fingerprint drift, enum drift). `version`,
    `migrate`, `backup` and `restore` work either way; a successful
    `migrate apply` (or a restore) re-verifies and sets the gate. The
    connection sits in a ref because a restore replaces the file and
    reopens. -/
structure Session where
  conn : IO.Ref Conn
  gate : IO.Ref (Option DbError)
  /-- Set when a restore swapped the instance file but both reopens
      failed (#77): the connection then serves the old, now-unlinked inode
      while the path holds the new file, so even gate-exempt verbs must
      refuse (with the stored reason) until the process restarts. -/
  dead : IO.Ref (Option String)

private def gateOf (b : Base) (conn : Conn) : IO (Option DbError) := do
  if let some c := b.chain then discard <| c.adopt conn
  match ← conn.verify b.specs b.headVersion with
  | .ok () => return none
  | .error e => return some e

def Session.open (b : Base) (inst : Instance) : IO (Except DbError Session) := do
  if let .error e := b.check then return .error e
  if let some parent := inst.path.parent then
    IO.FS.createDirAll parent
  match ← openDbRaw inst.path b.log b.openConfig with
  | .error e => return .error e
  | .ok conn =>
      try applyAuxiliary conn.raw b.auxiliary catch e => return .error (.sqlite (toString e))
      let gate ← IO.mkRef (← gateOf b conn)
      return .ok { conn := ← IO.mkRef conn, gate, dead := ← IO.mkRef none }

/-- Where the next backup of this instance goes: named by the base, the
    version the instance is at, and the clock. -/
def _root_.LeanDb.Instance.backupPath (i : Instance) (b : Base) (ver : Option Nat) (now : Nat) :
    System.FilePath :=
  let v := match ver with | some v => s!"v{v}" | none => "v0"
  i.backups / s!"{b.name}-{v}-{now}.sqlite"

private def backupJson (b : Base) (inst : Instance) (sess : Session) : IO Json := do
  let conn ← sess.conn.get
  let (_, ver) ← instanceInfoOn conn
  -- a second backup in the same wall-second (#74) gets a `-2`, `-3`…
  -- suffix instead of failing the verb
  let dest ← try
    backupToUniquified conn (inst.backupPath b ver (← unixNow conn))
  catch e =>
    return (DbError.sqlite s!"backup failed: {e}").toJson
  return Json.mkObj [("ok", Json.bool true), ("backup", Json.str dest.toString),
    ("schema_version", (ver.map fun v => Lean.toJson v).getD Json.null)]

/-! ### Restore safety: validate first, swap last

Issue #25: `restore <garbage>` used to drop the live connection and
overwrite the instance before validating the source, so a failed restore
destroyed user data and left the session silently serving an empty
in-memory database; `restore /dev/zero` read the whole source into
memory. -/

/-- Replace the instance file with `src` and reopen. Validation runs
    BEFORE anything destructive (`Restore.swapFile`); the copy lands under
    a temporary name and is renamed into place so no reader ever sees a
    half-written file, and stale `-wal`/`-shm` siblings go with the old
    file. The old connection stays open until the rename has succeeded and
    the new file has opened cleanly; a failure past the swap sets the gate
    (so verbs are refused loudly instead of silently hitting an empty
    database) and reopens the instance file. If the retry open fails too
    (#77), the dead flag is set: the connection still serves the old
    unlinked inode, so gate-exempt verbs refuse as well.

    Cross-process guard (#76): the swap refuses with a typed `busy` error
    while another writer holds the instance's write lock (`BEGIN
    IMMEDIATE` probe). Residual race: a writer that opens — or goes idle —
    between the probe and the rename still ends up on the unlinked old
    inode; its post-swap commits go to the deleted file and vanish, and
    its reads keep serving the pre-restore snapshot. Closing that window
    needs an advisory lock held for the whole session, not just the probe. -/
private def replaceFile (b : Base) (inst : Instance) (sess : Session) (verb : String)
    (src : System.FilePath) : IO (Except DbError Unit) := do
  match ← assertSoleWriter (← sess.conn.get) verb with
  | .error e => return .error e
  | .ok () =>
  match ← Restore.swapFile inst.path src with
  | .error e => return .error e
  | .ok () =>
  match ← openDbRaw inst.path b.log with
  | .ok conn =>
      sess.conn.set conn
      sess.gate.set (← gateOf b conn)
      return .ok ()
  | .error e =>
      sess.gate.set (some e)
      match ← openDbRaw inst.path b.log with
      | .ok conn =>
          -- #59: the retry opened cleanly, so the gate must be recomputed
          -- from the connection actually installed; leaving the stale `e`
          -- set would hold every gated verb back although the reopened
          -- instance verifies fine
          sess.conn.set conn
          sess.gate.set (← gateOf b conn)
      | .error retry =>
          -- #77: both reopens failed. The session's connection still
          -- serves the old, now-unlinked inode while the path holds the
          -- new file: gate-exempt verbs refuse too (see `refuseDead`)
          -- instead of backing up or migrating the discarded file.
          sess.dead.set (some s!"post-restore reopen failed; the session's connection serves the replaced instance file: {e}; retry: {retry}")
      return .error e

private def restoreJson (b : Base) (inst : Instance) (sess : Session) (src : System.FilePath) :
    IO Json := do
  let before ← (← sess.conn.get) |> instanceInfoOn
  match ← replaceFile b inst sess "restore" src with
  | .error e => return e.toJson
  | .ok () =>
      let conn ← sess.conn.get
      let (fp, ver) ← instanceInfoOn conn
      journalEvent conn [s!"restore from {src}"] true before.2 ver (some src.toString) "restore"
      return Json.mkObj [("ok", Json.bool true), ("restored", Json.str src.toString),
        ("fingerprint", (fp.map Json.str).getD Json.null),
        ("schema_version", (ver.map fun v => Lean.toJson v).getD Json.null),
        ("in_sync", Json.bool ((← sess.gate.get).isNone)),
        ("note", Json.str "the swap refuses while another writer holds the instance \
write lock; a writer that opens between the lock check and the rename still points \
at the replaced file — its post-swap writes are lost (#76)")]

private def rollbackJson (b : Base) (inst : Instance) (sess : Session) : IO Json := do
  let conn ← sess.conn.get
  match ← lastRestorable conn with
  | none => return (DbError.migrate "nothing to roll back: no applied migration has a backup").toJson
  | some (idx, fromVer, backup) =>
      let (_, before) ← instanceInfoOn conn
      match ← replaceFile b inst sess "rollback" backup with
      | .error e => return e.toJson
      | .ok () =>
          let conn ← sess.conn.get
          let (fp, ver) ← instanceInfoOn conn
          journalEvent conn [s!"rollback of migration {idx} from {backup}"] true before ver
            (some backup) "rollback: writes made after the migration are not in the backup"
          return Json.mkObj [("ok", Json.bool true), ("rolled_back", Lean.toJson idx),
            ("restored", Json.str backup),
            ("fingerprint", (fp.map Json.str).getD Json.null),
            ("schema_version", (ver.map fun v => Lean.toJson v).getD Json.null),
            ("expected_version", (fromVer.map fun v => Lean.toJson v).getD Json.null),
            ("in_sync", Json.bool ((← sess.gate.get).isNone)),
            ("note", Json.str "writes made after the migration are not in the backup; \
the swap refuses while another writer holds the write lock, but a writer that opens \
between the check and the rename still loses its post-swap writes (#76)")]

private def historyJson (sess : Session) (limit : Nat) : IO Json := do
  let rows ← readJournal (← sess.conn.get) limit
  return Json.mkObj [("ok", Json.bool true), ("count", Lean.toJson rows.size), ("entries", Json.arr rows)]

private def migrateUsage : String :=
  "migrate status | apply [--allow-destructive] [--no-backup] | rollback | history [limit] \
| freeze [--module M] [--imports A,B]"

/-! ### Chain mode: the frozen history drives status and apply -/

private def rowCount (conn : Conn) (table : String) : IO Nat := do
  try
    let stmt ← conn.raw.prepare s!"SELECT COUNT(*) FROM {quoteIdent table}"
    if ← stmt.step then return (← stmt.columnInt64 0).toNatClampNeg else return 0
  catch _ => return 0

private def stepTable : MigStep → Option String
  | .createTable spec => some spec.name
  | .addColumn t _ | .dropColumn t _ | .dropTable t | .restampShape t _
  | .addIndex t _ | .dropIndex t _ | .restampInvariant t _ _ => some t
  | .rebuildTable spec _ => some spec.name

/-- One pending migration as `status` reports it: its steps with row
    counts, whether each needs a judgment and whether one is declared. -/
private def pendingJson (conn : Conn) (prev : List TableSpec) (m : Migration) (version : Nat) :
    IO (Except String (Json × Bool)) := do
  let required := (Freeze.refusals prev m.snapshot).map (·.1)
  let declared := m.steps.filterMap (·.table?)
  match m.plan prev with
  | .error msg => return .error s!"V{version}: {msg}"
  | .ok plan =>
      let destructive := plan.destructiveAgainst prev
      let mut steps : Array Json := #[]
      for st in plan.steps do
        let table := stepTable st
        let rows ← match table with
          | some t => if prev.any (·.name == t) then rowCount conn t else pure 0
          | none => pure 0
        let transform := match table with
          | some t =>
              if declared.contains t then "provided"
              else if required.contains t then "required" else "none"
          | none => "none"
        steps := steps.push <| Json.mkObj [
          ("describe", Json.str st.describe),
          ("table", (table.map Json.str).getD Json.null),
          ("rows", Lean.toJson rows),
          ("destructive", Json.bool (st.destructive ||
            (match st with
              | .rebuildTable spec cols => (prev.find? (·.name == spec.name)).any fun o => cols.length < o.columns.size
              | _ => false))),
          ("transform", Json.str transform)]
      for st in m.steps do
        if let .custom d _ := st then
          steps := steps.push <| Json.mkObj [("describe", Json.str d), ("table", Json.null),
            ("rows", Lean.toJson 0), ("destructive", Json.bool false), ("transform", Json.str "custom")]
      let missing := required.filter (!declared.contains ·)
      return .ok (Json.mkObj [
        ("version", Lean.toJson version),
        ("from", Json.str m.fromFingerprint),
        ("to", Json.str m.toFingerprint),
        ("note", Json.str m.note),
        ("destructive", Json.bool destructive),
        ("transforms_missing", Json.arr (missing.map Json.str).toArray),
        ("steps", Json.arr steps)], destructive)

/-- The `(table, column)` pairs a schema change touches: columns added,
    dropped or changed in a surviving table, and every column (`*`) of a
    dropped table. A new table touches nothing that exists. -/
def changedColumns (old new : List TableSpec) : List (String × String) := Id.run do
  let mut out : List (String × String) := []
  for o in old do
    match new.find? (·.name == o.name) with
    | none => out := out ++ [(o.name, "*")]
    | some n =>
        for c in o.columns do
          match n.columns.find? (·.name == c.name) with
          | none => out := out ++ [(o.name, c.name)]
          | some c' => if c' != c then out := out ++ [(o.name, c.name)]
        for c in n.columns do
          if (o.columns.find? (·.name == c.name)).isNone then out := out ++ [(o.name, c.name)]
  return out

/-- Which registered queries (by their static footprints) and which logged
    runs (by the footprints the log recorded) a change touches. -/
private def impactJson (b : Base) (conn : Conn) (changed : List (String × String)) : IO (Json × Json × Json) := do
  let limit := conn.logConfig.impactLimit
  let skipped := changed.isEmpty || limit == 0
  let scan ← if skipped then pure ({} : LogFootprintScan) else scanLogFootprints conn limit
  let logged := scan.entries
  let window := Json.mkObj [("limit", Lean.toJson limit), ("scanned", Lean.toJson logged.size),
    ("truncated", Json.bool scan.truncated), ("skipped", Json.bool skipped)]
  let runsOf := fun (name : String) =>
    logged.foldl (init := 0) fun n (q, cols) =>
      if q == some name && !(cols.filter fun (t, c) => changed.any fun (t', c') => t == t' && (c == c' || c' == "*")).isEmpty then n + 1 else n
  let mut items : Array Json := #[]
  for q in b.queries do
    let f := b.resolveFootprint q.footprint
    let hit := f.touching changed
    let runs := runsOf q.name
    if !hit.isEmpty || runs > 0 || (f.residual && f.tables.any fun t => changed.any (·.1 == t)) then
      items := items.push <| Json.mkObj [("query", Json.str q.name),
        ("columns", Json.arr (hit.map fun (t, c) => Json.str s!"{t}.{c}").toArray),
        ("residual", Json.bool f.residual),
        ("logged_runs", Lean.toJson runs)]
  -- logged selects outside any registered query (scripts, other programs)
  let anonymous := logged.foldl (init := 0) fun n (q, cols) =>
    if q.isNone && !(cols.filter fun (t, c) => changed.any fun (t', c') => t == t' && (c == c' || c' == "*")).isEmpty then n + 1 else n
  return (Json.arr items, Lean.toJson anonymous, window)

private def changedJson (changed : List (String × String)) : Json :=
  Json.arr (changed.map fun (t, c) => Json.str s!"{t}.{c}").toArray

/-- `migrate status` / `apply` when the base carries a chain. -/
private def chainMigrate (b : Base) (inst : Instance) (sess : Session) (c : Chain)
    (apply allowDestructive backup : Bool) : IO Json := do
  let conn ← sess.conn.get
  -- the code must be frozen before the instance can follow it
  if let .error m := c.check b.specs then
    return (DbError.migrate m).toJson
  let (fp?, ver?) ← instanceInfoOn conn
  let some fp := fp? | do
    -- a fresh instance: verify created it at the head
    return Json.mkObj [("ok", Json.bool true), ("mode", Json.str "chain"),
      ("applied", Json.arr #[]), ("notes", Json.arr #[Json.str "fresh instance, created at the head"]),
      ("fingerprint", Json.str (fingerprint b.specs)),
      ("instance_version", Lean.toJson c.headVersion), ("head_version", Lean.toJson c.headVersion)]
  let some k := c.versionOf? fp | return (DbError.unknownLineage fp c.fingerprints).toJson
  let mut notes : Array String := #[]
  if ver? != some k then
    notes := notes.push s!"instance schema_version is {ver?}; by fingerprint it is at V{k}"
  let pending := c.migrations.drop k
  if pending.isEmpty then
    return Json.mkObj [("ok", Json.bool true), ("mode", Json.str "chain"),
      ("applied", Json.arr #[]),
      ("notes", Json.arr (#[Json.str "schema already up to date"] ++ notes.map Json.str)),
      ("fingerprint", Json.str (fingerprint b.specs)),
      ("instance_version", Lean.toJson k), ("head_version", Lean.toJson c.headVersion)]
  if !apply then
    let mut items : Array Json := #[]
    let mut describes : Array Json := #[]
    let mut destructive := false
    let mut prev := (c.at? k).getD []
    let mut v := k
    for m in pending do
      v := v + 1
      match ← pendingJson conn prev m v with
      | .error msg => return (DbError.migrate msg).toJson
      | .ok (j, d) =>
          items := items.push j
          destructive := destructive || d
          if let .ok arr := j.getObjValAs? (Array Json) "steps" then
            for st in arr do
              if let .ok d := st.getObjValAs? String "describe" then
                describes := describes.push (Json.str s!"V{v}: {d}")
      prev := m.snapshot
    let changed := changedColumns ((c.at? k).getD []) c.head
    let (impact, anonymous, window) ← impactJson b conn changed
    return Json.mkObj [("ok", Json.bool true), ("mode", Json.str "chain"),
      ("instance_version", Lean.toJson k), ("head_version", Lean.toJson c.headVersion),
      ("steps", Json.arr describes), ("destructive", Json.bool destructive),
      ("notes", Json.arr (notes.map Json.str)), ("pending", Json.arr items),
      ("changed", changedJson changed), ("impact", impact), ("unregistered_runs", anonymous),
      ("impact_log", window)]
  -- apply, one migration per transaction, each after its own backup
  let mut applied : Array Json := #[]
  let mut prev := (c.at? k).getD []
  let mut v := k
  for m in pending do
    let dest ← do
      if backup then pure (some (inst.backupPath b (some v) (← unixNow conn))) else pure none
    match ← m.applyOn conn prev (v + 1) allowDestructive dest with
    | .error e =>
        sess.gate.set (← gateOf b conn)
        return Json.mkObj [("ok", Json.bool false), ("code", Json.str e.code),
          ("message", Json.str e.message), ("mode", Json.str "chain"),
          ("applied", Json.arr applied), ("instance_version", Lean.toJson v)]
    | .ok r =>
        v := v + 1
        prev := m.snapshot
        applied := applied.push <| Json.mkObj [("version", Lean.toJson v),
          ("applied", Json.arr (r.applied.map Json.str).toArray),
          ("notes", Json.arr (r.notes.map Json.str).toArray),
          ("backup", (r.backup.map Json.str).getD Json.null)]
  sess.gate.set (← gateOf b conn)
  return Json.mkObj [("ok", Json.bool true), ("mode", Json.str "chain"),
    ("applied", Json.arr applied), ("notes", Json.arr (notes.map Json.str)),
    ("fingerprint", Json.str (fingerprint b.specs)),
    ("instance_version", Lean.toJson v), ("head_version", Lean.toJson c.headVersion)]

/-- `migrate freeze`: write the next version's file and the roll-up. -/
private def freezeJson (b : Base) (flags : List String) : IO Json := do
  let rec parse : List String → Except String (Option String × List String)
    | [] => .ok (none, [])
    | "--module" :: m :: rest => do let (_, i) ← parse rest; return (some m, i)
    | "--imports" :: is :: rest => do let (m, _) ← parse rest; return (m, is.splitOn ",")
    | f :: _ => .error s!"unrecognized freeze flag {String.quote f}"
  match parse flags with
  | .error m => return usageErr m
  | .ok (module?, imports) =>
      let module := module?.getD b.module
      if module.isEmpty then
        return usageErr "freeze needs the base's Lean module: set `module` on the base or pass --module <Module>"
      let imports := if imports.isEmpty then b.freezeImports else imports
      -- the module and import names become the write target and the
      -- generated source itself; anything that is not a plain dotted
      -- identifier must be refused before any IO (a `/` or `..` would
      -- write outside the package, newlines or comment tokens would
      -- inject source into the generated files)
      unless Freeze.moduleNameOk module do
        return usageErr s!"--module {String.quote module} is not a plain dotted Lean identifier"
      for i in imports do
        unless Freeze.moduleNameOk i do
          return usageErr s!"--imports {String.quote i} is not a plain dotted Lean identifier"
      let t := Freeze.Target.ofModule module imports
      let cur := b.specs
      -- freeze renders the schema as source (DDL defaults, snapshot
      -- literals); an invalid schema — e.g. a non-finite REAL default,
      -- which has no exact literal — must be refused, not frozen
      if let .error e := validateSchema cur then
        return e.toJson
      -- the freeze text renderer cannot emit every name the derive
      -- accepts; refuse those before any IO instead of writing an
      -- uncompilable (or injectable) file
      if let .error e := Freeze.checkNames cur then
        return (DbError.migrate e).toJson
      let (n, prev) ← match b.chain with
        | some c =>
            if fingerprint c.head == fingerprint cur then
              return (DbError.migrate s!"nothing to freeze: the code's schema is the chain's head V{c.headVersion}").toJson
            pure (c.headVersion + 1, some c.head)
        | none =>
            let v0 := t.dir / "V0.lean"
            if ← v0.pathExists then
              return (DbError.migrate s!"{v0} exists but the base carries no chain: set `chain := some {module}.Migrations.chain` on the base").toJson
            pure (0, none)
      let typeNames := b.tables.map fun tbl => (tbl.name, tbl.typeName)
      let (src, holes) := Freeze.versionFile t b.name n cur prev typeNames
      let file := t.dir / s!"V{n}.lean"
      let rollup : System.FilePath := t.dir.toString ++ ".lean"
      try
        IO.FS.createDirAll t.dir
        IO.FS.writeFile file src
        IO.FS.writeFile rollup (Freeze.rollup t b.name n)
      catch e =>
        return (DbError.migrate s!"freeze could not write: {e}").toJson
      let next := if n == 0 then
          s!"add `import {module}.Migrations` to {module}.lean (before Base), `chain := some {module}.Migrations.chain` to the base, and `leandb_check_head {module}.Migrations.chain {module}.base.specs` to the tests; then `lake build`"
        else if holes > 0 then
          s!"fill the {holes} hole(s) in {file}, then `lake build` and `migrate apply`"
        else "lake build, then `migrate apply`"
      return Json.mkObj [("ok", Json.bool true), ("version", Lean.toJson n),
        ("fingerprint", Json.str (fingerprint cur)),
        ("files", Json.arr #[Json.str file.toString, Json.str rollup.toString]),
        ("holes", Lean.toJson holes), ("next", Json.str next)]

private def migrateJson (b : Base) (inst : Instance) (sess : Session) (rest : List String) : IO Json := do
  match rest with
  | ["rollback"] => rollbackJson b inst sess
  | ["history"] => historyJson sess 50
  | ["history", n] =>
      match limitOf n with
      | .ok limit => historyJson sess limit
      | .error m => return usageErr m
  | "freeze" :: flags => freezeJson b flags
  | ["status"] => runMigrate false false true
  | "apply" :: flags =>
      let known := ["--allow-destructive", "--no-backup"]
      match flags.find? (!known.contains ·) with
      | some f => return usageErr s!"unrecognized migrate flag {String.quote f}; {migrateUsage}"
      | none => runMigrate true (flags.contains "--allow-destructive") (!flags.contains "--no-backup")
  | _ => return usageErr migrateUsage
where
  runMigrate (apply allowDestructive backup : Bool) : IO Json := do
    if let some c := b.chain then
      return ← chainMigrate b inst sess c apply allowDestructive backup
    let conn ← sess.conn.get
    let backupPath ← do
      if apply && backup then
        let (_, ver) ← instanceInfoOn conn
        pure (some (inst.backupPath b ver (← unixNow conn)))
      else pure none
    match ← migrateOn conn b.specs { apply, allowDestructive, backup := backupPath } with
    | .error e => return e.toJson
    | .ok (plan?, report?) =>
        if apply then
          -- the instance now matches the code (or says why not)
          sess.gate.set (← gateOf b conn)
        match report? with
        | some r => return r.toJson
        | none =>
            let plan := plan?.getD {}
            let old ← readStoredSchema conn
            let changed := changedColumns (old.getD []) b.specs
            let (impact, anonymous, window) ← impactJson b conn changed
            return Json.mkObj [("ok", Json.bool true),
              ("steps", Json.arr (plan.steps.map (Json.str ·.describe)).toArray),
              ("destructive", Json.bool plan.isDestructive),
              ("notes", Json.arr (plan.notes.map Json.str).toArray),
              ("changed", changedJson changed), ("impact", impact), ("unregistered_runs", anonymous),
              ("impact_log", window)]

/-- #77: gate-exempt verbs answer while the gate is set (a drifted
    instance still serves `version` and `migrate`), but not while the
    session is dead: after a failed post-restore reopen the connection
    serves the old, now-unlinked inode, and `version`, `migrate`,
    `backup` and `restore` refuse with the stored reason instead of
    reading or writing the discarded file. -/
private def refuseDead (sess : Session) (serve : IO Json) : IO Json := do
  match ← sess.dead.get with
  | some why => return (DbError.sqlite why).toJson
  | none => serve

private def handleOpen (b : Base) (inst : Instance) (sess : Session) : List String → IO Json
  | [] | ["help"] | ["--help"] => return usageJson b inst
  | ["schema"] =>
      match b.check with
      | .error e => return e.toJson
      | .ok () => return schemaJson b.name b.specs
  | ["version"] => do refuseDead sess (pure (versionJson b (some (← instanceInfoOn (← sess.conn.get)))))
  | "migrate" :: rest => refuseDead sess (migrateJson b inst sess rest)
  | ["backup"] => refuseDead sess (backupJson b inst sess)
  | ["restore", src] => refuseDead sess (restoreJson b inst sess src)
  | args => do
      match command b args with
      | .error m => return usageErr m
      | .ok act =>
          match ← sess.gate.get with
          | some e => return e.toJson
          | none =>
              let conn ← sess.conn.get
              -- a registered query runs under its name, so the log can say
              -- which query recorded which plan
              let queryName? := match args with
                | "query" :: name :: _ => some name
                | ["seed"] => some "seed"
                | _ => none
              conn.queryName.set queryName?
              let r ← act.run conn
              conn.queryName.set none
              match r with
              | .ok j => return j
              | .error e => return e.toJson

/-- The one place argv meets an open instance: every transport (one-shot
    CLI, JSON-lines `serve`, MCP, and HTTP) sends argv here and gets one
    JSON value back. `ok:false` responses carry a `code` (`usage`, or a
    `DbError` code) from which exit codes derive. Typed `DbError`s come
    back as JSON below this boundary, so a raw exception escaping here is
    an unexpected IO failure (#73): `migrate history`'s journal read,
    `unixNow` before a backup, a journal event after a restore's swap.
    The catch turns it into `ok:false` JSON so the transport loops lose
    neither the process (serve/MCP) nor the response (HTTP). -/
def _root_.LeanDb.Base.handle (b : Base) (inst : Instance) (sess : Session) :
    List String → IO Json := fun args =>
  try handleOpen b inst sess args
  catch e => return (DbError.sqlite (toString e)).toJson

/-- Exit code for a `handle` response: 0 ok, 3 usage, 4 schema mismatch,
    2 any other typed error. -/
def exitCodeOf (j : Json) : UInt32 :=
  if (j.getObjValAs? Bool "ok").toOption == some true then 0
  else match (j.getObjValAs? String "code").toOption with
    | some "usage" => 3
    | some "schema_mismatch" | some "unknown_lineage" => 4
    | _ => 2

/-- Max bytes of one request line on the stdio transports — the stdio
    analogue of the HTTP body cap (#21/#23). -/
def defaultMaxLineBytes : Nat := 2 * 1024 * 1024

/-- One request line from a stdio peer. -/
inductive StdLine where
  | /-- EOF with no bytes buffered. -/
    eof
  | /-- A complete line (the newline dropped). -/
    line (s : String)
  | /-- The line's bytes were not valid UTF-8 (#57): the transports answer
      it with an error instead of skipping it, or the peer would hang
      waiting for a response that never comes. -/
    undecodable
  | /-- The line exceeded the budget: it was drained, not buffered. -/
    tooLong

private partial def readLineLoop (h : IO.FS.Stream) (cap : Nat) (chunkSize : USize)
    (pending : IO.Ref ByteArray) (acc : ByteArray) (over : Bool) : IO StdLine := do
  let mut chunk ← pending.get
  pending.set ByteArray.empty
  -- WHY byte-wise: `Handle.read n` is stdio `fread` — on a pipe it blocks
  -- until *n* bytes or EOF, so chunked reads wedge against piped peers
  -- whose line is shorter than the chunk (#96). One byte per read returns
  -- as soon as a byte is available; correctness-first for a line protocol
  -- and the cap bounds the drain cost.
  if chunk.isEmpty then chunk ← h.read 1
  if chunk.isEmpty then
    if over then return .tooLong
    if acc.isEmpty then return .eof
    match String.fromUTF8? acc with
    | some s => return .line s
    | none => return .undecodable
  match chunk.findIdx? (· == 10) with
  | some i =>
      -- the rest of the chunk is the next request's first bytes: never
      -- discard it (a peer may pipeline)
      pending.set (chunk.extract (i + 1) chunk.size)
      if over || acc.size + i > cap then return .tooLong
      match String.fromUTF8? (acc ++ chunk.extract 0 i) with
      | some s => return .line s
      | none => return .undecodable
  | none =>
      -- no newline: keep going, but once the budget is gone, drain and
      -- discard — the bytes are never buffered past `cap`
      if acc.size + chunk.size > cap then readLineLoop h cap chunkSize pending ByteArray.empty true
      else readLineLoop h cap chunkSize pending (acc ++ chunk) over

/-- A line reader over a stdio peer, with a byte budget per request line —
    the stdio analogue of the HTTP body cap (#21/#23). Byte-wise reads
    (#96) with one chunk of pushback, so a pipelined peer's following
    lines survive; a misbehaving peer that emits a newline-less megabyte
    stream gets `tooLong` instead of an OOM. -/
structure LineReader where
  stream : IO.FS.Stream
  cap : Nat := defaultMaxLineBytes
  pending : IO.Ref ByteArray

/-- Open a reader over a stream. -/
def LineReader.new (stream : IO.FS.Stream) (cap : Nat := defaultMaxLineBytes) :
    IO LineReader := do
  let pending ← IO.mkRef ByteArray.empty
  return { stream, cap, pending }

/-- The next request line. EOF right after bytes is that (unterminated)
    line, like `Handle.getLine` would return it. -/
def LineReader.next (r : LineReader) : IO StdLine :=
  readLineLoop r.stream r.cap 1 r.pending ByteArray.empty false

/-- Served mode: JSON-lines over stdio against one persistent connection.
    Each request line is a JSON array of argv strings; each response is one
    JSON object line. EOF ends the session. A drifted instance is served
    too: verbs answer `schema_mismatch` until `["migrate","apply"]`. Only
    genuinely empty lines are skipped silently; an undecodable line is
    answered with an error (#57). -/
def serve (b : Base) (inst : Instance) : IO UInt32 := do
  match ← Session.open b inst with
  | .error e =>
      IO.eprintln e.toJson.compress
      return e.exitCode
  | .ok sess =>
      let stdin ← IO.getStdin
      let out ← IO.getStdout
      let reader ← LineReader.new stdin
      repeat
        match ← reader.next with
        | .eof => break
        | .tooLong =>
            out.putStrLn (usageErr s!"request line exceeds {defaultMaxLineBytes} bytes").compress
            out.flush
        | .undecodable =>
            out.putStrLn (usageErr "request line is not valid UTF-8").compress
            out.flush
        | .line rawLine =>
          let line := rawLine.trimAscii.toString
          if line.isEmpty then continue
          let argv? := Lean.Json.parse line >>= fun j => do
            let arr ← j.getArr?
            arr.toList.mapM (·.getStr?)
          match argv? with
          | .error m =>
              out.putStrLn (usageErr s!"expected a JSON array of argv strings: {m}").compress
          | .ok argv =>
              out.putStrLn (← b.handle inst sess argv).compress
          out.flush
      return 0

/-- The HTTP server, registered by `LeanDb.Http` at initialization so the
    CLI module (which it imports) can reach it. -/
initialize httpServer : IO.Ref (Option (Base → Instance → String → UInt16 → Option String → IO UInt32)) ← IO.mkRef none

/-- The MCP server, registered by `LeanDb.Mcp` the same way. -/
initialize mcpServer : IO.Ref (Option (Base → Instance → IO UInt32)) ← IO.mkRef none

/-- Run one command against a resolved instance. `help`, `schema` and
    `version` touch no file; everything else opens a session. -/
def runOn (b : Base) (inst : Instance) (args : List String) : IO UInt32 := do
  match args with
  | ["serve"] => serve b inst
  | ["serve", "--mcp"] =>
      match ← mcpServer.get with
      | some mcp => mcp b inst
      | none =>
          IO.eprintln (usageErr "MCP serving is not linked into this base").compress
          return 3
  | "serve" :: "--http" :: rest =>
      match ← httpServer.get with
      | some http =>
          let rec parse : List String → Except String (Option String × Option String × Option String)
            | [] => .ok (none, none, none)
            | "--bind" :: h :: r => do let (p, _, t) ← parse r; return (p, some h, t)
            | "--auth-token" :: t :: r => do let (p, h, _) ← parse r; return (p, h, some t)
            | f :: r =>
                if f.startsWith "--" then .error s!"unrecognized serve flag {f}"
                else do let (_, h, t) ← parse r; return (some f, h, t)
          match parse rest with
          | .error m => IO.eprintln (usageErr m).compress; return 3
          | .ok (port?, host?, token?) =>
              match port? with
              | some p =>
                  match portOf p with
                  | .ok port => http b inst (host?.getD "127.0.0.1") port token?
                  | .error m => IO.eprintln (usageErr m).compress; return 3
              | none => IO.eprintln (usageErr "serve --http <port> [--bind <host>] [--auth-token <token>]").compress; return 3
      | none =>
          IO.eprintln (usageErr "HTTP serving is not linked into this base").compress
          return 3
  | [] | ["help"] | ["--help"] =>
      IO.println (usageJson b inst).compress
      return 0
  | ["schema"] =>
      match b.check with
      | .error e => IO.eprintln e.toJson.compress; return e.exitCode
      | .ok () =>
          IO.println (schemaJson b.name b.specs).compress
          return 0
  | ["version"] =>
      IO.println (versionJson b (← instanceInfo inst.path)).compress
      return 0
  | args =>
      -- usage errors must not create the instance file: resolve the
      -- verb first, and only open a session when it is a real command
      let operator :=
        match args with
        | "migrate" :: _ => true
        | ["backup"] => true
        | ["restore", _] => true
        | _ => false
      if !operator then
        match command b args with
        | .error m =>
            IO.eprintln (usageErr m).compress
            return 3
        | .ok _ => pure ()
      match ← Session.open b inst with
      | .error e =>
          IO.eprintln e.toJson.compress
          return e.exitCode
      | .ok sess =>
          let j ← b.handle inst sess args
          let code := exitCodeOf j
          if code == 0 then IO.println j.compress else IO.eprintln j.compress
          return code

/-- The base's `main`: resolve the instance (`--db`, `$LEANDB_DB`, default)
    and run the command. -/
def run (b : Base) (args : List String) : IO UInt32 := do
  match ← Instance.resolve b args with
  | .error m =>
      IO.eprintln (usageErr m).compress
      return 3
  | .ok (inst, args) => runOn b inst args

end LeanDb.Cli
