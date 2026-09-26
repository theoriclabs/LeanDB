import SQLite
import Std.Data.HashMap
import Std.Data.HashSet
import LeanDb.Select
import LeanDb.PlanElab
import LeanDb.Json

namespace LeanDb

/-! # The runtime: connections, `DbM`, and the four verbs

Backed by `leansqlite` (bundled SQLite). SQL text appears only in this file
— it is the compilation target of the typed layer, never its interface.
-/

/-- Audit history is retained unless pruning is explicitly enabled. Impact
    reports inspect only the newest `impactLimit` logged selects. -/
structure LogConfig where
  maxEntries : Option Nat := none
  impactLimit : Nat := 1000
  verbs : LogVerbs := .all
  sampleEvery : Nat := 1
  batch : Bool := false
  registeredOnly : Bool := false
  deriving Repr

/-- Environment settings override the base's policy. Zero retains no logs
    (or skips historical impact scanning); `unlimited` disables retention. -/
def LogConfig.ofSettings (config : LogConfig) (maxEntries impactLimit : Option String)
    (verbs sample batch : Option String := none) :
    Except String LogConfig := do
  let parse := fun (name s : String) => do
    let some n := s.toNat? | throw s!"{name} must be a nonnegative integer"
    if n >= Int64.maxValue.toNatClampNeg then throw s!"{name} is out of range"
    pure n
  let maxEntries ← match maxEntries with
    | none => pure config.maxEntries
    | some "unlimited" => pure none
    | some s => some <$> parse "LEANDB_LOG_MAX" s
  let impactLimit ← match impactLimit with
    | none => pure config.impactLimit
    | some s => parse "LEANDB_LOG_IMPACT_LIMIT" s
  if maxEntries.any (· >= Int64.maxValue.toNatClampNeg) || impactLimit >= Int64.maxValue.toNatClampNeg then
    throw "log limits must be smaller than Int64.maxValue"
  let verbs ← match verbs with
    | none => pure config.verbs
    | some s =>
        let some v := LogVerbs.ofString? s | throw s!"LEANDB_LOG_VERBS must be all|failuresAndPlans|failuresOnly|none"
        pure v
  let sampleEvery ← match sample with
    | none => pure config.sampleEvery
    | some s =>
        let n ← parse "LEANDB_LOG_SAMPLE" s
        if n == 0 then throw "LEANDB_LOG_SAMPLE must be at least 1"
        pure n
  let batch ← match batch with
    | none => pure config.batch
    | some "1" | some "true" | some "yes" => pure true
    | some "0" | some "false" | some "no" => pure false
    | some s => throw s!"LEANDB_LOG_BATCH must be true or false, got {s}"
  return { maxEntries, impactLimit, verbs, sampleEvery, batch, registeredOnly := config.registeredOnly }

/-- Apply environment overrides to an `OpenConfig`. Invalid values fail
    before the database is opened (exit code 3 at the CLI). -/
def OpenConfig.ofEnv (c : OpenConfig) : IO (Except String OpenConfig) := do
  if let .error e := c.checkExtra then return .error e
  let mut c := c
  if let some s ← IO.getEnv "LEANDB_SYNCHRONOUS" then
    let some v := Synchronous.ofString? s | return .error s!"LEANDB_SYNCHRONOUS is not off|normal|full|extra"
    c := { c with synchronous := v }
  if let some s ← IO.getEnv "LEANDB_BUSY_TIMEOUT_MS" then
    let some n := s.toNat? | return .error "LEANDB_BUSY_TIMEOUT_MS must be a nonnegative integer"
    c := { c with busyTimeoutMs := n }
  if let some s ← IO.getEnv "LEANDB_CACHE_SIZE_KIB" then
    let some n := s.toNat? | return .error "LEANDB_CACHE_SIZE_KIB must be a nonnegative integer"
    c := { c with cacheSizeKiB := some n }
  if let some s ← IO.getEnv "LEANDB_MMAP_BYTES" then
    let some n := s.toNat? | return .error "LEANDB_MMAP_BYTES must be a nonnegative integer"
    c := { c with mmapBytes := some n }
  if let some s ← IO.getEnv "LEANDB_WAL_AUTOCHECKPOINT" then
    let some n := s.toNat? | return .error "LEANDB_WAL_AUTOCHECKPOINT must be a nonnegative integer"
    c := { c with walAutocheckpoint := some n }
  return .ok c

def OpenConfig.apply (db : SQLite) (c : OpenConfig) : IO Unit := do
  db.exec s!"PRAGMA busy_timeout = {c.busyTimeoutMs}"
  db.exec s!"PRAGMA synchronous = {c.synchronous.toSql}"
  if let some n := c.cacheSizeKiB then
    db.exec s!"PRAGMA cache_size = -{n}"
  if let some n := c.mmapBytes then
    db.exec s!"PRAGMA mmap_size = {n}"
  if let some n := c.walAutocheckpoint then
    db.exec s!"PRAGMA wal_autocheckpoint = {n}"
  if c.tempStoreMemory then
    db.exec "PRAGMA temp_store = MEMORY"
  for (name, value) in c.extraPragmas do
    db.exec s!"PRAGMA {name} = {value}"

structure Conn where
  raw : SQLite
  queryName : IO.Ref (Option String)
  logConfig : LogConfig := {}
  logWrites : IO.Ref Nat
  txDepth : IO.Ref Nat
  poisoned : IO.Ref (Option String)
  /-- Set on a `SQLITE_OPEN_READONLY` / `query_only` connection (LDB-09). -/
  readOnly : Bool := false
  /-- Effective open-time pragmas, for `Runtime.status` / HTTP startup. -/
  openConfig : OpenConfig := {}
  /-- Plan hashes seen since open (`failuresAndPlans` dedupe). -/
  seenPlans : IO.Ref (Std.HashSet String)
  /-- Sample counter for successful ops. -/
  logSample : IO.Ref Nat

def Conn.ofRaw (raw : SQLite) (logConfig : LogConfig := {}) (openConfig : OpenConfig := {})
    (readOnly : Bool := false) : IO Conn := do
  let queryName ← IO.mkRef none
  let logWrites ← IO.mkRef (0 : Nat)
  let txDepth ← IO.mkRef (0 : Nat)
  let poisoned ← IO.mkRef none
  let seenPlans ← IO.mkRef ({} : Std.HashSet String)
  let logSample ← IO.mkRef (0 : Nat)
  return {
    raw := raw
    queryName := queryName
    logConfig := logConfig
    logWrites := logWrites
    txDepth := txDepth
    poisoned := poisoned
    readOnly := readOnly
    openConfig := openConfig
    seenPlans := seenPlans
    logSample := logSample
  }

/-- Mark the connection unusable: a `ROLLBACK` failed, so the open
    transaction state is unknown and no later verb may run. -/
def Conn.poison (conn : Conn) (why : String) : IO Unit :=
  conn.poisoned.set (some why)

/-- The database monad: a connection, typed errors, IO. -/
abbrev DbM := ReaderT Conn (ExceptT DbError IO)

private def requireWritable (verb : String) : DbM Unit := fun conn =>
  ExceptT.mk do
    if conn.readOnly then return .error (.readOnly verb) else return .ok ()



def DbM.run (conn : Conn) (act : DbM α) : IO (Except DbError α) :=
  (act conn).run

/-- Run a SQLite IO action, converting failures via `onErr`. -/
private def sqliteWith (onErr : IO.Error → DbError) (act : SQLite → IO α) : DbM α :=
  fun conn => ExceptT.mk do
    match ← conn.poisoned.get with
    | some why => return .error (.poisoned why)
    | none =>
      try (.ok <$> act conn.raw) catch e => pure (.error (onErr e))

private def sqlite (act : SQLite → IO α) : DbM α :=
  sqliteWith (fun e => .sqlite (toString e)) act

/-- Keep the newest N entries, including when ids have gaps. The OFFSET
    scan runs only at open or at a retention batch boundary, not per verb. -/
private def pruneLogRaw (db : SQLite) (keep : Nat) : IO Nat := do
  if keep >= Int64.maxValue.toNatClampNeg then
    throw <| IO.userError "log retention limit is out of range"
  if keep == 0 then
    db.exec "DELETE FROM _leandb_log"
  else
    let stmt ← db.prepare "DELETE FROM _leandb_log WHERE id <= (SELECT id FROM _leandb_log ORDER BY id DESC LIMIT 1 OFFSET ?)"
    stmt.bindInt64 1 (Int64.ofNat keep)
    stmt.exec
  return (← db.changes).toNatClampNeg

/-- Explicitly prune audit history without changing the connection's policy. -/
def pruneLog (keep : Nat) : DbM Nat := sqlite (pruneLogRaw · keep)

private def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- SQLite reports every constraint violation as primary code 19; the
    message distinguishes the kinds — but an FK failure means different
    things per verb (dangling `Ref` on insert/update, referenced-row on
    delete), so the caller says what it means via `fkError`.

    TEXT-SHAPE DEPENDENCY. The seam that separates `.missingRef`,
    `.restricted` and `.duplicate` from a catch-all `.sqlite` *should* be
    SQLite's extended result code — SQLITE_CONSTRAINT_FOREIGNKEY 787,
    _UNIQUE 2067, _PRIMARYKEY 1555, each `19 ||| (subtype <<< 8)`, so the
    low byte stays 19. It is not: bundled `leansqlite` passes
    `sqlite3_step`/`sqlite3_exec`'s return value straight to
    `IO.Error.otherError` (bindings/leansqlite.c) and binds neither
    `sqlite3_extended_result_codes` nor `sqlite3_extended_errcode` — and
    SQLite has no PRAGMA for either — so extended codes stay off and only
    19 ever arrives. That leaves the human-readable message, which is not
    a stable API, deciding which typed error the caller sees.

    So: match the extended codes anyway (free today, correct the day
    upstream binds `sqlite3_extended_result_codes`), and fall back to a
    case-insensitive substring match, which survives the re-wordings that
    `startsWith` on "FOREIGN KEY" / "UNIQUE" would silently downgrade. -/
private def constraintError (table : String) (fkError : DbError) (e : IO.Error) : DbError :=
  match e with
  | .otherError code details =>
      if code % 256 != 19 then .sqlite (toString e) else
      let msg := details.toLower
      -- the full phrase, not any occurrence of "foreign key": escaped
      -- identifiers may carry spaces, so a column literally named
      -- «foreign key» puts that substring inside "UNIQUE constraint
      -- failed: t.foreign key" — the bare substring would misroute a
      -- UNIQUE violation to `.missingRef`. SQLite's FK violations read
      -- exactly "FOREIGN KEY constraint failed" (no table/column names).
      if code == 787 || hasSub msg "foreign key constraint failed" then fkError
      -- _UNIQUE and _PRIMARYKEY both read "UNIQUE constraint failed: t.c".
      else if code == 2067 || code == 1555 || hasSub msg "unique" || hasSub msg "primary key" then
        .duplicate table details
      else .sqlite s!"constraint: {details}"
  | e => .sqlite (toString e)

def bindCol (stmt : SQLite.Stmt) (idx : Int32) : Col → IO Unit
  | .int v => stmt.bindInt64 idx v
  | .text v => stmt.bindText idx v
  | .real v =>
      /- SQLite stores a bound NaN as NULL: against a NOT NULL REAL
         column the write fails with a misleading constraint error, and
         against a nullable one it "succeeds" but the value silently
         reads back `none`. Refuse it at the write boundary instead —
         a NaN has no SQLite representation that survives a round trip.
         The same refusal covers the infinities: they bind and store,
         but every JSON surface renders them as the *strings*
         "Infinity"/"-Infinity", so the column stops being a REAL the
         moment it is read back as JSON (see `Col.fromJson`). A REAL
         value that cannot round-trip as a REAL is refused at the
         boundary. -/
      if v.isNaN || v.isInf then
        throw <| IO.userError s!"REAL value is {if v.isNaN then "NaN" else "infinite"} (it has no SQLite representation that survives a round trip as a REAL)"
      else stmt.bindFloat idx v
  | .null => stmt.bindNull idx

/-- Bind row values starting at parameter `first` (bind params are 1-based). -/
def bindCols (stmt : SQLite.Stmt) (first : Nat) (cols : Array Col) : IO Unit := do
  for h : i in [0:cols.size] do
    bindCol stmt (Int32.ofNat (first + i)) cols[i]

/-- A column we cannot represent (`none`) is a decode failure like any
    other; the caller names the table and field it came from. -/
def readCol (stmt : SQLite.Stmt) (i : Int32) : IO (Option Col) := do
  match ← stmt.columnType i with
  | .integer => return some (.int (← stmt.columnInt64 i))
  | .float => return some (.real (← stmt.columnDouble i))
  | .text => return some (.text (← stmt.columnText i))
  | .null => return some .null
  | .blob => return none

/-- Read `n` result columns starting at `first`. `label i` names the
    `(table, field)` column `i` was selected from — consulted only when a
    value cannot be represented, so a row decode allocates nothing for it. -/
def readRow (stmt : SQLite.Stmt) (first n : Nat) (label : Nat → String × String) :
    IO (Except DbError (Array Col)) := do
  let mut cols : Array Col := Array.mkEmpty n
  for i in [0:n] do
    match ← readCol stmt (Int32.ofNat (first + i)) with
    | some c => cols := cols.push c
    | none =>
        let (table, field) := label i
        return .error (.decode table field "BLOB columns are not supported")
  return .ok cols

/-- Read the current result row as `id` (column 0) plus the entity columns. -/
private def readStored (α : Type) [Entity α] (stmt : SQLite.Stmt) :
    IO (Except DbError (Stored α)) := do
  let id ← stmt.columnInt64 0
  let fields := Entity.fields (α := α)
  let label (i : Nat) : String × String :=
    (Entity.tableName α, (fields[i]?.map Entity.fieldName).getD "?")
  match ← readRow stmt 1 fields.size label with
  | .error e => return .error e
  | .ok cols => return (Entity.decode cols).map (⟨⟨id⟩, ·⟩)

/-- Lift a typed result into `DbM`. -/
def DbM.ofExcept (r : Except DbError α) : DbM α :=
  fun _ => ExceptT.mk (pure r)

/-- Append to `_leandb_log`. Best-effort: the log never fails an operation.
    Policy (`LogVerbs`, sampling) is applied here so the default `.all` /
    `sampleEvery = 1` path is byte-identical to 0.3.x. -/
private def logOp (verb detail : String) (ok : Bool) (error : Option String) (rows : Nat)
    (plan : Option String) : DbM Unit := fun conn => ExceptT.mk do
  if conn.logConfig.maxEntries == some 0 then return .ok ()
  let cfg := conn.logConfig
  let should ←
    match cfg.verbs with
    | .none => pure false
    | .failuresOnly => pure (!ok)
    | .failuresAndPlans =>
        if !ok then pure true
        else match plan with
          | none => pure false
          | some p =>
              let seen ← conn.seenPlans.get
              if seen.contains p then pure false
              else
                conn.seenPlans.set (seen.insert p)
                pure true
    | .all =>
        if !ok then pure true
        else if cfg.registeredOnly then
          pure (← conn.queryName.get).isSome
        else if cfg.sampleEvery <= 1 then pure true
        else do
          let n := (← conn.logSample.get) + 1
          conn.logSample.set (if n >= cfg.sampleEvery then 0 else n)
          pure (n >= cfg.sampleEvery)
  unless should do return .ok ()
  try
    let query ← conn.queryName.get
    let stmt ← conn.raw.prepare
      "INSERT INTO _leandb_log (verb, detail, ok, error, rows, plan, query) VALUES (?, ?, ?, ?, ?, ?, ?)"
    stmt.bindText 1 verb
    stmt.bindText 2 detail
    stmt.bindInt64 3 (if ok then 1 else 0)
    match error with
    | some e => stmt.bindText 4 e
    | none => stmt.bindNull 4
    stmt.bindInt64 5 (Int64.ofNat rows)
    match plan with
    | some p => stmt.bindText 6 p
    | none => stmt.bindNull 6
    match query with
    | some q => stmt.bindText 7 q
    | none => stmt.bindNull 7
    stmt.exec
    if let some keep := conn.logConfig.maxEntries then
      let writes := (← conn.logWrites.get) + 1
      conn.logWrites.set writes
      -- Bound steady-state growth without scanning the retention window
      -- after every operation. Small windows get proportionally smaller batches.
      if writes >= min 128 (max 1 keep) then
        discard <| pruneLogRaw conn.raw keep
        conn.logWrites.set 0
    return .ok ()
  catch _ => return .ok ()

/-- Run an operation and log it: verb, detail, outcome, row count, and for
    a select the plan as data. The query log is the audit trail and the
    agent's episodic memory (plan.md §4.4) — on by default. -/
private def withLog (verb detail : String) (count : α → Nat) (act : DbM α)
    (plan : Option String := none) : DbM α := do
  match ← fun conn => ExceptT.mk (.ok <$> (act conn).run) with
  | .ok a =>
      logOp verb detail true none (count a) plan
      return a
  | .error e =>
      logOp verb detail false (some e.code) 0 plan
      throw e

private def liftExcept (r : Except DbError α) : DbM α := DbM.ofExcept r

private def quoteId (s : String) : String := quoteIdent s

private def columnList (α : Type) [Entity α] : String :=
  String.intercalate ", " ("id" :: (Entity.columns α).toList.map (quoteId ·.name))

private def placeholders (n : Nat) : String :=
  String.intercalate ", " (List.replicate n "?")

/-! ## Child tables (LEP-0003 D)

A parent's child lists live in their own tables and are *part of the
parent's value*: every read reattaches them, every write owns them.
Reads cost one engine-internal statement per child table per fetch —
`WHERE parent IN (…)` over the fetched parents, chunked — never one per
row. Writes run inside a transaction. -/

/-- Run `act` inside `BEGIN DEFERRED … COMMIT` (or `begin` when given).
    Reentrant: a nested call joins the open transaction under a SAVEPOINT
    so a multi-statement verb that fails is atomic and does not leave
    partial effects for an outer commit to keep (LDB-20). -/
private def transaction (act : DbM α) (begin : String := "BEGIN DEFERRED") : DbM α :=
    fun conn => ExceptT.mk do
  let exec (sql : String) : IO (Except DbError Unit) :=
    try conn.raw.exec sql; pure (.ok ()) catch e => pure (.error (.sqlite (toString e)))
  match ← conn.poisoned.get with
  | some why => return .error (.poisoned why)
  | none =>
  let depth ← conn.txDepth.get
  let savepoint := s!"_leandb_op_{depth}"
  match ← (if depth == 0 then exec begin else exec s!"SAVEPOINT {savepoint}") with
  | .error e => return .error e
  | .ok () =>
  conn.txDepth.set (depth + 1)
  let undo : IO (Option DbError) := do
    let r ←
      if depth == 0 then exec "ROLLBACK"
      else
        match ← exec s!"ROLLBACK TO SAVEPOINT {savepoint}" with
        | .error e => pure (.error e)
        | .ok () => exec s!"RELEASE SAVEPOINT {savepoint}"
    match r with
    | .ok () => return none
    | .error re =>
        let why := s!"rollback of {if depth == 0 then "transaction" else savepoint} \
failed: {re.message}"
        conn.poison why
        return some (.poisoned why)
  let finish (r : Except DbError α) : IO (Except DbError α) := do
    conn.txDepth.set depth
    match r with
    | .ok a =>
        let sealed' ←
          if depth == 0 then exec "COMMIT"
          else exec s!"RELEASE SAVEPOINT {savepoint}"
        match sealed' with
        | .ok () => return .ok a
        | .error e =>
            match ← undo with
            | some pe => return .error pe
            | none => return .error e
    | .error e =>
        match ← undo with
        | some pe => return .error pe
        | none => return .error e
  let r ← try (act conn).run catch e => pure (.error (.sqlite (toString e)))
  finish r

/-- A consistent deferred read snapshot (`BEGIN DEFERRED … COMMIT`).
    Nested calls join the open transaction. Multi-statement reads that
    must see one WAL snapshot use this; the engine's own `get` /
    `fetchAll` / `selectP` already do. Public so adapters need not
    rebuild it (LDB-24). -/
def readSnapshot (act : DbM α) : DbM α := transaction act

/-- How many parent ids one child fetch names: SQLite's default parameter
    limit is far above this, and the statement text stays small. -/
private def childChunk : Nat := 500

/-- Attach every child list of `α` to `rows`: per child table, one
    `SELECT parent, position, <record columns> … WHERE parent IN (…) ORDER
    BY parent, position` per chunk of parent ids, grouped by parent, then
    `ChildLink.attach` (which also checks derived columns computed from
    the list). Order and length of `rows` are preserved; an entity without
    children costs nothing. -/
private def attachLists (α : Type) [Entity α] (rows : Array (Stored α)) :
    DbM (Array (Stored α)) := do
  let links := Entity.children (α := α)
  if links.isEmpty || rows.isEmpty then return rows
  -- distinct parent ids (a joined result repeats a parent per product row)
  let ids := (rows.map (·.id.toInt64)).qsort (· < ·)
  let ids := ids.foldl (init := #[]) fun acc i =>
    if acc.back? == some i then acc else acc.push i
  let mut rows := rows
  for link in links do
    let cols := link.spec.columns
    let parentCol := cols.getD 0 default |>.name
    let positionCol := cols.getD 1 default |>.name
    let names := String.intercalate ", " (cols.toList.map (quoteId ·.name))
    let n := link.recordColumns.size
    let label (i : Nat) : String × String := (link.table, ((cols[i + 2]?).map (·.name)).getD "?")
    let mut groups : Std.HashMap Int64 (Array (Nat × Array Col)) := {}
    for start in [0:ids.size:childChunk] do
      let chunk := ids.extract start (start + childChunk)
      let sql := s!"SELECT {names} FROM {quoteId link.table} WHERE {quoteId parentCol} IN ({placeholders chunk.size}) ORDER BY {quoteId parentCol}, {quoteId positionCol}"
      let raw ← sqlite fun db => do
        let stmt ← db.prepare sql
        for h : i in [0:chunk.size] do stmt.bindInt64 (Int32.ofNat (i + 1)) chunk[i]
        let mut out : Array (Int64 × Nat × Except DbError (Array Col)) := #[]
        repeat
          if ← stmt.step then
            let parent ← stmt.columnInt64 0
            let position ← stmt.columnInt64 1
            out := out.push (parent, position.toNatClampNeg, ← readRow stmt 2 n label)
          else break
        return out
      for (parent, position, r) in raw do
        let cols ← liftExcept r
        groups := groups.insert parent ((groups.getD parent #[]).push (position, cols))
    rows ← rows.mapM fun r => do
      let v ← liftExcept (link.attach (groups.getD r.id.toInt64 #[]) r.val)
      return ⟨r.id, v⟩
  return rows

/-- The entity's declared invariant (LDB-16) on one value. -/
private def checkInvariant [Entity α] (a : α) : DbM Unit :=
  match Entity.invariant (α := α) with
  | some (name, holds) =>
      if holds a then pure () else throw (.invariant (Entity.tableName α) name)
  | none => pure ()

/-- Every field must fit in its SQLite column (LDB-18). A `Nat` above
    `Int64.maxValue` is refused rather than wrapping. -/
private def checkSqlRange [Entity α] (a : α) : DbM Unit :=
  (Entity.fields (α := α)).forM fun f =>
    match (Entity.codec f).toSql? (Entity.get f a) with
    | some _ => pure ()
    | none => throw (.decode (Entity.tableName α) (Entity.fieldName f)
        "value is outside the range SQLite INTEGER can store")

/-- Every typed read ends here: the child lists attached (`attachLists`),
    then the entity's invariant checked on each whole value (LDB-16). A row
    that fails is refused with `.invariant`, never returned. -/
private def attachChildren (α : Type) [Entity α] (rows : Array (Stored α)) :
    DbM (Array (Stored α)) := do
  let rows ← attachLists α rows
  if (Entity.invariant (α := α)).isSome then rows.forM (checkInvariant ·.val)
  return rows

/-- Write child rows of one list for parent `id`, at positions `start…`:
    the record's columns after `parent` and `position`. -/
private def insertChildRows [Entity α] (link : ChildLink α) (id : Int64) (start : Nat)
    (rows : Array (Array Col)) : DbM Unit := do
  if rows.isEmpty then return
  let names := String.intercalate ", " (link.spec.columns.toList.map (quoteId ·.name))
  let sql := s!"INSERT INTO {quoteId link.table} ({names}) VALUES ({placeholders link.spec.columns.size})"
  sqliteWith (constraintError link.table (.missingRef link.table)) fun db => do
    let stmt ← db.prepare sql
    for h : i in [0:rows.size] do
      stmt.reset
      stmt.clearBindings
      stmt.bindInt64 1 id
      stmt.bindInt64 2 (Int64.ofNat (start + i))
      bindCols stmt 3 rows[i]
      stmt.exec

/-- Write the child rows of one list for parent `id`: positions `0…`. -/
private def insertChildren [Entity α] (link : ChildLink α) (id : Int64) (a : α) : DbM Unit :=
  insertChildRows link id 0 (link.rows a)

/-- `INSERT` a value; returns it with its assigned identity. A parent with
    child lists writes its own row and then every child row, in one
    transaction. -/
def insert (α : Type) [Entity α] (a : α) : DbM (Stored α) := withLog "insert" (Entity.tableName α) (fun _ => 1) do
  requireWritable "insert"
  checkInvariant a
  checkSqlRange a
  let spec := Entity.spec α
  let links := Entity.children (α := α)
  let names := String.intercalate ", " (spec.columns.toList.map (quoteId ·.name))
  let sql := if spec.columns.isEmpty then
    s!"INSERT INTO {quoteId spec.name} DEFAULT VALUES"
  else
    s!"INSERT INTO {quoteId spec.name} ({names}) VALUES ({placeholders spec.columns.size})"
  let act : DbM (Stored α) := do
    sqliteWith (constraintError spec.name (.missingRef spec.name)) fun db => do
      let stmt ← db.prepare sql
      unless spec.columns.isEmpty do bindCols stmt 1 (Entity.encode a)
      stmt.exec
    let id ← sqlite (·.lastInsertRowId)
    for link in links do insertChildren link id a
    return ⟨⟨id⟩, a⟩
  if links.isEmpty then act else transaction act

/-- Fetch one row by typed identity. Parent row and child lists share one
    deferred snapshot so a concurrent writer cannot tear them. -/
def get [Entity α] (id : Id α) : DbM (Option (Stored α)) := transaction do
  let sql := s!"SELECT {columnList α} FROM {quoteId (Entity.tableName α)} WHERE id = ?"
  let row ← sqlite fun db => do
    let stmt ← db.prepare sql
    stmt.bindInt64 1 id.toInt64
    if ← stmt.step then some <$> readStored α stmt else return none
  match row with
  | none => return none
  | some r => do
      let rows ← attachChildren α #[← liftExcept r]
      return rows[0]?

/-- Every row of `α`'s table, in id order. Parent rows and child lists
    share one deferred snapshot. -/
def fetchAll (α : Type) [Entity α] : DbM (Array (Stored α)) := transaction do
  let sql := s!"SELECT {columnList α} FROM {quoteId (Entity.tableName α)} ORDER BY id"
  let rows ← sqlite fun db => do
    let stmt ← db.prepare sql
    let mut out := #[]
    repeat
      if ← stmt.step then out := out.push (← readStored α stmt) else break
    return out
  attachChildren α (← rows.mapM liftExcept)

/-- Compare-and-swap update: `SET` to `new` only where the row still equals
    `old`, id included. A lost race is a typed `.stale`, never a silent
    clobber. `IS` (not `=`) so `NULL` columns pin correctly. The CAS is on
    the parent's own columns; once it holds, every child list is replaced
    wholesale (`DELETE … WHERE parent = ?`, then re-inserted), in the same
    transaction. The CAS does not see the child lists: a writer whose
    parent columns match `old` but whose lists moved on is not refused.
    To grow a list against a stale read, use `append` (LDB-15). -/
def update [Entity α] (old : Stored α) (new : α) : DbM (Stored α) := withLog "update" (Entity.tableName α) (fun _ => 1) do
  requireWritable "update"
  checkInvariant new
  checkSqlRange new
  let spec := Entity.spec α
  let links := Entity.children (α := α)
  let cas : DbM Unit := do
    if spec.columns.isEmpty then
      let changed ← sqlite fun db => do
        let stmt ← db.prepare s!"UPDATE {quoteId spec.name} SET id = id WHERE id = ?"
        stmt.bindInt64 1 old.id.toInt64
        stmt.exec
        db.changes
      if changed == 0 then throw (.notFound spec.name old.id.toInt64)
      return
    let sets := String.intercalate ", " (spec.columns.toList.map (s!"{quoteId ·.name} = ?"))
    let pins := String.intercalate " AND " (spec.columns.toList.map (s!"{quoteId ·.name} IS ?"))
    let sql := s!"UPDATE {quoteId spec.name} SET {sets} WHERE id = ? AND {pins}"
    let n := spec.columns.size
    let changed ← sqliteWith (constraintError spec.name (.missingRef spec.name)) fun db => do
      let stmt ← db.prepare sql
      bindCols stmt 1 (Entity.encode new)
      stmt.bindInt64 (Int32.ofNat (n + 1)) old.id.toInt64
      bindCols stmt (n + 2) (Entity.encode old.val)
      stmt.exec
      db.changes
    if changed == 0 then
      match ← get old.id with
      | some _ => throw (.stale spec.name old.id.toInt64)
      | none => throw (.notFound spec.name old.id.toInt64)
  let act : DbM (Stored α) := do
    cas
    for link in links do
      let parentCol := (link.spec.columns.getD 0 default).name
      sqlite fun db => do
        let stmt ← db.prepare s!"DELETE FROM {quoteId link.table} WHERE {quoteId parentCol} = ?"
        stmt.bindInt64 1 old.id.toInt64
        stmt.exec
      insertChildren link old.id.toInt64 new
    return ⟨old.id, new⟩
  if links.isEmpty then act else transaction act

/-- `update` for a value that grows its child lists (LDB-15): each child
    list of `new` continues the same list of `old`. Only the added child
    rows are written, at the positions after the stored ones; no stored
    child row is rewritten. The parent's own columns are written as
    `update` writes them, so a column derived from a list can move with it.

    Refused with `.stale` when the parent's columns, or the length of any
    child list, changed since `old` was read. It runs under `BEGIN
    IMMEDIATE`, so the check and the write hold one write lock; a writer in
    another process that wins anyway meets the `(parent, position)` UNIQUE
    index, and that is `.stale` too. A list in `new` that does not continue
    the stored one is `.notAppend`: that is an `update`. -/
def append [Entity α] (old : Stored α) (new : α) : DbM (Stored α) :=
    withLog "append" (Entity.tableName α) (fun _ => 1) do
  requireWritable "append"
  let spec := Entity.spec α
  let table := spec.name
  let id := old.id.toInt64
  let mut added : Array (ChildLink α × Nat × Array (Array Col)) := #[]
  for link in Entity.children (α := α) do
    let before := link.rows old.val
    let after := link.rows new
    unless before.size ≤ after.size && after.extract 0 before.size == before do
      throw (.notAppend link.table "the list does not continue the stored one")
    added := added.push (link, before.size, after.extract before.size after.size)
  checkInvariant new
  checkSqlRange new
  transaction (begin := "BEGIN IMMEDIATE") do
    -- the parent: `update`'s compare-and-swap against `old`
    let pins := spec.columns.toList.map fun c => s!"{quoteId c.name} IS ?"
    let sets := spec.columns.toList.map fun c => s!"{quoteId c.name} = ?"
    let setSql := if sets.isEmpty then "id = id" else String.intercalate ", " sets
    let n := spec.columns.size
    let changed ← sqliteWith (constraintError table (.missingRef table)) fun db => do
      let stmt ← db.prepare
        s!"UPDATE {quoteId table} SET {setSql} WHERE {String.intercalate " AND " ("id = ?" :: pins)}"
      bindCols stmt 1 (Entity.encode new)
      stmt.bindInt64 (Int32.ofNat (n + 1)) id
      bindCols stmt (n + 2) (Entity.encode old.val)
      stmt.exec
      db.changes
    if changed == 0 then
      let present ← sqlite fun db => do
        let stmt ← db.prepare s!"SELECT 1 FROM {quoteId table} WHERE id = ?"
        stmt.bindInt64 1 id
        stmt.step
      if present then throw (.stale table id) else throw (.notFound table id)
    -- each list: still `old`'s length, then only the new rows
    for (link, stored, rows) in added do
      let parentCol := (link.spec.columns.getD 0 default).name
      let count ← sqlite fun db => do
        let stmt ← db.prepare
          s!"SELECT COUNT(*) FROM {quoteId link.table} WHERE {quoteId parentCol} = ?"
        stmt.bindInt64 1 id
        discard stmt.step
        stmt.columnInt64 0
      unless count.toNatClampNeg == stored do throw (.stale table id)
      try insertChildRows link id stored rows
      catch
        | .duplicate .. => throw (.stale table id)
        | e => throw e
    return ⟨old.id, new⟩

/-- Delete by typed identity. Rows referenced elsewhere refuse with
    `.restricted` (FK RESTRICT) — destruction is loud. A parent's own child
    rows go with it (the child FK cascades: they are part of its value),
    while any other table's `Ref` to it still restricts. -/
def delete [Entity α] (id : Id α) : DbM Unit := withLog "delete" (Entity.tableName α) (fun _ => 1) do
  requireWritable "delete"
  let table := Entity.tableName α
  let changed ← sqliteWith (constraintError table (.restricted table id.toInt64)) fun db => do
    let stmt ← db.prepare s!"DELETE FROM {quoteId table} WHERE id = ?"
    stmt.bindInt64 1 id.toInt64
    stmt.exec
    db.changes
  if changed == 0 then throw (.notFound table id.toInt64)

/-- Rows of `α`'s table matching a pushed predicate, in id order. The
    table is aliased `t0` and every index of the predicate renders as
    `t0` — only conjuncts over `α`'s own columns may reach here
    (`Pred.forTable`), and a quantifier among them needs the alias to
    name its own table. -/
def fetchFiltered (α : Type) [Entity α] {ts : List Type} (pred : Pred ts)
    (limit : Option Nat := none) (order : Array (Order ts) := #[])
    (window : Window := {}) : DbM (Array (Stored α)) := transaction do
  if let .error e := window.check then throw e
  let cap := window.limit <|> limit
  if pred.isTrivial && cap.isNone && window.offset == 0 && order.isEmpty then
    return ← fetchAll α
  let (whereSql, binds) := pred.render fun _ => "t0"
  let orderSql :=
    if order.isEmpty then " ORDER BY id"
    else
      let keys := order.toList.map fun o => s!"{quoteId o.column} {o.dir.sql}"
      s!" ORDER BY {String.intercalate ", " keys}, id ASC"
  let mut tail := ""
  let mut extra : Array LeanDb.Col := #[]
  if let some n := cap then
    tail := tail ++ " LIMIT ?"
    extra := extra.push (.int (Int64.ofNat n))
  if window.offset != 0 then
    tail := tail ++ " OFFSET ?"
    extra := extra.push (.int (Int64.ofNat window.offset))
  let sql := s!"SELECT {columnList α} FROM {quoteId (Entity.tableName α)} AS t0 WHERE {whereSql}{orderSql}{tail}"
  let rows ← sqlite fun db => do
    let stmt ← db.prepare sql
    bindCols stmt 1 binds
    bindCols stmt (binds.size + 1) extra
    let mut out := #[]
    repeat
      if ← stmt.step then out := out.push (← readStored α stmt) else break
    return out
  attachChildren α (← rows.mapM liftExcept)

/-- The live database as a row `Source`, ignoring plans. Rows come with
    their child lists attached, so `selectSpec` over it — the reference
    semantics — sees whole values. -/
def dbSource : Source DbM := ⟨fun _ α _ => fetchAll α⟩

/-- The live database narrowed by a pushed plan's per-table conjuncts. -/
def plannedSource {ts : List Type} (pushed : Pred ts)
    (order : Array (Order ts) := #[]) (window : Window := {}) : Source DbM :=
  ⟨fun i α _ =>
    if i == 0 then fetchFiltered α (pushed.forTable i) none order window
    else fetchFiltered α (pushed.forTable i)⟩

/-- ON clause for joining table `i`: cross-table conjuncts that mention
    `i` and only earlier tables. `1` if none (a remaining cartesian). -/
private def joinOnSql {ts : List Type} (p : Pred ts) (i : Nat) : String :=
  let ons := p.conjuncts.filter fun c =>
    c.hasJoin && c.tables.contains i && c.tables.all (fun t => t <= i)
  if ons.isEmpty then "1"
  else String.intercalate " AND " (ons.map fun c => (c.render Pred.tAlias).1)

/-- `FROM t0 JOIN t1 ON <fk> JOIN t2 ON …` — join conditions are the
    plan's cross-table conjuncts. -/
private def joinedFromSql (ts : List Type) [RowsOf ts] (p : Pred ts) : String :=
  let specs := RowsOf.specs ts
  match specs.zipIdx with
  | [] => ""
  | (s0, _) :: rest =>
      rest.foldl (init := s!"{quoteId s0.name} AS t0") fun acc (spec, i) =>
        acc ++ s!" JOIN {quoteId spec.name} AS t{i} ON {joinOnSql p i}"

/-- Joined execution: one SQL statement, `JOIN` on the plan's cross-table
    conjuncts (the foreign-key column for a typed `join`). Used when the
    plan relates tables — the pushed joins cut the product in SQL instead
    of materializing it client-side. `pushed` is opaque-free
    (`Pred.approx`). An exact plan may also push `order`/`window`. -/
def selectJoined (ts : List Type) [RowsOf ts] (pushed : Pred ts)
    (where' : Rows ts → Bool) (sortBy : SortBy (Rows ts))
    (order : Array (Order ts) := #[]) (window : Window := {}) :
    DbM (Array (Rows ts)) := do
  let specs := RowsOf.specs ts
  let sel := specs.zipIdx.map fun (spec, i) =>
    String.intercalate ", " (s!"t{i}.id" :: spec.columns.toList.map fun c => s!"t{i}.{quoteId c.name}")
  let idOrder := specs.zipIdx.map fun (_, i) => s!"t{i}.id"
  let orderSql :=
    if order.isEmpty then
      s!" ORDER BY {String.intercalate ", " idOrder}"
    else
      let keys := order.toList.map fun o => s!"t0.{quoteId o.column} {o.dir.sql}"
      s!" ORDER BY {String.intercalate ", " (keys ++ idOrder)}"
  let (whereSql, binds) := pushed.renderT
  let mut tail := ""
  let mut extra : Array LeanDb.Col := #[]
  if let some n := window.limit then
    tail := tail ++ " LIMIT ?"
    extra := extra.push (.int (Int64.ofNat n))
  if window.offset != 0 then
    tail := tail ++ " OFFSET ?"
    extra := extra.push (.int (Int64.ofNat window.offset))
  let sql := s!"SELECT {String.intercalate ", " sel} FROM {joinedFromSql ts pushed} " ++
    s!"WHERE {whereSql}{orderSql}{tail}"
  -- One label per selected column, in the same order as `sel` above, so a
  -- bad value names the table and field it actually came from.
  let labels : Array (String × String) := specs.foldl (init := #[]) fun acc spec =>
    acc.push (spec.name, "id") ++ (spec.columns.map fun c => (spec.name, c.name))
  let raw ← sqlite fun db => do
    let stmt ← db.prepare sql
    bindCols stmt 1 binds
    bindCols stmt (binds.size + 1) extra
    let mut out : Array (Except DbError (Array Col)) := #[]
    repeat
      if ← stmt.step then
        out := out.push (← readRow stmt 0 labels.size (labels.getD · ("?", "?")))
      else break
    return out
  let rows ← raw.mapM fun r => do
    let cols ← liftExcept r
    liftExcept (RowsOf.decodeFrom (ts := ts) cols 0)
  let rows ← RowsOf.mapTables (ts := ts) (fun α _ rows => attachChildren α rows) rows
  return finishRows ts rows where' sortBy

/-- Run a pushed plan and a decider: the opaque-free `pushed` ships to
    SQL — the joined executor when it relates tables, per-table fetches
    otherwise — and `where'` is applied to what comes back. The one path
    under both `select` and `selectP`, so they cannot diverge.

    `order`/`window` are pushed into SQL when `exact` (no residual),
    including foreign-key joins (`JOIN` + `LIMIT`/`OFFSET`). Otherwise
    the window is applied in Lean after `where'`, so a `LIMIT 1` cannot
    miss a later row that only the residual accepts (LDB-17). -/
private def runPlanned (ts : List Type) [RowsOf ts] (pushed : Pred ts)
    (where' : Rows ts → Bool) (sortBy : SortBy (Rows ts))
    (order : Array (Order ts) := #[]) (window : Window := {})
    (exact : Bool := false) : DbM (Array (Rows ts)) := do
  let pushWindow := exact
  let rows ←
    if pushed.hasJoin then
      selectJoined ts pushed where' sortBy order (if pushWindow then window else {})
    else
      selectSpec ts (plannedSource pushed order (if pushWindow then window else {}))
        where' (if order.isEmpty then sortBy else .preserve)
  if pushWindow then return rows else return window.apply rows

private def selectDetail (ts : List Type) [RowsOf ts] (p : Pred ts) : String :=
  s!"{String.intercalate "×" ((RowsOf.specs ts).map (·.name))} | {p.describe}"

/-- A column reference as JSON: the table at its row position and its name. -/
private def colJson (names : Nat → String) {ts : List Type} {τ : Type} {i : ColCodec τ}
    (c : Pred.Col ts τ i) : Lean.Json :=
  Lean.Json.mkObj [("table", Lean.Json.str (names c.tableIdx)), ("column", Lean.Json.str c.name)]

/-- The plan as data (the log stores this next to `describe`'s text): one
    object per node, values in their stored encoding, the residual as
    `{"opaque":true}`. Quantifiers carry the child table and their body
    over `child :: ts`. -/
partial def Pred.toJsonWith {ts : List Type} (names : Nat → String) : Pred ts → Lean.Json
  | .tt => Lean.Json.mkObj [("kind", Lean.Json.str "tt")]
  | .ff => Lean.Json.mkObj [("kind", Lean.Json.str "ff")]
  | .eq (i := i) c op v =>
      Lean.Json.mkObj [("kind", Lean.Json.str "eq"), ("col", colJson names c),
        ("op", Lean.Json.str op.sql), ("value", (@toCol _ i v).toJson)]
  | .ord (i := i) (so := _) c op v =>
      Lean.Json.mkObj [("kind", Lean.Json.str "ord"), ("col", colJson names c),
        ("op", Lean.Json.str op.sql), ("value", (@toCol _ i v).toJson)]
  | .eq2 a op b =>
      Lean.Json.mkObj [("kind", Lean.Json.str "eq2"), ("left", colJson names a),
        ("op", Lean.Json.str op.sql), ("right", colJson names b)]
  | .ord2 (so := _) a op b =>
      Lean.Json.mkObj [("kind", Lean.Json.str "ord2"), ("left", colJson names a),
        ("op", Lean.Json.str op.sql), ("right", colJson names b)]
  | .isNull c => Lean.Json.mkObj [("kind", Lean.Json.str "isNull"), ("col", colJson names c)]
  | .isNotNull c => Lean.Json.mkObj [("kind", Lean.Json.str "isNotNull"), ("col", colJson names c)]
  | .bit (ce := ce) c a set =>
      Lean.Json.mkObj [("kind", Lean.Json.str "bit"), ("col", colJson names c),
        ("variant", Lean.Json.str (@ClosedEnum.encodeName _ ce a)), ("set", Lean.Json.bool set)]
  | .and a b => Lean.Json.mkObj [("kind", Lean.Json.str "and"),
      ("a", a.toJsonWith names), ("b", b.toJsonWith names)]
  | .or a b => Lean.Json.mkObj [("kind", Lean.Json.str "or"),
      ("a", a.toJsonWith names), ("b", b.toJsonWith names)]
  | .opaque _ => Lean.Json.mkObj [("opaque", Lean.Json.bool true)]
  | .exists (child := child) (ent := ent) parent fk body =>
      let childName := @Entity.tableName child ent
      let inner := fun i => if i == 0 then childName else names (i - 1)
      Lean.Json.mkObj [("kind", Lean.Json.str "exists"), ("child", Lean.Json.str childName),
        ("parent", colJson names parent), ("fk", colJson inner fk), ("body", body.toJsonWith inner)]
  | .forall (child := child) (ent := ent) parent fk body =>
      let childName := @Entity.tableName child ent
      let inner := fun i => if i == 0 then childName else names (i - 1)
      Lean.Json.mkObj [("kind", Lean.Json.str "forall"), ("child", Lean.Json.str childName),
        ("parent", colJson names parent), ("fk", colJson inner fk), ("body", body.toJsonWith inner)]

def Footprint.toJson (f : Footprint) : Lean.Json :=
  Lean.Json.mkObj [("tables", Lean.Json.arr (f.tables.map Lean.Json.str).toArray),
    ("columns", Lean.Json.arr (f.columns.map fun (t, c) => Lean.Json.str s!"{t}.{c}").toArray),
    ("residual", Lean.Json.bool f.residual)]

/-- What the log stores for a select: the tables, the plan, its footprint. -/
private def planJson (ts : List Type) [RowsOf ts] (p : Pred ts) : String :=
  let specs := RowsOf.specs ts
  let names := fun i => (specs[i]?.map (·.name)).getD s!"t{i}"
  (Lean.Json.mkObj [("tables", Lean.Json.arr (specs.map (Lean.Json.str ·.name)).toArray),
    ("plan", p.toJsonWith names), ("footprint", p.footprint.toJson)]).compress

/-- The typed select. The trailing `plan` is reified from `where'` by the
    `leandb_plan` tactic at each call site as a `Pred ts`; what ships to
    SQL is its pushable projection `approx` (`Pred.approx_sound`: it never
    excludes a row the plan accepts). Join conditions route to the joined
    executor, everything else narrows per-table fetches. The lambda is
    still applied to what comes back (`finishRows`), so the reference
    semantics (`selectSpec` over an unfiltered source) define the result
    and pushdown can only be an optimization. -/
def select (ts : List Type) [RowsOf ts] (where' : Rows ts → Bool)
    (sortBy : SortBy (Rows ts) := .preserve)
    (plan : PlanFor where' := by leandb_plan) : DbM (Array (Rows ts)) :=
  withLog "select" (selectDetail ts plan.plan) (·.size) (plan := some (planJson ts plan.plan)) <|
    runPlanned ts plan.plan.approx where' sortBy

/-- The snapshot a plan quantifies over (LEP-0004): every child table it
    mentions, whole, via `fetchAll`. One fetch per quantified child per
    select — bounded by the child table, not by the product; a few hundred
    rows in these bases. Narrowing it to the children of the fetched
    parents (`IN (…)`) is a later optimization. -/
def Pred.snapshot {ts : List Type} (p : Pred ts) : DbM Pred.Snapshot :=
  go p.children .empty
where
  go : List ((β : Type) × Entity β) → Pred.Snapshot → DbM Pred.Snapshot
    | [], snap => pure snap
    | ⟨β, ent⟩ :: rest, snap => do
        let rows ← @fetchAll β ent
        go rest (@Pred.Snapshot.add snap β ent rows)

/-- The typed select over a plan given as data (LEP-0004) — the only way
    to write a plan that quantifies over a child table, since a lambda over
    `Rows ts` cannot mention rows it was not given. Same executor as
    `select` (`runPlanned`), same log line; the decider is the plan's own
    denotation over a snapshot of its child tables, so the
    lambda-always-runs invariant holds literally: `finishRows` filters by
    `p.denote`, and pushdown (`p.approx`) can only narrow the fetch. -/
def selectP (ts : List Type) [RowsOf ts] (p : Pred ts)
    (sortBy : SortBy (Rows ts) := .preserve)
    (order : Array (Order ts) := #[]) (window : Window := {}) : DbM (Array (Rows ts)) :=
  withLog "select" (selectDetail ts p) (·.size) (plan := some (planJson ts p)) <|
    transaction do
      if let .error e := window.check then throw e
      if window.limit.isSome && order.isEmpty then
        match sortBy with
        | .preserve => pure ()
        | _ => throw (.sqlite "limit requires a pushed order")
      let snap ← p.snapshot
      runPlanned ts p.approx (p.denote snap) sortBy order window
        (exact := !p.hasOpaque)

/-- `select` with pushdown disabled — the executable reference, for
    differential testing against the planned path. -/
def selectUnplanned (ts : List Type) [RowsOf ts] (where' : Rows ts → Bool)
    (sortBy : SortBy (Rows ts) := .preserve) : DbM (Array (Rows ts)) :=
  selectSpec ts dbSource where' sortBy

/-! ## Opening an instance -/

private def metaDdl : String :=
  "CREATE TABLE IF NOT EXISTS _leandb_meta (key TEXT PRIMARY KEY, value TEXT NOT NULL)"

def migrationsDdl : String :=
  "CREATE TABLE IF NOT EXISTS _leandb_migrations (idx INTEGER PRIMARY KEY AUTOINCREMENT, \
steps TEXT NOT NULL, fingerprint TEXT NOT NULL, \
applied_at INTEGER NOT NULL DEFAULT (unixepoch()), ok INTEGER NOT NULL)"

private def logDdl : String :=
  "CREATE TABLE IF NOT EXISTS _leandb_log (id INTEGER PRIMARY KEY AUTOINCREMENT, \
at INTEGER NOT NULL DEFAULT (unixepoch()), verb TEXT NOT NULL, detail TEXT NOT NULL, \
ok INTEGER NOT NULL, error TEXT, rows INTEGER NOT NULL)"

/-- Columns the log gained after 0.2.0: the plan as data and the query
    it ran under. -/
def logColumns : List (String × String) := [("plan", "TEXT"), ("query", "TEXT")]

def readMeta (db : SQLite) (key : String) : IO (Option String) := do
  let stmt ← db.prepare "SELECT value FROM _leandb_meta WHERE key = ?"
  stmt.bindText 1 key
  if ← stmt.step then some <$> stmt.columnText 0 else return none

def writeMeta (db : SQLite) (key value : String) : IO Unit := do
  let stmt ← db.prepare "INSERT OR REPLACE INTO _leandb_meta (key, value) VALUES (?, ?)"
  stmt.bindText 1 key
  stmt.bindText 2 value
  stmt.exec

def columnNames (db : SQLite) (table : String) : IO (List String) := do
  let stmt ← db.prepare s!"PRAGMA table_info({quoteId table})"
  let mut present : List String := []
  repeat
    if ← stmt.step then
      present := (← stmt.columnText 1) :: present
    else break
  return present

/-- Add the columns of an engine bookkeeping table that an older engine
    did not create (idempotent; `PRAGMA table_info` decides). Only the
    engine's own tables are ever touched this way.

    The read-then-ALTER is deliberately not wrapped in a transaction: two
    processes opening the same pre-0.2.0 instance concurrently both see the
    column missing and both ALTER (#78), and the loser's
    `duplicate column name` must not fail the open of a fine database — so
    a failed ALTER re-reads `table_info` and treats present = success. -/
def ensureColumns (db : SQLite) (table : String) (cols : List (String × String)) : IO Unit := do
  let present ← columnNames db table
  for (name, decl) in cols do
    unless present.contains name do
      try
        db.exec s!"ALTER TABLE {quoteId table} ADD COLUMN {quoteId name} {decl}"
      catch e =>
        unless (← columnNames db table).contains name do
          throw e

/-! ### Restore safety primitives

Shared by the CLI session (`Cli.replaceFile`) and `Runtime.Service.restore`:
validate the source before anything destructive, copy it bounded. -/

/-- The 16-byte magic string every SQLite 3 file begins with. -/
def Restore.magic : ByteArray := "SQLite format 3\u0000".toUTF8

/-- Do these leading bytes carry the SQLite 3 magic header? -/
def Restore.headerOk (bytes : ByteArray) : Bool :=
  bytes.size >= Restore.magic.size &&
    (List.range Restore.magic.size).all fun i => bytes[i]! == Restore.magic[i]!

/-- Validate a restore source before anything destructive happens: the
    magic header refuses text files and directories cheaply, then the
    source must open as a database and pass `PRAGMA quick_check`. -/
def Restore.validate (src : System.FilePath) : IO (Except DbError Unit) := do
  let head ← try
      let h ← IO.FS.Handle.mk src .read
      let bytes ← h.read Restore.magic.size.toUSize
      pure bytes
    catch e => return .error (.migrate s!"restore source cannot be read: {src} ({e})")
  unless Restore.headerOk head do
    return .error (.migrate s!"restore source is not a SQLite database: {src}")
  try
    let db ← SQLite.open src
    let stmt ← db.prepare "PRAGMA quick_check"
    if ← stmt.step then
      let verdict ← stmt.columnText 0
      if verdict == "ok" then return .ok ()
      return .error (.migrate s!"restore source failed quick_check: {src} ({verdict})")
    return .error (.migrate s!"restore source failed quick_check: {src}")
  catch e =>
    return .error (.migrate s!"restore source is not a valid SQLite database: {src} ({e})")

/-- Bounded-memory file copy: 1 MiB reads, so the source's size never
    sets the process's memory use. -/
def Restore.copyChunked (src dest : System.FilePath) : IO Unit := do
  let chunk : USize := 1024 * 1024
  let input ← IO.FS.Handle.mk src .read
  let output ← IO.FS.Handle.mk dest .write
  repeat
    let bytes ← input.read chunk
    if bytes.isEmpty then break
    output.write bytes

/-- #76: refuse the restore/rollback file swap while another process holds
    the instance's write lock. `BEGIN IMMEDIATE` takes SQLite's RESERVED
    lock and fails immediately (no busy timeout is set) when a concurrent
    writer is active; the probe transaction is rolled back at once — it
    asserts availability, it writes nothing. Not a lockfile: a writer that
    opens between the probe and the rename still ends up on the unlinked
    old inode — its post-swap commits vanish (documented on the verbs). -/
def assertSoleWriter (conn : Conn) (verb : String) : IO (Except DbError Unit) := do
  try
    conn.raw.exec "BEGIN IMMEDIATE"
  catch e =>
    return .error (.busy s!"{verb}: another writer holds the instance write lock ({e}); \
retry when the other writer is idle")
  conn.raw.exec "ROLLBACK"
  return .ok ()

/-- Replace the instance file at `path` with `src`: validate first, copy
    under a temporary name, rename into place so no reader sees a
    half-written file, and take stale `-wal`/`-shm`/`-journal` siblings
    with the old file. The caller reopens after the swap. -/
def Restore.swapFile (path src : System.FilePath) : IO (Except DbError Unit) := do
  unless ← src.pathExists do
    return .error (.migrate s!"restore source does not exist: {src}")
  match ← Restore.validate src with
  | .error e => return .error e
  | .ok () => pure ()
  try
    let tmp : System.FilePath := path.toString ++ ".restore"
    try
      Restore.copyChunked src tmp
    catch e =>
      try IO.FS.removeFile tmp catch _ => pure ()
      throw e
    for suffix in ["-wal", "-shm", "-journal"] do
      let side : System.FilePath := path.toString ++ suffix
      if ← side.pathExists then IO.FS.removeFile side
    IO.FS.rename tmp path
    return .ok ()
  catch e =>
    return .error (.sqlite s!"restore failed: {e}")

/-- Columns the journal gained after 0.2.0: the versions a migration moved
    between, the backup taken before it, and a free-form note. -/
def journalColumns : List (String × String) :=
  [("from_version", "INTEGER"), ("to_version", "INTEGER"), ("backup", "TEXT"), ("note", "TEXT")]

/-- SQLite's clock, so backups and journal rows agree on the epoch. -/
def unixNow (conn : Conn) : IO Nat := do
  let stmt ← conn.raw.prepare "SELECT unixepoch()"
  if ← stmt.step then return (← stmt.columnInt64 0).toNatClampNeg else return 0

/-- A full, consistent copy of the instance at `dest` (`VACUUM INTO`),
    after a WAL checkpoint so nothing is left in a `-wal` file. `dest`
    must not exist. -/
def backupTo (conn : Conn) (dest : System.FilePath) : IO Unit := do
  if let some parent := dest.parent then
    IO.FS.createDirAll parent
  if ← dest.pathExists then
    throw <| IO.userError s!"backup target already exists: {dest}"
  conn.raw.exec "PRAGMA wal_checkpoint(TRUNCATE)"
  let quoted := "'" ++ (dest.toString.replace "'" "''") ++ "'"
  conn.raw.exec s!"VACUUM INTO {quoted}"

/-- How many `-N` suffixes a backup name may go through before refusing. -/
def backupRetries : Nat := 32

/-- A full, consistent copy of the instance, like `backupTo`, but the
    destination is only a suggestion: on a name collision — two backups in
    the same wall-second, since the clock has second resolution (#74), or
    another process claiming the name between the check and the write —
    the path is retried as `<base>-2`, `<base>-3`… up to `retries`. Returns
    the path actually written; callers journal it, and `migrate apply`
    retries must stay possible within one wall-second. `unixNow`'s 0
    fallback (every same-version backup colliding) is covered by the same
    suffix loop. -/
def backupToUniquified (conn : Conn) (dest : System.FilePath)
    (retries : Nat := backupRetries) : IO System.FilePath := do
  -- the suffix base is the suggested name minus `.sqlite`, computed once:
  -- every retry starts from it, so collisions yield `base-2`, `base-3`…
  -- (recomputing from the last attempt would compound suffixes instead)
  let stem := dest.toString.dropEnd (if dest.toString.endsWith ".sqlite" then 7 else 0)
  let mut d := dest
  for k in [1:retries + 1] do
    try
      backupTo conn d
      return d
    catch e =>
      -- the pre-check and `VACUUM INTO` itself both say "already exists"
      unless (e.toString.splitOn "already exists").length > 1 do
        throw e
      d := s!"{stem}-{k + 1}.sqlite"
  throw <| IO.userError s!"no free backup path after {retries} collisions: {dest}"

def readJournal (conn : Conn) (limit : Nat) : IO (Array Lean.Json) := do
  let stmt ← conn.raw.prepare
    "SELECT idx, steps, fingerprint, applied_at, ok, from_version, to_version, backup, note \
FROM _leandb_migrations ORDER BY idx DESC LIMIT ?"
  stmt.bindInt64 1 (Int64.ofNat limit)
  let mut out := #[]
  let optText := fun (i : Int32) => do
    if (← stmt.columnType i) == .null then pure Lean.Json.null
    else Lean.Json.str <$> stmt.columnText i
  let optInt := fun (i : Int32) => do
    if (← stmt.columnType i) == .null then pure Lean.Json.null
    else pure (Lean.toJson (← stmt.columnInt64 i).toInt)
  repeat
    if ← stmt.step then
      let steps := (Lean.Json.parse (← stmt.columnText 1)).toOption.getD Lean.Json.null
      out := out.push <| Lean.Json.mkObj [
        ("idx", Lean.toJson (← stmt.columnInt64 0).toInt),
        ("steps", steps),
        ("fingerprint", Lean.Json.str (← stmt.columnText 2)),
        ("applied_at", Lean.toJson (← stmt.columnInt64 3).toInt),
        ("ok", Lean.Json.bool ((← stmt.columnInt64 4) == 1)),
        ("from_version", ← optInt 5),
        ("to_version", ← optInt 6),
        ("backup", ← optText 7),
        ("note", ← optText 8)]
    else break
  return out

/-- Open the file (creating it if absent) and make sure the engine's own
    bookkeeping tables exist — nothing about the base's schema is checked
    or applied. A server holds a connection opened this way so it can
    answer `version`/`migrate` on a drifted instance; `Conn.verify` is the
    step that admits the base's verbs. -/
def openDbRaw (path : System.FilePath) (logConfig : LogConfig := {})
    (openConfig : OpenConfig := {}) (readOnly : Bool := false) :
    IO (Except DbError Conn) := do
  let logConfig ← match logConfig.ofSettings
      (← IO.getEnv "LEANDB_LOG_MAX")
      (← IO.getEnv "LEANDB_LOG_IMPACT_LIMIT")
      (← IO.getEnv "LEANDB_LOG_VERBS")
      (← IO.getEnv "LEANDB_LOG_SAMPLE")
      (← IO.getEnv "LEANDB_LOG_BATCH") with
    | .ok config => pure config
    | .error m => return .error (.sqlite s!"invalid log configuration: {m}")
  -- Invalid env values fail *before* the database is opened.
  let openConfig ← match ← openConfig.ofEnv with
    | .ok c => pure c
    | .error m => return .error (.sqlite s!"invalid open configuration: {m}")
  try
    let db ←
      if readOnly then
        SQLite.openWith path .readonly
      else
        SQLite.open path
    db.exec "PRAGMA foreign_keys = ON"
    unless readOnly do
      db.exec "PRAGMA journal_mode = WAL"
    openConfig.apply db
    if readOnly then
      db.exec "PRAGMA query_only = ON"
    db.exec metaDdl
    unless readOnly do
      db.exec logDdl
      db.exec migrationsDdl
      ensureColumns db "_leandb_migrations" journalColumns
      ensureColumns db "_leandb_log" logColumns
      db.exec "CREATE INDEX IF NOT EXISTS _leandb_log_select_id ON _leandb_log(id DESC) WHERE verb = 'select' AND plan IS NOT NULL"
      if let some keep := logConfig.maxEntries then discard <| pruneLogRaw db keep
    return .ok (← Conn.ofRaw db logConfig openConfig readOnly)
  catch e =>
    return .error (.sqlite (toString e))

/-- Check the open instance against the code's schema: refuse fingerprint
    drift, apply DDL idempotently, scan stored closed-world values for
    drift, and record the schema. Drift is an error, not a surprise. -/
def Conn.verify (conn : Conn) (specs : List TableSpec) (initialVersion : Nat := 1) :
    IO (Except DbError Unit) := do
  if let .error e := validateSchema specs then return .error e
  try
    let db := conn.raw
    let fp := fingerprint specs
    match ← readMeta db "schema_fingerprint" with
    | some stored =>
        if stored != fp then
          return .error (.schemaMismatch fp stored)
    | none =>
        -- a file with no fingerprint meta was not created by this engine.
        -- Stamping the base's fingerprint onto a foreign file whose
        -- physical tables contradict `specs` would make the metadata lie
        -- (later verbs fail with raw SQL errors instead of a typed
        -- mismatch, and `migrate` plans from a phantom baseline), so a
        -- first open of a file that already carries user tables is
        -- refused by name. Empty files (and files this engine's own DDL
        -- has just created) pass.
        let stmt ← db.prepare
          "SELECT name FROM sqlite_master WHERE type = 'table' \
AND name NOT LIKE 'sqlite\\_%' ESCAPE '\\' AND name NOT LIKE '\\_leandb\\_%' ESCAPE '\\'"
        if ← stmt.step then
          let existing ← stmt.columnText 0
          return .error (.migrate s!"the file already carries tables (first: {String.quote existing}) \
but records no LeanDB schema: it was not created by this base. Adopt it with \
`leandb import-sqlite` instead of opening it as this base's instance")
    -- Extra user tables / virtual tables / triggers in a fingerprinted
    -- instance are tolerated and ignored by the fingerprint (LDB-11).
    for spec in specs do
      db.exec spec.ddl
      for sql in spec.indexDdl do db.exec sql
    -- CHECK guards new writes; this guards data written under an older world.
    for spec in specs do
      for c in spec.columns do
        if let some vs := c.enum then
          let stmt ← db.prepare
            s!"SELECT DISTINCT {quoteId c.name} FROM {quoteId spec.name} WHERE {quoteId c.name} IS NOT NULL"
          repeat
            if ← stmt.step then
              let v ← stmt.columnText 0
              unless vs.contains v do
                return .error (.enumDrift spec.name c.name v)
            else break
        -- an EnumSet column: no stored bit outside the world's mask
        if let some vs := c.enumSet then
          let stmt ← db.prepare
            s!"SELECT {quoteId c.name} FROM {quoteId spec.name} WHERE ({quoteId c.name} & ~{enumSetMask vs.size}) != 0 LIMIT 1"
          if ← stmt.step then
            return .error (.enumDrift spec.name c.name (toString (← stmt.columnInt64 0)))
    writeMeta db "schema_fingerprint" fp
    writeMeta db "schema_json" (specsToJson specs).compress
    if (← readMeta db "schema_version").isNone then
      writeMeta db "schema_version" (toString initialVersion)
    return .ok ()
  catch e =>
    return .error (.sqlite (toString e))

/-- Open (creating if absent) an instance for the given schema: `openDbRaw`
    then `Conn.verify`. Refuses to open an instance whose fingerprint
    disagrees with the code's. -/
def openDb (path : System.FilePath) (specs : List TableSpec) (logConfig : LogConfig := {})
    (openConfig : OpenConfig := {}) : IO (Except DbError Conn) := do
  match ← openDbRaw path logConfig openConfig with
  | .error e => return .error e
  | .ok conn =>
      match ← conn.verify specs with
      | .error e => return .error e
      | .ok () => return .ok conn

/-- Recent query-log entries, newest first, as JSON rows. -/
def readLog (limit : Nat) : DbM (Array Lean.Json) := sqlite fun db => do
  let stmt ← db.prepare
    "SELECT id, at, verb, detail, ok, error, rows, plan, query FROM _leandb_log ORDER BY id DESC LIMIT ?"
  stmt.bindInt64 1 (Int64.ofNat limit)
  let mut out := #[]
  repeat
    if ← stmt.step then
      let err ← (do if (← stmt.columnType 5) == .null then pure Lean.Json.null
                    else Lean.Json.str <$> stmt.columnText 5)
      let plan ← (do if (← stmt.columnType 7) == .null then pure Lean.Json.null
                     else pure ((Lean.Json.parse (← stmt.columnText 7)).toOption.getD Lean.Json.null))
      let query ← (do if (← stmt.columnType 8) == .null then pure Lean.Json.null
                      else Lean.Json.str <$> stmt.columnText 8)
      out := out.push <| Lean.Json.mkObj [
        ("id", Lean.toJson (← stmt.columnInt64 0).toInt),
        ("at", Lean.toJson (← stmt.columnInt64 1).toInt),
        ("verb", Lean.Json.str (← stmt.columnText 2)),
        ("detail", Lean.Json.str (← stmt.columnText 3)),
        ("ok", Lean.Json.bool ((← stmt.columnInt64 4) == 1)),
        ("error", err),
        ("rows", Lean.toJson (← stmt.columnInt64 6).toInt),
        ("plan", plan),
        ("query", query)]
    else break
  return out

structure LogFootprintScan where
  entries : Array (Option String × List (String × String)) := #[]
  truncated : Bool := false

/-- Inspect at most `limit` plans and probe one extra row without parsing
    its JSON, so callers can disclose that older history was excluded. -/
def scanLogFootprints (conn : Conn) (limit : Nat) : IO LogFootprintScan := do
  if limit >= Int64.maxValue.toNatClampNeg then
    throw <| IO.userError "log impact limit is out of range"
  let stmt ← conn.raw.prepare
    "SELECT query, plan FROM _leandb_log WHERE verb = 'select' AND plan IS NOT NULL ORDER BY id DESC LIMIT ?"
  stmt.bindInt64 1 (Int64.ofNat (limit + 1))
  let mut out := #[]
  repeat
    if ← stmt.step then
      if out.size == limit then return { entries := out, truncated := true }
      let q ← (do if (← stmt.columnType 0) == .null then pure none else some <$> stmt.columnText 0)
      let plan := (Lean.Json.parse (← stmt.columnText 1)).toOption.getD Lean.Json.null
      let cols := ((plan.getObjVal? "footprint" >>= (·.getObjValAs? (Array String) "columns")).toOption.getD #[]).toList
      let pairs := cols.filterMap fun s =>
        match s.splitOn "." with
        | [t, c] => some (t, c)
        | _ => none
      out := out.push (q, pairs)
    else break
  return { entries := out }

/-- Logged selects, newest first: `(query name, footprint columns)`. -/
def logFootprints (conn : Conn) (limit : Nat) : IO (Array (Option String × List (String × String))) := do
  return (← scanLogFootprints conn limit).entries


/-! ## LDB-06: `count` / `exists`

When the predicate has no residual, these render `COUNT(*)` / `EXISTS`.
Otherwise they fetch and reduce in Lean and the plan log records that. -/

def countP [RowsOf ts] (p : Pred ts) : DbM Nat :=
  withLog "count" (selectDetail ts p) (fun _ => 1) (plan := some (planJson ts p)) do
    if p.hasOpaque then
      return (← selectP ts p).size
    let specs := RowsOf.specs ts
    let (fromSql, whereSql, binds) ← match specs with
      | [spec] =>
          let (w, b) := p.approx.render fun _ => "t0"
          pure (s!"{quoteId spec.name} AS t0", w, b)
      | _ =>
          let (w, b) := p.approx.renderT
          pure (joinedFromSql ts p.approx, w, b)
    sqlite fun db => do
      let stmt ← db.prepare s!"SELECT COUNT(*) FROM {fromSql} WHERE {whereSql}"
      bindCols stmt 1 binds
      if ← stmt.step then return (← stmt.columnInt64 0).toNatClampNeg else return 0

def count [RowsOf ts] (p : Rows ts → Bool) (plan : PlanFor p := by leandb_plan) : DbM Nat :=
  withLog "count" (selectDetail ts plan.plan) (fun _ => 1) (plan := some (planJson ts plan.plan)) do
    return (← runPlanned ts plan.plan.approx p .preserve).size

def exists? [RowsOf ts] (p : Rows ts → Bool) (plan : PlanFor p := by leandb_plan) : DbM Bool :=
  withLog "exists" (selectDetail ts plan.plan) (fun _ => 1) (plan := some (planJson ts plan.plan)) do
    let rows ← runPlanned ts plan.plan.approx p .preserve #[] { limit := some 1 } (exact := false)
    return !rows.isEmpty

def existsP [RowsOf ts] (p : Pred ts) : DbM Bool :=
  withLog "exists" (selectDetail ts p) (fun _ => 1) (plan := some (planJson ts p)) do
    if p.hasOpaque then
      return !(← selectP ts p (window := { limit := some 1 })).isEmpty
    let specs := RowsOf.specs ts
    let (fromSql, whereSql, binds) ← match specs with
      | [spec] =>
          let (w, b) := p.approx.render fun _ => "t0"
          pure (s!"{quoteId spec.name} AS t0", w, b)
      | _ =>
          let (w, b) := p.approx.renderT
          pure (joinedFromSql ts p.approx, w, b)
    sqlite fun db => do
      let stmt ← db.prepare
        s!"SELECT EXISTS(SELECT 1 FROM {fromSql} WHERE {whereSql})"
      bindCols stmt 1 binds
      if ← stmt.step then return (← stmt.columnInt64 0) != 0 else return false

/-! ## LDB-07: field-level `patch` -/

structure Assignment (α : Type) [Entity α] where
  field : Entity.Field α
  encoded : Col

def Assignment.of [Entity α] (f : Entity.Field α) (v : Entity.fieldTy f) : Assignment α :=
  ⟨f, (Entity.codec f).toCol v⟩

structure Patch (α : Type) [Entity α] where
  sets : Array (Assignment α)

inductive PatchResult where
  | updated | notFound | guardFailed
  deriving Repr, DecidableEq

def patch [Entity α] (id : Id α) (p : Patch α) (guard : Pred [α] := .tt) :
    DbM PatchResult := withLog "patch" (Entity.tableName α) (fun _ => 1) do
  requireWritable "patch"
  if guard.hasOpaque then
    throw (.sqlite "patch guard must not contain an opaque leaf")
  let run : DbM PatchResult := do
    let spec := Entity.spec α
    if p.sets.isEmpty then
      match ← get id with
      | some _ => return .updated
      | none => return .notFound
    let sets := String.intercalate ", " (p.sets.toList.map fun a =>
      s!"{quoteId (Entity.fieldName a.field)} = ?")
    let (whereSql, binds) := guard.render fun _ => "t0"
    let sql := s!"UPDATE {quoteId spec.name} AS t0 SET {sets} WHERE t0.id = ? AND {whereSql}"
    let changed ← sqliteWith (constraintError spec.name (.missingRef spec.name)) fun db => do
      let stmt ← db.prepare sql
      bindCols stmt 1 (p.sets.map (·.encoded))
      stmt.bindInt64 (Int32.ofNat (p.sets.size + 1)) id.toInt64
      bindCols stmt (p.sets.size + 2) binds
      stmt.exec
      db.changes
    if changed != 0 then return .updated
    match ← get id with
    | some _ => return .guardFailed
    | none => return .notFound
  -- a declared invariant (LDB-16) is checked on the patched row before the
  -- transaction commits: `get` refuses a row that fails it, which rolls back
  if (Entity.invariant (α := α)).isNone then run
  else transaction do
    let r ← run
    if r == .updated then discard <| get id
    return r

/-! ## LDB-08: `insertMany` and `scan` -/

def insertMany (α : Type) [Entity α] (rows : Array α) : DbM (Array (Stored α)) :=
  withLog "insertMany" (Entity.tableName α) (·.size) do
    requireWritable "insertMany"
    rows.forM checkInvariant
    rows.forM checkSqlRange
    if rows.isEmpty then return #[]
    let spec := Entity.spec α
    let links := Entity.children (α := α)
    let names := String.intercalate ", " (spec.columns.toList.map (quoteId ·.name))
    let sql := if spec.columns.isEmpty then
      s!"INSERT INTO {quoteId spec.name} DEFAULT VALUES"
    else
      s!"INSERT INTO {quoteId spec.name} ({names}) VALUES ({placeholders spec.columns.size})"
    transaction do
      let out ← sqliteWith (constraintError spec.name (.missingRef spec.name)) fun db => do
        let stmt ← db.prepare sql
        let mut out : Array (Stored α) := Array.mkEmpty rows.size
        for a in rows do
          stmt.reset
          stmt.clearBindings
          unless spec.columns.isEmpty do bindCols stmt 1 (Entity.encode a)
          stmt.exec
          let id ← db.lastInsertRowId
          out := out.push ⟨⟨id⟩, a⟩
        return out
      if !links.isEmpty then
        for s in out do
          for link in links do insertChildren link s.id.toInt64 s.val
      return out

/-- Keyset-paginated walk over `id`. Each chunk is its own deferred
    snapshot so a concurrent writer is not starved. `f` returns `false`
    to stop. -/
partial def scan [Entity α] (p : Pred [α]) (chunk : Nat := 500)
    (f : Array (Stored α) → DbM Bool) : DbM Unit :=
  withLog "scan" (Entity.tableName α) (fun _ => 1) do
    if chunk == 0 || chunk >= Int64.maxValue.toNatClampNeg then
      throw (.sqlite "scan chunk is out of range")
    let rec go (last : Option Int64) : DbM Unit := do
      let window : Window := { limit := some chunk }
      let rows ← match last with
        | none => fetchFiltered α p none #[{ column := "id", dir := .asc }] window
        | some id =>
            let (whereSql, binds) := p.render fun _ => "t0"
            transaction do
              let rows ← sqlite fun db => do
                let stmt ← db.prepare
                  s!"SELECT {columnList α} FROM {quoteId (Entity.tableName α)} AS t0 \
WHERE ({whereSql}) AND t0.id > ? ORDER BY t0.id ASC LIMIT ?"
                bindCols stmt 1 binds
                stmt.bindInt64 (Int32.ofNat (binds.size + 1)) id
                stmt.bindInt64 (Int32.ofNat (binds.size + 2)) (Int64.ofNat chunk)
                let mut out := #[]
                repeat
                  if ← stmt.step then out := out.push (← readStored α stmt) else break
                return out
              attachChildren α (← rows.mapM liftExcept)
      if rows.isEmpty then return
      unless (← f rows) do return
      if rows.size < chunk then return
      go (rows.back?.map (·.id.toInt64))
    go none

/-! ## LDB-11: FTS5 auxiliary search -/

def Auxiliary.ddl : Auxiliary → List String
  | .fts5 name content columns tokenizer =>
      let cols := String.intercalate ", " (columns.toList ++ [s!"tokenize='{tokenizer}'"])
      let fts := s!"CREATE VIRTUAL TABLE IF NOT EXISTS {quoteIdent name} USING fts5({cols})"
      -- content-sync triggers: insert/update/delete on the content table
      let colList := String.intercalate ", " (columns.toList.map quoteIdent)
      let newList := String.intercalate ", " (columns.toList.map fun c => s!"new.{quoteIdent c}")
      let ins := s!"CREATE TRIGGER IF NOT EXISTS {quoteIdent (name ++ "_ai")} AFTER INSERT ON {quoteIdent content} BEGIN \
INSERT INTO {quoteIdent name}(rowid, {colList}) VALUES (new.id, {newList}); END"
      let del := s!"CREATE TRIGGER IF NOT EXISTS {quoteIdent (name ++ "_ad")} AFTER DELETE ON {quoteIdent content} BEGIN \
INSERT INTO {quoteIdent name}({quoteIdent name}, rowid) VALUES ('delete', old.id); END"
      let upd := s!"CREATE TRIGGER IF NOT EXISTS {quoteIdent (name ++ "_au")} AFTER UPDATE ON {quoteIdent content} BEGIN \
INSERT INTO {quoteIdent name}({quoteIdent name}, rowid) VALUES ('delete', old.id); \
INSERT INTO {quoteIdent name}(rowid, {colList}) VALUES (new.id, {newList}); END"
      [fts, ins, del, upd]

def applyAuxiliary (db : SQLite) (aux : List Auxiliary) : IO Unit := do
  for a in aux do
    for sql in a.ddl do db.exec sql

/-- Ranked FTS5 search: `query` is a bound `MATCH` parameter, never
    interpolated. Returns `(id, bm25)` in rank order. -/
def searchP [Entity α] (aux : Auxiliary) (query : String) (window : Window := {}) :
    DbM (Array (Stored α × Float)) :=
  withLog "search" (Entity.tableName α) (·.size) do
    if let .error e := window.check then throw e
    let .fts5 name content _ _ := aux
    unless content == Entity.tableName α do
      throw (.sqlite s!"searchP content table {content} is not {Entity.tableName α}")
    let mut tail := ""
    let mut extra : Array Col := #[]
    if let some n := window.limit then
      tail := tail ++ " LIMIT ?"; extra := extra.push (.int (Int64.ofNat n))
    if window.offset != 0 then
      tail := tail ++ " OFFSET ?"; extra := extra.push (.int (Int64.ofNat window.offset))
    let sql := s!"SELECT {columnList α}, bm25({quoteId name}) FROM {quoteId (Entity.tableName α)} \
JOIN {quoteId name} ON {quoteId name}.rowid = {quoteId (Entity.tableName α)}.id \
WHERE {quoteId name} MATCH ? ORDER BY bm25({quoteId name}){tail}"
    transaction do
      let raw ← sqlite fun db => do
        let stmt ← db.prepare sql
        stmt.bindText 1 query
        bindCols stmt 2 extra
        let mut out : Array (Except DbError (Stored α) × Float) := #[]
        repeat
          if ← stmt.step then
            let row ← readStored α stmt
            let rank ← stmt.columnDouble (Int32.ofNat ((Entity.fields (α := α)).size + 1))
            out := out.push (row, rank)
          else break
        return out
      raw.mapM fun (r, rank) => do
        let s ← liftExcept r
        let rows ← attachChildren α #[s]
        match rows[0]? with
        | some s => return (s, rank)
        | none => throw (.sqlite "searchP: attached row missing")

/-- Open, run, and report — the whole lifecycle for scripts and tests. -/
def withDb (path : System.FilePath) (specs : List TableSpec) (act : DbM α) :
    IO (Except DbError α) := do
  match ← openDb path specs with
  | .error e => return .error e
  | .ok conn => act.run conn

end LeanDb
