import Std.Sync.RecursiveMutex
import Std.Sync.Mutex
import LeanDb.Base
import LeanDb.Transaction

namespace LeanDb.Runtime

/-! # `Service`: one connection, serialized admission

The runtime the native adapters consume (LDB-01). A `Service` owns one
`Conn` behind a `Std.RecursiveMutex`: every `withConnection` call runs
serialized, off the caller's event loop, and a callback that calls back
into `withConnection` on the same thread is rejected with
`RuntimeError.reentrant` instead of deadlocking (the recursive lock lets
the same thread in, so the depth counter sees the reentry; a different
thread blocks until the holder finishes).

Lifecycle: `ready → draining → ready` (`drain`/`resume`), `ready →
restoring → ready` (`restore`), and `closed` (`close`, terminal).
`ready` reports the lifecycle state and the verify gate; an inspection
session (`SessionMode.inspect`) is never ready — `Managed.readiness`
treats it as unready by construction.

`restore` reuses the restore-safety path (`Restore.swapFile`): validate
the source, swap under a temporary name, reopen, re-verify. A reopen
failure leaves the service gated — verbs are refused loudly — rather
than serving a file it could not open (#77's shape).

Snapshot lanes (LDB-13): `snapshot` runs its `VACUUM INTO` on a pooled
reader connection when `Config.readers > 0` — a consistent read snapshot
in WAL mode, so the writer keeps serving during the backup — and falls
back to the writer (logging it) when no readers are configured;
`snapshotOn` names the lane explicitly. A snapshot writes to `dest.tmp`
and renames on success, so a failed snapshot leaves no torn output.
`restore` waits for a running snapshot: it stands down before its rename
with a typed error, so the swap never happens under a reader's `VACUUM
INTO`.

The callback contract: `f` must not retain the `Conn` past return. The
connection enforces synchronous ownership; nothing stops a callback from
stashing it, so this is documented, not enforced.
-/

/-- The service's lifecycle. `draining`/`restoring` refuse new
    `withConnection` admissions; `closed` is terminal. -/
inductive State where
  | ready
  | draining
  | restoring
  | closed
  deriving Repr, DecidableEq

/-- What kind of session the service runs. `inspect` is read-only and
    never `ready`: it exists to look at an instance, not to serve it. -/
inductive SessionMode where
  | serve
  | inspect
  deriving Repr, DecidableEq

/-- Is this session read-only? Inspection sessions are. -/
def SessionMode.readOnly : SessionMode → Bool
  | .serve => false
  | .inspect => true

/-- Errors the service itself raises, distinct from `DbError`: host
    exceptions the callback or SQLite threw untyped (the single place
    they are converted, per #73), lifecycle refusals, and reentrancy. -/
inductive RuntimeError where
  /-- A host `IO.Error` escaped the callback or the engine. -/
  | host (message : String)
  /-- The service is not admitting work: draining, restoring, or closed. -/
  | notReady (state : State)
  /-- `withConnection` was called from inside a `withConnection`
      callback on the same thread. -/
  | reentrant
  /-- The instance failed verification; verbs are gated. -/
  | gated (e : DbError)
  /-- A snapshot is already running; `snapshotOn` refuses to start a
      second one (two `VACUUM INTO`s to one `dest.tmp` would corrupt
      each other). -/
  | snapshotBusy
  /-- A running snapshot stood down because `restore` claimed the
      connection (LDB-13); its partial output was removed. -/
  | snapshotAborted
  deriving Repr

def RuntimeError.message : RuntimeError → String
  | .host m => s!"host error: {m}"
  | .notReady s => s!"service is not ready (state: {repr s})"
  | .reentrant => "withConnection called reentrantly from its own callback"
  | .gated e => s!"instance gated: {e.message}"
  | .snapshotBusy => "a snapshot is already running"
  | .snapshotAborted => "snapshot aborted: restore claimed the connection"

instance : ToString RuntimeError := ⟨RuntimeError.message⟩

/-- Which connection a snapshot runs on (LDB-13). `.reader` runs the
    `VACUUM INTO` on a pooled read-only connection — a consistent read
    snapshot in WAL mode, so the writer keeps serving during the backup.
    `.writer` holds the writer connection under the admission lock for
    the whole backup: the pre-LDB-13 behaviour, and the fallback when
    `Config.readers := 0`. -/
inductive SnapshotLane where
  | reader
  | writer
  deriving Repr, DecidableEq

/-- The lane's name, for `Runtime.status`. -/
def SnapshotLane.name : SnapshotLane → String
  | .reader => "reader"
  | .writer => "writer"

/-- How the last finished snapshot went, for `Runtime.status`. -/
structure SnapshotStat where
  lane : SnapshotLane
  durationMs : Nat
  bytes : Nat
  deriving Repr

/-- A snapshot in flight, registered in the slot so `restore` can
    coordinate with it (LDB-13): `abort` is set when restore claims the
    connection. The `VACUUM INTO` itself cannot be interrupted, so the
    snapshot honours the request where it can — before the rename — and
    removes its partial output. -/
private structure SnapshotJob where
  lane : SnapshotLane
  tmp : System.FilePath
  abort : IO.Ref Bool

/-- Mutable service state, inside the lock. -/
private structure Slot where
  conn : Conn
  state : State
  depth : Nat := 0
  gate : Option DbError := none
  readers : Array (Std.Mutex Conn) := #[]
  readerIdx : Nat := 0
  snapshotJob : Option SnapshotJob := none
  lastSnapshot : Option SnapshotStat := none

structure Config where
  readers : Nat := 0
  readerBusyTimeoutMs : Nat := 5000
  deriving Repr

structure Service where
  base : Base
  inst : Instance
  session : SessionMode
  config : Config := {}
  slot : Std.RecursiveMutex Slot

namespace Service

private def gateOf (b : Base) (conn : Conn) : IO (Option DbError) := do
  if let some c := b.chain then discard <| c.adopt conn
  match ← conn.verify b.specs b.headVersion with
  | .ok () => return none
  | .error e => return some e

def new (b : Base) (inst : Instance) (session : SessionMode) (verify : Bool := true)
    (config : Config := {}) : IO Service := do
  if let .error e := b.check then throw <| IO.userError e.message
  if let some parent := inst.path.parent then
    IO.FS.createDirAll parent
  let conn ← match ← openDbRaw inst.path b.log b.openConfig with
    | .ok conn => pure conn
    | .error e => throw <| IO.userError e.message
  try applyAuxiliary conn.raw b.auxiliary catch e => throw e
  let gate ← if verify then gateOf b conn else pure (some (.schemaInvalid "unverified"))
  let nReaders := max config.readers 1
  let mut readers : Array (Std.Mutex Conn) := #[]
  for _ in [0:nReaders] do
    let rc ← match ← openDbRaw inst.path b.log
        { b.openConfig with busyTimeoutMs := config.readerBusyTimeoutMs } (readOnly := true) with
      | .ok c => pure c
      | .error e => throw <| IO.userError e.message
    readers := readers.push (← Std.Mutex.new rc)
  let slot ← Std.RecursiveMutex.new { conn, state := State.ready, gate, readers }
  return { base := b, inst, session, config, slot }

/-- The lifecycle state, for `ManagedChecks.waitState`. -/
def state (s : Service) : IO State :=
  s.slot.atomically (return (← getThe Slot).state)

/-- Is the service admitting work? A serving session in `ready` with no
    gate; an inspection session is never ready. -/
def ready (s : Service) : IO Bool :=
  if s.session.readOnly then return false else
    s.slot.atomically (return (← getThe Slot).state == .ready && (← getThe Slot).gate.isNone)

/-- The instance file this service serves. -/
def database (s : Service) : System.FilePath := s.inst.path

/-- Run `f` on the connection, serialized. Refuses while draining,
    restoring, or closed; refuses reentrant calls from the callback's own
    thread; refuses while the gate is set (a drifted instance is repaired
    through `restore` or the CLI, not served). Host exceptions from `f`
    become `RuntimeError.host` — the one place they are converted, so a
    server built on this cannot die to a raw `IO.Error` (#73). -/
def withConnection (s : Service) (f : Conn → IO α) : IO (Except RuntimeError α) :=
  s.slot.atomically do
    let st ← getThe Slot
    if st.depth > 0 then return .error .reentrant
    if st.state != .ready then return .error (.notReady st.state)
    if let some e := st.gate then return .error (.gated e)
    set { st with depth := st.depth + 1 }
    try
      .ok <$> f st.conn
    catch e =>
      pure (.error (.host (toString e)))
    finally
      modify fun st => { st with depth := st.depth - 1 }

/-- A pooled read-only connection (LDB-09, LDB-19). Does not hold the
    writer lock for the duration of `f`, so concurrent readers on
    distinct pool slots proceed. Each slot is locked per connection.
    `readers := 0` still opens one dedicated reader — the writer
    connection is never handed out as a reader. -/
def withReader (s : Service) (f : Conn → IO α) : IO (Except RuntimeError α) := do
  let picked : Except State (Std.Mutex Conn) ← s.slot.atomically do
    let st ← getThe Slot
    if st.state != .ready then return Except.error st.state
    if st.readers.isEmpty then return Except.error st.state
    let i := st.readerIdx % st.readers.size
    set { st with readerIdx := st.readerIdx + 1 }
    match st.readers[i]? with
    | some m => return Except.ok m
    | none => return Except.error st.state
  match picked with
  | .error st => return Except.error (.notReady st)
  | .ok mtx =>
      try
        Except.ok <$> mtx.atomically fun ref => do f (← ref.get)
      catch e => return Except.error (.host (toString e))

/-- Stop admitting work and wait for the in-flight call to finish. -/
def drain (s : Service) : IO Unit :=
  s.slot.atomically do
    let st ← getThe Slot
    if st.state == .ready then set { st with state := .draining }

/-- Admit work again after `drain`. -/
def resume (s : Service) : IO Unit :=
  s.slot.atomically do
    let st ← getThe Slot
    if st.state == .draining then set { st with state := .ready }

/-- `dest.tmp`: a snapshot writes here and renames on success, so a
    failed snapshot leaves no torn output at `dest` (LDB-13). -/
private def snapshotTmp (dest : System.FilePath) : System.FilePath :=
  s!"{dest}.tmp"

/-- Give up a snapshot: remove the partial output and clear the job, so
    `restore` stops waiting and a new snapshot may start. -/
private def snapshotCleanup (s : Service) (job : SnapshotJob) : IO Unit := do
  try IO.FS.removeFile job.tmp catch _ => pure ()
  s.slot.atomically do
    modify fun st => { st with snapshotJob := none }

/-- Move the finished backup into place and record the stat. A failure
    removes the partial output; nothing torn is left at `dest`. -/
private def snapshotFinish (s : Service) (job : SnapshotJob) (dest : System.FilePath)
    (start : Nat) : IO (Except RuntimeError Unit) := do
  try
    let bytes := (← System.FilePath.metadata job.tmp).byteSize.toNat
    IO.FS.rename job.tmp dest
    let durationMs := (← IO.monoMsNow) - start
    let stat : SnapshotStat := { lane := job.lane, durationMs, bytes }
    s.slot.atomically do
      modify fun st => { st with snapshotJob := none, lastSnapshot := some stat }
    return .ok ()
  catch e =>
    discard <| s.snapshotCleanup job
    return .error (.host (toString e))

/-- A consistent copy of the instance at `dest` (`VACUUM INTO`), on the
    caller's chosen lane. The reader lane runs the backup on a pooled
    read-only connection — no WAL checkpoint, which a reader cannot run;
    `VACUUM INTO` reads through the WAL itself — outside the writer lock,
    so the writer keeps serving. The backup is written to `dest.tmp` and
    renamed on success. At most one snapshot runs at a time
    (`.snapshotBusy`), and `restore` waits for the running one before its
    file swap (LDB-13). With the writer lane — or with `readers := 0`,
    where the fallback is logged — the backup holds the writer connection
    for its whole duration, the pre-LDB-13 behaviour. -/
def snapshotOn (s : Service) (lane : SnapshotLane) (dest : System.FilePath) :
    IO (Except RuntimeError Unit) := do
  if ← dest.pathExists then
    return .error (.host s!"backup target already exists: {dest}")
  try IO.FS.removeFile (snapshotTmp dest) catch _ => pure ()
  let start ← IO.monoMsNow
  let tmp := snapshotTmp dest
  -- Which connection runs the backup: a pooled reader when the caller
  -- asked for the reader lane and readers exist, the writer otherwise.
  let reg : Except RuntimeError (SnapshotJob × Option (Std.Mutex Conn)) ← s.slot.atomically do
    let st ← getThe Slot
    if st.state != .ready then return .error (.notReady st.state)
    if st.snapshotJob.isSome then return .error .snapshotBusy
    let useReader := lane == .reader && !st.readers.isEmpty
    if !useReader && lane == .reader then
      IO.eprintln "leandb: snapshot falls back to the writer connection (no reader connections configured; set Config.readers)"
    let abort ← IO.mkRef false
    let job : SnapshotJob := { lane := if useReader then .reader else .writer, tmp, abort }
    let conn? : Option (Std.Mutex Conn) :=
      if useReader then
        -- round-robin over the pool, the same rule as `withReader`
        let i := st.readerIdx % st.readers.size
        st.readers[i]?
      else none
    set { st with readerIdx := st.readerIdx + (if useReader then 1 else 0), snapshotJob := some job }
    return .ok (job, conn?)
  match reg with
  | .error e => return .error e
  | .ok (job, conn?) =>
    match conn? with
    | some mtx =>
        -- reader lane: the pool is not the writer lock, so run outside it,
        -- but hold the pool slot's own lock for the whole backup, so no
        -- `withReader` / `runRead` shares the handle or sees `query_only`
        -- lifted. `query_only` refuses a `VACUUM INTO` even on a read-only
        -- connection; the connection is `SQLITE_OPEN_READONLY`, so the
        -- pragma is only lifted for the backup, which writes the target
        -- file, never the instance.
        let r ←
          try
            mtx.atomically fun ref => do
              let conn ← ref.get
              conn.raw.exec "PRAGMA query_only = OFF"
              try backupTo conn tmp (checkpoint := false)
              finally conn.raw.exec "PRAGMA query_only = ON"
            if ← job.abort.get then
              -- restore claimed the connection while the `VACUUM INTO`
              -- ran; it cannot be interrupted, so stand down before the
              -- rename
              discard <| s.snapshotCleanup job
              pure (.error .snapshotAborted)
            else s.snapshotFinish job dest start
          catch e =>
            discard <| s.snapshotCleanup job
            pure (.error (.host (toString e)))
        return r
    | none =>
        -- writer lane: hold the writer for the whole backup, as before;
        -- `restore` serializes behind the same lock
        match ← s.withConnection fun conn => backupTo conn tmp (checkpoint := true) with
        | .error e =>
            discard <| s.snapshotCleanup job
            return .error e
        | .ok () => s.snapshotFinish job dest start

/-- A consistent copy of the instance at `dest`, on the reader lane when
    readers are configured and on the writer (logged) otherwise. -/
def snapshot (s : Service) (dest : System.FilePath) : IO (Except RuntimeError Unit) :=
  s.snapshotOn .reader dest

/-- Replace the instance file with `src` and reopen: drain, swap under a
    temporary name (`Restore.swapFile` validates first), reopen, re-verify.
    A reopen failure leaves the service gated rather than serving a file
    it could not open. Waits for a running snapshot first: the snapshot is
    asked to stand down before its rename — it fails typed
    (`.snapshotAborted`) and its partial output is removed — so the swap
    never happens under a reader's `VACUUM INTO` (LDB-13). -/
def restore (s : Service) (src : System.FilePath) : IO (Except RuntimeError Unit) := do
  -- claim the connection: refuse closed, mark restoring (new admissions
  -- are refused with `.notReady .restoring`), and learn whether a
  -- snapshot is mid-flight. The writer lane holds the same lock, so what
  -- is found here can only be a reader-lane snapshot.
  let claimed : Except RuntimeError (Option SnapshotJob) ← s.slot.atomically do
    let st ← getThe Slot
    if st.state == .closed then return Except.error (.notReady .closed)
    set { st with state := .restoring }
    return Except.ok st.snapshotJob
  match claimed with
  | .error e => return .error e
  | .ok none => pure ()
  | .ok (some job) =>
      job.abort.set true
      -- wait for it to stand down: poll the slot (briefly) until the job
      -- is gone; the `VACUUM INTO` itself cannot be interrupted
      repeat
        let gone : Bool ← s.slot.atomically do
          let st ← getThe Slot
          return !st.snapshotJob.any (·.tmp == job.tmp)
        if gone then break
        IO.sleep 10
  s.slot.atomically do
    let st ← getThe Slot
    -- a `close` may have landed between the claim and here
    if st.state != .restoring then return .error (.notReady st.state)
    let r ← Restore.swapFile s.inst.path src
    match r with
    | .error e =>
        set { (← getThe Slot) with state := .ready }
        return .error (.host e.message)
    | .ok () =>
    match ← openDbRaw s.inst.path s.base.log with
    | .ok conn =>
        let gate ← gateOf s.base conn
        set { (← getThe Slot) with conn, state := .ready, gate }
        return .ok ()
    | .error e =>
        -- the swap succeeded but the file did not open: gate loudly
        -- instead of serving whatever the old connection still sees (#77)
        set { (← getThe Slot) with state := .ready, gate := some e }
        return .error (.gated e)

/-- Close the service: drain, mark closed. The `Conn` is dropped; SQLite
    closes when the handle is collected. Terminal. -/
def close (s : Service) : IO Unit :=
  s.slot.atomically do
    let st ← getThe Slot
    set { st with state := .closed }

end Service

/-- Private diagnostics: instance paths, lifecycle, gate. Never a public
    API surface — it names files on the host. -/
def status (s : Service) : IO Lean.Json := do
  let st ← s.slot.atomically (return ← getThe Slot)
  return Lean.Json.mkObj [
    ("base", Lean.Json.str s.base.name),
    ("database", Lean.Json.str s.inst.path.toString),
    ("backups", Lean.Json.str s.inst.backups.toString),
    ("session", Lean.Json.str (if s.session.readOnly then "inspect" else "serve")),
    ("read_only", Lean.Json.bool s.session.readOnly),
    ("state", Lean.Json.str (toString (repr st.state))),
    ("ready", Lean.Json.bool (st.state == .ready && st.gate.isNone && !s.session.readOnly)),
    ("gated", Lean.Json.bool st.gate.isSome),
    ("gate", (st.gate.map (Lean.Json.str ·.message)).getD Lean.Json.null),
    ("snapshot", (st.snapshotJob.map fun job => Lean.Json.str job.lane.name).getD Lean.Json.null),
    ("last_snapshot", (st.lastSnapshot.map fun stat => Lean.Json.mkObj
      [("lane", Lean.Json.str stat.lane.name),
       ("duration_ms", Lean.toJson stat.durationMs),
       ("bytes", Lean.toJson stat.bytes)]).getD Lean.Json.null)]

end LeanDb.Runtime
