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
  deriving Repr

def RuntimeError.message : RuntimeError → String
  | .host m => s!"host error: {m}"
  | .notReady s => s!"service is not ready (state: {repr s})"
  | .reentrant => "withConnection called reentrantly from its own callback"
  | .gated e => s!"instance gated: {e.message}"

instance : ToString RuntimeError := ⟨RuntimeError.message⟩

/-- Mutable service state, inside the lock. -/
private structure Slot where
  conn : Conn
  state : State
  depth : Nat := 0
  gate : Option DbError := none
  readers : Array (Std.Mutex Conn) := #[]
  readerIdx : Nat := 0

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

/-- A consistent copy of the instance at `dest` (`VACUUM INTO`), run on
    the connection under the lock. -/
def snapshot (s : Service) (dest : System.FilePath) : IO (Except RuntimeError Unit) :=
  s.withConnection fun conn => backupTo conn dest

/-- Replace the instance file with `src` and reopen: drain, swap under a
    temporary name (`Restore.swapFile` validates first), reopen, re-verify.
    A reopen failure leaves the service gated rather than serving a file
    it could not open. -/
def restore (s : Service) (src : System.FilePath) : IO (Except RuntimeError Unit) :=
  s.slot.atomically do
    let st ← getThe Slot
    if st.state == .closed then return .error (.notReady .closed)
    set { st with state := .restoring }
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
    ("gate", (st.gate.map (Lean.Json.str ·.message)).getD Lean.Json.null)]

end LeanDb.Runtime
