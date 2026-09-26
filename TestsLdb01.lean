import LeanDb
import FixturePortable

deriving instance LeanDb.ClosedEnum for PortableRole
deriving instance LeanDb.Inline for PortableReply

/-! LDB-01: the public transaction combinator and `LeanDb.Runtime.Service`.

Engine-level acceptance tests: nested savepoint rollback leaves the outer
transaction intact; `.abort` returns the value and rolls back; `BEGIN
IMMEDIATE` blocks a second writer until commit; reentrancy through
`withConnection` is a typed error; a throwing callback leaves the service
ready. -/

namespace TestsLdb01

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def check' (condition : Bool) (message : String) : DbM Unit :=
  unless condition do throw (.sqlite s!"FAIL: {message}")

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

structure TxAuthor where
  name : String
  deriving Repr, LeanDb.Entity

private def specs : List TableSpec := [Entity.spec TxAuthor]

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb01.sqlite"
private def dbPath2 : System.FilePath := ".lake" / "leandb_test_ldb01_svc.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

/-- `.abort` returns the value and rolls the write back. -/
private def testAbort : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    let r ← transaction do
      discard <| insert TxAuthor ⟨"ghost"⟩
      return (Tx.abort "domain says no" : Tx String Unit)
    check' (r matches .error "domain says no") "abort carries the domain value"
    let all ← fetchAll TxAuthor
    check' all.isEmpty "aborted insert leaves no row"
  discard <| expectOk r "abort test"

/-- A nested transaction aborts via savepoint; the outer commits. -/
private def testNestedSavepoint : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    let r : Except String Unit ← transaction do
      discard <| insert TxAuthor ⟨"outer"⟩
      let inner ← transaction do
        discard <| insert TxAuthor ⟨"inner"⟩
        return (Tx.abort "inner abort" : Tx String Unit)
      check' (inner matches .error "inner abort") "inner abort value"
      return Tx.commit ()
    check' (r matches .ok ()) "outer commits despite inner abort"
    let names ← (·.map (·.val.name)) <$> fetchAll TxAuthor
    check' (names == #["outer"]) s!"outer row survives, inner rolled back (got {names})"
  discard <| expectOk r "nested savepoint test"

/-- `withTransaction` commits; a `DbError` inside rolls back and re-raises. -/
private def testWithTransaction : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    withTransaction do
      discard <| insert TxAuthor ⟨"committed"⟩
    let names ← (·.map (·.val.name)) <$> fetchAll TxAuthor
    check' (names == #["committed"]) "withTransaction commits"
  discard <| expectOk r "withTransaction commit"
  let r ← withDb dbPath specs do
    let act : DbM Unit := withTransaction do
      discard <| insert TxAuthor ⟨"rolled back"⟩
      throw (.sqlite "boom")
    match ← (fun conn => ExceptT.mk (.ok <$> (act conn).run)) with
    | .error e => check' (e.code == "sqlite") "error re-raised"
    | .ok () => throw (.sqlite "FAIL: expected error")
    let names ← (·.map (·.val.name)) <$> fetchAll TxAuthor
    check' (names == #["committed"]) "failed withTransaction rolled back"
  discard <| expectOk r "withTransaction rollback"

/-- `untrackedSqlite` runs raw SQL inside the open transaction. -/
private def testUntracked : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    withTransaction do
      discard <| insert TxAuthor ⟨"typed"⟩
      untrackedSqlite fun db =>
        db.exec "INSERT INTO \"tx_author\" (\"name\") VALUES ('raw')"
    let names ← (·.map (·.val.name)) <$> fetchAll TxAuthor
    check' (names == #["typed", "raw"]) "raw write inside the transaction commits"
  discard <| expectOk r "untrackedSqlite"

/-- `BEGIN IMMEDIATE` holds the write lock: a second connection's write
    waits for the first commit (busy_timeout honoured). -/
private def testImmediateBlocks : IO Unit := do
  fresh dbPath
  discard <| expectOk (← withDb dbPath specs (pure ())) "create"
  let conn1 ← expectOk (← openDb dbPath specs) "conn1"
  let conn2 ← expectOk (← openDb dbPath specs) "conn2"
  -- conn1 holds BEGIN IMMEDIATE for ~400ms; conn2's writer must land after.
  let t1 ← IO.asTask (prio := .default) do
    DbM.run conn1 <| transaction do
      discard <| insert TxAuthor ⟨"first"⟩
      untrackedSqlite fun _ => IO.sleep 400
      return (Tx.commit (← IO.monoMsNow) : Tx String Nat)
  IO.sleep 100
  let started ← IO.monoMsNow
  let r2 ← DbM.run conn2 <| withTransaction do
    discard <| insert TxAuthor ⟨"second"⟩
  let done ← IO.monoMsNow
  discard <| expectOk r2 "second writer waits then commits"
  let committedAt := (← expectOk (← IO.ofExcept t1.get) "first transaction").toOption.getD 0
  check (done >= committedAt) s!"second writer ran before first committed ({done} < {committedAt})"
  check (done - started >= 200) s!"second writer did not wait ({done - started}ms)"
  let names ← expectOk (← DbM.run conn1 ((·.map (·.val.name)) <$> fetchAll TxAuthor)) "read back"
  check (names == #["first", "second"]) s!"both rows committed: {names}"

private def svcBase : Base :=
  { name := "ldb01svc", tables := [CliTable.of TxAuthor] }

/-- `withConnection` reentrancy is a typed error; a throwing callback
    leaves the service ready; drain/resume/close gate admission. -/
private def testService : IO Unit := do
  fresh dbPath2
  let svc ← Runtime.Service.new svcBase (Instance.ofPath dbPath2) .serve true
  check (← svc.ready) "service ready after open"
  check ((← svc.state) == .ready) "state ready"
  check (!svc.session.readOnly) "serve session is not read-only"
  -- reentrancy: the callback calls back in on the same thread
  let r : Except Runtime.RuntimeError (Except Runtime.RuntimeError Unit) ←
    svc.withConnection fun _ => svc.withConnection fun _ => pure ()
  match r with
  | .ok (.error .reentrant) | .error .reentrant => pure ()
  | _ => throw <| IO.userError "FAIL: reentrant withConnection must be rejected"
  -- a throwing callback becomes .host and the service stays ready
  let r : Except Runtime.RuntimeError Unit ← svc.withConnection fun _ =>
    throw <| IO.userError "boom"
  match r with
  | .error (.host _) => pure ()
  | _ => throw <| IO.userError "FAIL: host exception must be typed"
  check (← svc.ready) "service ready after a throwing callback"
  -- work runs on the connection
  let r : Except Runtime.RuntimeError _ ← svc.withConnection fun conn =>
    DbM.run conn (insert TxAuthor ⟨"via service"⟩)
  match r with
  | .ok (.ok _) => pure ()
  | _ => throw <| IO.userError s!"FAIL: insert through service: {repr r}"
  -- drain refuses new admission, resume restores it
  svc.drain
  check ((← svc.state) == .draining) "draining state"
  check (!(← svc.ready)) "not ready while draining"
  let r ← svc.withConnection fun _ => pure ()
  check (r matches .error (.notReady .draining)) "drain refuses admission"
  svc.resume
  check (← svc.ready) "ready after resume"
  -- snapshot writes a copy
  let snap : System.FilePath := ".lake" / "leandb_test_ldb01_snap.sqlite"
  if ← snap.pathExists then IO.FS.removeFile snap
  let r ← svc.snapshot snap
  check r.isOk "snapshot succeeds"
  check (← snap.pathExists) "snapshot file exists"
  -- restore replaces the file and re-verifies
  let r ← svc.restore snap
  check r.isOk s!"restore succeeds: {repr r}"
  check (← svc.ready) "ready after restore"
  -- status reports private diagnostics
  let st ← Runtime.status svc
  check ((st.getObjValAs? String "database").toOption == some dbPath2.toString)
    "status names the database"
  check ((st.getObjValAs? Bool "ready").toOption == some true) "status ready"
  -- close is terminal
  svc.close
  check ((← svc.state) == .closed) "closed state"
  let r ← svc.withConnection fun _ => pure ()
  check (r matches .error (.notReady .closed)) "closed refuses admission"

/-- An inspection session is never ready. -/
private def testInspectSession : IO Unit := do
  fresh dbPath2
  let svc ← Runtime.Service.new svcBase (Instance.ofPath dbPath2) .inspect true
  check (svc.session.readOnly) "inspect session is read-only"
  check (!(← svc.ready)) "inspection session is never ready"
  svc.close

structure IndexedDoc where
  doc : String
  revision : Nat
  deriving Repr, LeanDb.Entity

instance : Indexes IndexedDoc where
  indexes := #[{ unique := true, columns := #["doc", "revision"] }]

structure Counted where
  tag : String
  deriving Repr, LeanDb.Entity

structure PortableRow where
  role : PortableRole
  note : String
  deriving Repr, LeanDb.Entity

private def io (act : IO α) : DbM α :=
  fun _ => ExceptT.mk (Except.ok <$> act)

private def testIndexes : IO Unit := do
  fresh dbPath
  let specs := [Entity.spec IndexedDoc]
  check ((Entity.spec IndexedDoc).indexes.size == 1) "Indexes instance reaches TableSpec"
  let r ← withDb dbPath specs do
    discard <| insert IndexedDoc ⟨"a", 1⟩
    let act : DbM Unit := discard <| insert IndexedDoc ⟨"a", 1⟩
    match ← (fun conn => ExceptT.mk (.ok <$> (act conn).run)) with
    | .error e => check' (e.code == "duplicate") "unique index names the violation"
    | .ok () => throw (.sqlite "FAIL: expected duplicate")
  discard <| expectOk r "indexes"

private def testCountExists : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath [Entity.spec Counted] do
    discard <| insert Counted ⟨"x"⟩
    discard <| insert Counted ⟨"x"⟩
    discard <| insert Counted ⟨"y"⟩
    let n ← countP (ts := [Counted]) .tt
    check' (n == 3) s!"countP tt = 3, got {n}"
    let yes ← existsP (ts := [Counted]) .tt
    check' yes "existsP tt"
  discard <| expectOk r "count/exists"

private def testPatchInsertManyScan : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath [Entity.spec Counted] do
    let stored ← insertMany Counted #[⟨"a"⟩, ⟨"b"⟩, ⟨"c"⟩]
    check' (stored.size == 3) "insertMany returns 3"
    let some first := stored[0]? | throw (.sqlite "FAIL: empty insertMany")
    let p : Patch Counted :=
      { sets := #[Assignment.of Counted.Field.tag "aa"] }
    let pr ← patch first.id p
    check' (pr == .updated) "patch updates"
    let got ← get first.id
    check' (got.map (·.val.tag) == some "aa") "patched column"
    let n ← io (IO.mkRef (0 : Nat))
    scan (α := Counted) .tt 2 fun chunk => do
      io (n.modify (· + chunk.size))
      return true
    let total ← io n.get
    check' (total == 3) s!"scan visited {total}"
  discard <| expectOk r "patch/insertMany/scan"

private def testOpenConfigAndLogPolicy : IO Unit := do
  fresh dbPath
  let log : LogConfig := { verbs := .failuresOnly }
  let conn ← expectOk (← openDb dbPath [Entity.spec Counted] log
    { synchronous := .normal, busyTimeoutMs := 2500 }) "open with config"
  discard <| expectOk (← DbM.run conn (insert Counted ⟨"z"⟩)) "insert"
  let logs ← expectOk (← DbM.run conn (readLog 10)) "readLog"
  check (logs.isEmpty) s!"failuresOnly writes no success rows, got {logs.size}"
  check (conn.openConfig.synchronous == .normal) "openConfig recorded"
  check (!conn.readOnly) "writer is not read-only"

private def testPostHocDeriving : IO Unit := do
  fresh dbPath
  check (ClosedEnum.variants (α := PortableRole) == #["admin", "user"])
    "post-hoc ClosedEnum variants"
  let r ← withDb dbPath [Entity.spec PortableRow] do
    discard <| insert PortableRow ⟨.admin, "ok"⟩
    let rows ← fetchAll PortableRow
    check' (rows.size == 1) "portable row round-trips"
  discard <| expectOk r "post-hoc deriving"

private def testReadOnlyGuard : IO Unit := do
  fresh dbPath
  discard <| expectOk (← withDb dbPath [Entity.spec Counted] (pure ())) "create"
  let ro ← expectOk (← openDbRaw dbPath {} {} true) "open readonly"
  check ro.readOnly "flag set"
  let r ← DbM.run ro (insert Counted ⟨"nope"⟩)
  match r with
  | .error e => check (e.code == "read_only") s!"readOnly error, got {e}"
  | .ok _ => throw <| IO.userError "FAIL: write on readonly must fail"


/-! ## Snapshot lanes (LDB-13)

`snapshot` runs its `VACUUM INTO` on a pooled reader, so the writer
keeps committing during the backup; `readers := 0` still has the one
dedicated reader (LDB-19), so there is no writer fallback. The output is
written to `dest.tmp` and renamed on success, `restore` waits for a
running snapshot (typed `.snapshotAborted`, no torn output), and
`status` reports the last snapshot's lane, duration and size. -/

structure SnapRow where
  tag : String
  padding : String
  deriving Repr, LeanDb.Entity

private def snapBase : Base :=
  { name := "ldb13", tables := [CliTable.of SnapRow] }

private def snapDbPath : System.FilePath := ".lake" / "leandb_test_ldb13.sqlite"
private def snapDest : System.FilePath := ".lake" / "leandb_test_ldb13_snap.sqlite"
private def snapDest2 : System.FilePath := ".lake" / "leandb_test_ldb13_snap2.sqlite"
private def snapTmpOf (d : System.FilePath) : System.FilePath :=
  System.FilePath.mk (d.toString ++ ".tmp")

/-- Seed `n` rows of `pad`-character padding through the writer
    connection. -/
private def seedRows (svc : Runtime.Service) (n : Nat) (pre : String := "seed")
    (pad : Nat := 64) : IO Nat := do
  let r ← svc.withConnection fun conn =>
    DbM.run conn do
      withTransaction do
        let rows : Array SnapRow := (Array.range n).map fun i =>
          ⟨s!"{pre}-{i}", String.mk (List.replicate pad 'x')⟩
        discard <| insertMany SnapRow rows
      let stored ← fetchAll SnapRow
      return stored.size
  match r with
  | .ok (.ok n) => pure n
  | .ok (.error e) | .error e => throw <| IO.userError s!"FAIL: seeding rows: {repr e}"

/-- `PRAGMA quick_check` over a copy: the snapshot is a valid database. -/
private def quickCheckOk (p : System.FilePath) : IO Bool := do
  let db ← SQLite.open p
  let stmt ← db.prepare "PRAGMA quick_check"
  discard <| stmt.step
  return (← stmt.columnText 0) == "ok"

/-- Is a snapshot in flight? `status` reports the running snapshot's
    lane, or null (LDB-13 diagnostics). -/
private def snapshotRunning (svc : Runtime.Service) : IO Bool := do
  let st ← Runtime.status svc
  match st.getObjVal? "snapshot" with
  | .ok j => return !(j matches .null)
  | .error _ => return false

/-- The `last_snapshot` object `status` reports (LDB-13). -/
private def lastSnapshotOf (svc : Runtime.Service) : IO Lean.Json := do
  let st ← Runtime.status svc
  return (st.getObjVal? "last_snapshot").toOption.getD .null

/-- With `readers := 1` the snapshot runs on the reader while the writer
    keeps committing every ~10 ms: every commit lands, the copy is a
    valid database, and `restore` accepts it. -/
private def testSnapshotReaderLane : IO Unit := do
  fresh snapDbPath
  if ← snapDest.pathExists then IO.FS.removeFile snapDest
  try IO.FS.removeFile (snapTmpOf snapDest) catch _ => pure ()
  let svc ← Runtime.Service.new snapBase (Instance.ofPath snapDbPath) .serve true
    { readers := 1 }
  discard <| seedRows svc 2000
  -- the writer commits every ~10 ms while the snapshot runs
  let commits ← IO.asTask (prio := .default) do
    let mut ok := 0
    for i in [0:60] do
      let r ← svc.withConnection fun conn =>
        DbM.run conn do
          withTransaction do
            discard <| insert SnapRow ⟨s!"commit-{i}", "c"⟩
          pure ()
      match r with
      | .ok (.ok ()) => ok := ok + 1
      | .ok (.error e) | .error e => throw <| IO.userError s!"FAIL: commit {i} failed: {repr e}"
      IO.sleep 10
    return ok
  -- the reader-lane snapshot overlaps the commit loop
  let snapTask ← IO.asTask (prio := .default) do
    svc.snapshot snapDest
  let snapResult ← IO.ofExcept snapTask.get
  let commitsOk ← IO.ofExcept commits.get
  match snapResult with
  | .ok () => pure ()
  | .error e => throw <| IO.userError s!"FAIL: reader-lane snapshot: {repr e}"
  check (commitsOk == 60) s!"every commit succeeded during the snapshot, got {commitsOk}"
  -- no torn output: only the renamed copy, never `dest.tmp`
  check (← snapDest.pathExists) "snapshot file exists"
  check (!(← (snapTmpOf snapDest).pathExists)) "no snapshot tmp left behind"
  check (← quickCheckOk snapDest) "snapshot passes PRAGMA quick_check"
  -- `restore` accepts the reader-lane copy
  let r ← svc.restore snapDest
  check r.isOk s!"restore accepts the snapshot: {repr r}"
  check (← svc.ready) "ready after restore"
  -- status reports the lane, duration and size of the last snapshot
  let stat ← lastSnapshotOf svc
  check ((stat.getObjValAs? String "lane").toOption == some "reader")
    s!"last snapshot ran on the reader lane: {stat}"
  let durMs := (stat.getObjValAs? Nat "duration_ms").toOption.getD 0
  check (durMs > 0) s!"duration reported: {stat}"
  let bytes := (stat.getObjValAs? Nat "bytes").toOption.getD 0
  check (bytes > 0) s!"size reported: {stat}"
  -- the restored instance serves the snapshot's data (2000 seeded rows,
  -- plus whatever committed before the backup's read snapshot)
  let r ← svc.withConnection fun conn =>
    DbM.run conn do
      let stored ← fetchAll SnapRow
      return stored.size
  match r with
  | .ok (.ok n) => check (n >= 2000) s!"restored instance serves the snapshot's rows, got {n}"
  | .ok (.error e) | .error e => throw <| IO.userError s!"FAIL: read after restore: {repr e}"
  svc.close

/-- Is `PRAGMA query_only` on for this connection? -/
private def queryOnly (conn : Conn) : IO Bool := do
  let stmt ← conn.raw.prepare "PRAGMA query_only"
  discard <| stmt.step
  return (← stmt.columnInt64 0) == 1

/-- The reader-lane snapshot holds its pool slot's lock for the whole
    backup: with `readers := 1` a `withReader` that arrives mid-backup
    runs only once the `VACUUM INTO` is complete, the snapshot waits for
    a callback that holds the only slot, and readers see `query_only`
    back on after a snapshot that succeeded and after one that failed. -/
private def testSnapshotHoldsReader : IO Unit := do
  fresh snapDbPath
  for p in [snapDest, snapDest2] do
    if ← p.pathExists then IO.FS.removeFile p
    try IO.FS.removeFile (snapTmpOf p) catch _ => pure ()
  let svc ← Runtime.Service.new snapBase (Instance.ofPath snapDbPath) .serve true
    { readers := 1 }
  discard <| seedRows svc 30000 "seed" 200
  -- a reader arriving once the backup has started writing `dest.tmp`
  -- waits for it: its callback sees the output at its final size, or
  -- already renamed into place
  let tmp2 := snapTmpOf snapDest2
  let snapTask ← IO.asTask (prio := .dedicated) (svc.snapshot snapDest2)
  repeat
    if (← tmp2.pathExists) || (← IO.hasFinished snapTask) then break
    IO.sleep 1
  let seen ← svc.withReader fun _ => do
    if ← snapDest2.pathExists then return none
    try return some (← System.FilePath.metadata tmp2).byteSize catch _ => return none
  let r ← IO.ofExcept snapTask.get
  check r.isOk s!"snapshot under a waiting reader: {repr r}"
  let final := (← System.FilePath.metadata snapDest2).byteSize
  match seen with
  | .ok none => pure ()
  | .ok (some n) => check (n == final) s!"a reader ran mid-backup: saw {n} of {final} bytes"
  | .error e => throw <| IO.userError s!"FAIL: reader during snapshot: {repr e}"
  -- a reader callback takes the only slot and keeps it for 200 ms
  let taken ← IO.mkRef false
  let released ← IO.mkRef 0
  let held ← IO.asTask (prio := .dedicated) do
    svc.withReader fun conn => do
      taken.set true
      IO.sleep 200
      released.set (← IO.monoMsNow)
      queryOnly conn
  repeat
    if ← taken.get then break
    IO.sleep 2
  let r ← svc.snapshot snapDest
  let doneAt ← IO.monoMsNow
  check r.isOk s!"snapshot on the held slot: {repr r}"
  let heldR ← IO.ofExcept held.get
  check (heldR matches .ok true) s!"the holding reader saw query_only on: {repr heldR}"
  check (doneAt >= (← released.get)) "the snapshot waited for the reader holding its slot"
  let ro ← svc.withReader queryOnly
  check (ro matches .ok true) s!"query_only is back on after a snapshot: {repr ro}"
  -- a failed backup restores it too: the destination's parent is a file,
  -- so `backupTo` throws while the pragma is lifted
  let r ← svc.snapshot (snapDest / "nested.sqlite")
  check (r matches .error (.host _)) s!"snapshot under a file fails: {repr r}"
  let ro ← svc.withReader queryOnly
  check (ro matches .ok true) s!"query_only is back on after a failed snapshot: {repr ro}"
  svc.close

/-- With `readers := 0` the snapshot still runs on the reader lane — the
    pool's dedicated slot, not the writer — and produces a valid copy;
    the writer lane runs only when asked for. -/
private def testSnapshotNoReaders : IO Unit := do
  fresh snapDbPath
  for p in [snapDest, snapDest2] do
    if ← p.pathExists then IO.FS.removeFile p
    try IO.FS.removeFile (snapTmpOf p) catch _ => pure ()
  let svc ← Runtime.Service.new snapBase (Instance.ofPath snapDbPath) .serve true
    { readers := 0 }
  discard <| seedRows svc 5
  let r ← svc.snapshot snapDest
  match r with
  | .ok () => pure ()
  | .error e => throw <| IO.userError s!"FAIL: snapshot with readers := 0: {repr e}"
  check (← snapDest.pathExists) "snapshot wrote the file"
  check (!(← (snapTmpOf snapDest).pathExists)) "no snapshot tmp left behind"
  check (← quickCheckOk snapDest) "snapshot passes quick_check"
  let stat ← lastSnapshotOf svc
  check ((stat.getObjValAs? String "lane").toOption == some "reader")
    s!"readers := 0 still snapshots on the reader lane: {stat}"
  -- the writer lane is an explicit choice
  let r ← svc.snapshotOn .writer snapDest2
  check r.isOk s!"explicit writer lane: {repr r}"
  let stat ← lastSnapshotOf svc
  check ((stat.getObjValAs? String "lane").toOption == some "writer")
    s!"writer lane recorded: {stat}"
  svc.close

/-- `snapshotOn .writer` on a service with readers runs on the writer and
    refuses a second snapshot while one is running or the destination
    already exists. -/
private def testSnapshotWriterLane : IO Unit := do
  fresh snapDbPath
  for p in [snapDest, snapDest2] do
    if ← p.pathExists then IO.FS.removeFile p
    try IO.FS.removeFile (snapTmpOf p) catch _ => pure ()
  let svc ← Runtime.Service.new snapBase (Instance.ofPath snapDbPath) .serve true
    { readers := 1 }
  discard <| seedRows svc 100
  let r ← svc.snapshotOn .writer snapDest
  match r with
  | .ok () => pure ()
  | .error e => throw <| IO.userError s!"FAIL: writer-lane snapshot: {repr e}"
  let stat ← lastSnapshotOf svc
  check ((stat.getObjValAs? String "lane").toOption == some "writer")
    s!"explicit writer lane is recorded: {stat}"
  -- the destination exists now: a second snapshot to it is refused
  let r2 ← svc.snapshotOn .writer snapDest
  check (r2 matches .error (.host _)) s!"existing destination refused: {repr r2}"
  -- while a snapshot runs, a second one is refused with a typed error
  discard <| seedRows svc 1200 "more"
  let busy ← IO.asTask (prio := .default) do svc.snapshotOn .reader snapDest2
  IO.sleep 30 -- let the overlapping snapshot register its job
  let r3 ← svc.snapshotOn .writer snapDest2
  match r3 with
  | .error .snapshotBusy => pure ()
  | .error (.host _) => pure () -- the first snapshot finished before the second registered
  | other => throw <| IO.userError s!"FAIL: concurrent snapshot must be refused, got {repr other}"
  let busyR ← IO.ofExcept busy.get
  check busyR.isOk s!"the overlapping snapshot itself succeeded: {repr busyR}"
  svc.close

/-- `restore` while a reader snapshot runs: the snapshot either finishes
    first or stands down with a typed error; no torn output is left and
    the instance serves the restored data. -/
private def testRestoreDuringSnapshot : IO Unit := do
  fresh snapDbPath
  for p in [snapDest, snapDest2] do
    if ← p.pathExists then IO.FS.removeFile p
    try IO.FS.removeFile (snapTmpOf p) catch _ => pure ()
  let svc ← Runtime.Service.new snapBase (Instance.ofPath snapDbPath) .serve true
    { readers := 1 }
  discard <| seedRows svc 2000
  -- the restore source: a good copy taken before more rows arrive
  let r0 ← svc.snapshotOn .writer snapDest
  -- extra rows so the second snapshot has real work: a multi-megabyte
  -- `VACUUM INTO` is still running when the restore claims the lane
  discard <| seedRows svc 30000 "extra" 200
  -- a reader-lane snapshot; restore claims the connection mid-backup
  let snapTask ← IO.asTask (prio := .default) do
    svc.snapshotOn .reader snapDest2
  -- wait until the snapshot has registered its job (status shows the
  -- running lane), so the restore is guaranteed to claim mid-backup
  let mut polls := 0
  repeat
    if ← snapshotRunning svc then break
    if polls > 500 then throw <| IO.userError "FAIL: snapshot never registered"
    polls := polls + 1
    IO.sleep 2
  let restoreR ← svc.restore snapDest
  let snapR ← IO.ofExcept snapTask.get
  match snapR with
  | .ok () => check restoreR.isOk s!"snapshot finished first, restore followed: {repr restoreR}"
  | .error .snapshotAborted =>
      check restoreR.isOk s!"snapshot stood down typed, restore completed: {repr restoreR}"
  | .error e => throw <| IO.userError s!"FAIL: unexpected snapshot error: {repr e}"
  -- no torn output either way
  check (!(← (snapTmpOf snapDest2).pathExists)) "no partial snapshot output left"
  check (← svc.ready) "ready after restore"
  -- the instance serves the restored data: the restore source's 2000 rows
  let r ← svc.withConnection fun conn =>
    DbM.run conn do
      let stored ← fetchAll SnapRow
      return stored.size
  match r with
  | .ok (.ok n) => check (n == 2000) s!"post-restore instance holds the backup's rows, got {n}"
  | .ok (.error e) | .error e => throw <| IO.userError s!"FAIL: read after restore-during-snapshot: {repr e}"
  svc.close

def run : IO Unit := do
  testAbort
  testNestedSavepoint
  testWithTransaction
  testUntracked
  testImmediateBlocks
  testService
  testSnapshotReaderLane
  testSnapshotHoldsReader
  testSnapshotNoReaders
  testSnapshotWriterLane
  testRestoreDuringSnapshot
  testInspectSession
  testIndexes
  testCountExists
  testPatchInsertManyScan
  testOpenConfigAndLogPolicy
  testPostHocDeriving

end TestsLdb01
