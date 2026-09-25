import LeanDb

/-! LDB-19: `withReader` locks each pooled connection and never hands
    out the writer. With `readers := 0` it still opens a dedicated
    read-only connection; writes on it are `.readOnly`. -/

namespace TestsLdb19

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

structure Item where
  name : String
  deriving Repr, LeanDb.Entity

private def svcBase : Base :=
  { name := "ldb19", tables := [CliTable.of Item] }

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb19.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

/-- `readers := 0` must not fall back to the writer: the connection is
    read-only and a write is `.readOnly`. -/
private def testNotWriter : IO Unit := do
  fresh dbPath
  let svc ← Runtime.Service.new svcBase (Instance.ofPath dbPath) .serve true
    { readers := 0 }
  let seeded ← svc.withConnection fun conn =>
    DbM.run conn (insert Item ⟨"seed"⟩)
  match seeded with
  | .ok (.ok _) => pure ()
  | r => throw <| IO.userError s!"FAIL: seed write: {repr r}"
  let ro ← svc.withReader fun conn => do
    check conn.readOnly "withReader connection is read-only"
    DbM.run conn (insert Item ⟨"nope"⟩)
  match ro with
  | .ok (.error e) => check (e.code == "read_only") s!"write on reader: {e}"
  | .ok (.ok _) => throw <| IO.userError "FAIL: withReader handed out a writable connection"
  | .error e => throw <| IO.userError s!"FAIL: withReader: {e}"
  svc.close

/-- Two concurrent `withReader` calls on a one-slot pool both complete:
    they serialize on the per-connection lock instead of sharing the
    SQLite handle. -/
private def testLock : IO Unit := do
  fresh dbPath
  let svc ← Runtime.Service.new svcBase (Instance.ofPath dbPath) .serve true
    { readers := 1 }
  let seeded ← svc.withConnection fun conn =>
    DbM.run conn (insert Item ⟨"x"⟩)
  match seeded with
  | .ok (.ok _) => pure ()
  | r => throw <| IO.userError s!"FAIL: seed: {repr r}"
  let work : IO (Except Runtime.RuntimeError Nat) :=
    svc.withReader fun conn => do
      let a ← expectOk (← DbM.run conn (fetchAll Item)) "read 1"
      IO.sleep 50
      let b ← expectOk (← DbM.run conn (fetchAll Item)) "read 2"
      check (a.size == b.size) "snapshot reads agree"
      return a.size
  let t1 ← IO.asTask (prio := .default) work
  let t2 ← IO.asTask (prio := .default) work
  let r1 ← IO.ofExcept t1.get
  let r2 ← IO.ofExcept t2.get
  match r1, r2 with
  | .ok 1, .ok 1 => pure ()
  | _, _ => throw <| IO.userError s!"FAIL: concurrent withReader: {repr r1} {repr r2}"
  svc.close

def run : IO Unit := do
  testNotWriter
  testLock

end TestsLdb19
