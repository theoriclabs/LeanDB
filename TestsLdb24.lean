import LeanDb

/-! LDB-24: the deferred read snapshot is a public API (`readSnapshot`).
    A multi-statement read sees one WAL snapshot; a writer on another
    connection is not visible until the snapshot ends. -/

namespace TestsLdb24

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def check' (condition : Bool) (message : String) : DbM Unit :=
  unless condition do throw (.sqlite s!"FAIL: {message}")

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

private def io (act : IO α) : DbM α :=
  fun _ => ExceptT.mk (Except.ok <$> act)

structure Note where
  text : String
  deriving Repr, LeanDb.Entity

private def specs : List TableSpec := Entity.specs Note

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb24.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def testSnapshotHidesWriter : IO Unit := do
  fresh dbPath
  let c1 ← expectOk (← openDb dbPath specs) "conn1"
  let c2 ← expectOk (← openDb dbPath specs) "conn2"
  discard <| expectOk (← DbM.run c1 (insert Note ⟨"first"⟩)) "insert"
  let r ← DbM.run c1 <| readSnapshot do
    let n0 := (← fetchAll Note).size
    check' (n0 == 1) s!"started with one row, got {n0}"
    discard <| io (DbM.run c2 (insert Note ⟨"second"⟩))
    let n1 := (← fetchAll Note).size
    check' (n1 == 1) s!"snapshot still has one row, got {n1}"
  discard <| expectOk r "readSnapshot"
  let after ← expectOk (← DbM.run c1 (fetchAll Note)) "after"
  check (after.size == 2) s!"after the snapshot the second row is visible, got {after.size}"

def run : IO Unit := testSnapshotHidesWriter

end TestsLdb24
