import LeanDb

/-! LDB-22: `count` / `exists?` honour the lambda, not only the plan.
    A hand-written `.tt` plan used to `COUNT(*)` every row while the
    lambda still filtered. -/

namespace TestsLdb22

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

structure Person where
  name : String
  age : Nat
  deriving Repr, LeanDb.Entity

private def specs : List TableSpec := Entity.specs Person

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb22.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def even (p : Stored Person) : Bool := p.val.age % 2 == 0

/-- Plan is `.tt` (exact, every row); the lambda keeps only even ages. -/
private def testHonourLambda : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    discard <| insert Person ⟨"a", 1⟩
    discard <| insert Person ⟨"b", 2⟩
    discard <| insert Person ⟨"c", 3⟩
    let n ← count (ts := [Person]) even (plan := .tt)
    unless n == 1 do
      throw (.sqlite s!"FAIL: count even with .tt plan = {n}, want 1")
    let yes ← exists? (ts := [Person]) even (plan := .tt)
    unless yes do throw (.sqlite "FAIL: exists? even with .tt plan")
    let no ← exists? (ts := [Person]) (fun p => p.val.age % 2 == 3) (plan := .tt)
    unless !no do throw (.sqlite "FAIL: exists? impossible residual")
  discard <| expectOk r "count/exists? honour lambda"

def run : IO Unit := testHonourLambda

end TestsLdb22
