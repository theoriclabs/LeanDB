import LeanDb

/-! LDB-17: apply `order`/`window` after the residual Lean-side filter
    unless the plan is exact.

    A pushed `LIMIT 1` on the `approx` superset can miss a later row that
    only the residual accepts: `existsP` then answers false, and a page
    can be short or empty. -/

namespace TestsLdb17

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

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb17.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

/-- Residual: even ages. The first row in id order is odd, so a SQL
    `LIMIT 1` over `approx` (every row) never sees an even age. -/
private def even (p : Stored Person) : Bool := p.val.age % 2 == 0

private def evenPlan : Pred [Person] := pred% [Person] even

/-- `existsP` with a residual must not answer false when a matching row
    exists after the first `approx` row. -/
private def testExistsP : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    discard <| insert Person ⟨"odd", 1⟩
    discard <| insert Person ⟨"even", 2⟩
    check evenPlan.hasOpaque "even ages are residual"
    let yes ← existsP evenPlan
    unless yes do throw (.sqlite "FAIL: existsP missed the even row behind LIMIT 1")
    let no ← existsP (pred% [Person] fun p => p.val.age % 2 == 3)
    unless !no do throw (.sqlite "FAIL: existsP should be false when nothing matches")
  discard <| expectOk r "existsP"

/-- Pagination over a residual: `LIMIT 1` is the first *matching* row,
    not the first fetched row. Offset 1 is the second match. -/
private def testPagination : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    discard <| insert Person ⟨"a", 1⟩
    discard <| insert Person ⟨"b", 2⟩
    discard <| insert Person ⟨"c", 3⟩
    discard <| insert Person ⟨"d", 4⟩
    let page0 ← selectP [Person] evenPlan (window := { limit := some 1 })
    unless page0.map (·.val.name) == #["b"] do
      throw (.sqlite s!"FAIL: first even page, got {page0.map (·.val.name)}")
    let page1 ← selectP [Person] evenPlan (window := { limit := some 1, offset := 1 })
    unless page1.map (·.val.name) == #["d"] do
      throw (.sqlite s!"FAIL: second even page, got {page1.map (·.val.name)}")
    let all ← selectP [Person] evenPlan (window := { limit := some 10 })
    unless all.map (·.val.name) == #["b", "d"] do
      throw (.sqlite s!"FAIL: all even rows, got {all.map (·.val.name)}")
  discard <| expectOk r "pagination"

/-- An exact plan still pushes the window: `age ≥ 2` with `LIMIT 1` is
    the first matching row in id order. -/
private def testExactStillPushes : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    discard <| insert Person ⟨"a", 1⟩
    discard <| insert Person ⟨"b", 2⟩
    discard <| insert Person ⟨"c", 3⟩
    let p : Pred [Person] := pred% [Person] fun x => x.val.age ≥ 2
    unless !p.hasOpaque do throw (.sqlite "FAIL: age ≥ 2 should be exact")
    let page ← selectP [Person] p (window := { limit := some 1 })
    unless page.map (·.val.name) == #["b"] do
      throw (.sqlite s!"FAIL: exact LIMIT 1, got {page.map (·.val.name)}")
  discard <| expectOk r "exact window"

def run : IO Unit := do
  testExistsP
  testPagination
  testExactStillPushes

end TestsLdb17
