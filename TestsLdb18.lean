import LeanDb

/-! LDB-18: `SqlOrd Nat` is lawful. `Nat` columns are bounded to what a
    SQLite INTEGER holds (`0 … Int64.maxValue`). A comparison bound
    outside that range no longer wraps, so `select (·.n < 2^64)` agrees
    with its Lean meaning. -/

namespace TestsLdb18

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

private def expectDecode (r : Except DbError α) (context : String) : IO Unit :=
  match r with
  | .ok _ => throw <| IO.userError s!"FAIL: {context}: expected decode refusal, got success"
  | .error e => check (e.code == "decode") s!"{context}: expected decode, got {e}"

structure Num where
  n : Nat
  deriving Repr, LeanDb.Entity

private def specs : List TableSpec := Entity.specs Num

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb18.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

/-- Wrapping `2^64` to 0 would push `n < 0` and return no rows. -/
private def ltPlan : PlanFor (ts := [Num]) (fun (r : Stored Num) => r.val.n < 2 ^ 64) :=
  by leandb_plan

private def testBoundRendersAsTrue : IO Unit := do
  check (ltPlan.plan.renderT == ("1", #[]))
    s!"n < 2^64 must render as true, got {repr ltPlan.plan.renderT}"
  check (!ltPlan.plan.hasOpaque) "n < 2^64 stays an ordered leaf (SqlOrd Nat)"

private def testSelectAgrees : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    discard <| insert Num ⟨1⟩
    discard <| insert Num ⟨natSqlMax⟩
    let rows ← select [Num] (fun r => r.val.n < 2 ^ 64)
    unless rows.size == 2 do
      throw (.sqlite s!"FAIL: select (·.n < 2^64) returned {rows.size} rows, want 2")
    let viaP ← selectP [Num] ltPlan.plan
    unless viaP.size == 2 do
      throw (.sqlite s!"FAIL: selectP (n < 2^64) returned {viaP.size} rows, want 2")
  discard <| expectOk r "select n < 2^64"

private def testWriteRefused : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    let act : DbM Unit := discard <| insert Num ⟨2 ^ 64⟩
    match ← (fun conn => ExceptT.mk (.ok <$> (act conn).run)) with
    | .error e =>
        unless e.code == "decode" do
          throw (.sqlite s!"FAIL: insert 2^64 expected decode, got {e}")
    | .ok () => throw (.sqlite "FAIL: insert 2^64 must be refused")
    discard <| insert Num ⟨natSqlMax⟩
    let all ← fetchAll Num
    unless all.map (·.val.n) == #[natSqlMax] do
      throw (.sqlite s!"FAIL: max Nat must store, got {all.map (·.val.n)}")
  discard <| expectOk r "write bound"
  expectDecode (← (do
    fresh dbPath
    withDb dbPath specs (discard <| insertMany Num #[⟨2 ^ 63⟩])))
    "insertMany 2^63"

def run : IO Unit := do
  testBoundRendersAsTrue
  testSelectAgrees
  testWriteRefused

end TestsLdb18
