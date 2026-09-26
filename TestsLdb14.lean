import LeanDb

/-! LDB-14 review regressions. A pushed `prefix` must be exact, not just a
    widening the lambda re-checks: `selectP`, `Query.exec` and the typed
    `first`/`page`/`count`/`exists` push LIMIT/OFFSET/COUNT/EXISTS for
    every plan without an opaque leaf, so a `LIKE` that also matched
    `Hagrid` for `"ha"` took a window slot the re-check then emptied. -/

namespace TestsLdb14

open LeanDb

private def check' (condition : Bool) (message : String) : DbM Unit :=
  unless condition do throw (.sqlite s!"FAIL: {message}")

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

structure Wizard where
  name : String
  deriving Repr, BEq, LeanDb.Entity

schema% School := Wizard

private def specs : List TableSpec := IsSchema.specs School

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb14.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

/-- Reified to a `Pred.prefix` leaf, so the query is exact and `first` /
    `page` push their window. -/
private def byPrefix : Query School [Wizard] (Stored Wizard) :=
  (Query.from Wizard).where' (fun w => w.val.name.startsWith "ha")

private theorem byPrefix_exact : byPrefix.exact = true := by exact_plan

/-- Only `Hagrid` matches it case-folded; nothing matches it exactly. -/
private def byHag : Query School [Wizard] (Stored Wizard) :=
  (Query.from Wizard).where' (fun w => w.val.name.startsWith "hag")

/-- `run r` equals `denote r (← load)`, and is `want`. -/
private def runIs {α} [BEq α] [Repr α] (r : Read School α) (want : α) (msg : String) :
    DbM Unit := do
  let st ← DbState.load (s := School)
  match ← Read.run (s := School) r with
  | .error e => throw (.sqlite s!"FAIL: {msg}: fault {e}")
  | .ok got =>
      check' (got == Read.denote (s := School) r st) s!"{msg}: run ≠ denote (load)"
      check' (got == want) s!"{msg}: got {repr got}"

private def names (xs : List (Valid Wizard)) : List String := xs.map (·.val.name)

/-- `Hagrid` comes first in id order: a case-folding `LIMIT 1` would fetch
    it alone and `first` would answer `none`. -/
private def testTypedWindow : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    for n in ["Hagrid", "ha1", "habitat", "Harry"] do
      discard <| insert Wizard ⟨n⟩
    runIs ((·.map (·.val.name)) <$> Read.first byPrefix) (some "ha1") "first"
    runIs ((fun p => (names p.items, p.total)) <$> Read.page byPrefix { limit := some 2 })
      (["ha1", "habitat"], 2) "page limit 2"
    runIs ((fun p => (names p.items, p.total)) <$>
        Read.page byPrefix { offset := 1, limit := some 1 })
      (["habitat"], 2) "page offset 1"
    runIs (Read.count byPrefix) 2 "count"
    runIs (Read.«exists» byPrefix) true "exists"
    runIs (Read.count byHag) 0 "count of a case-folded-only prefix"
    runIs (Read.«exists» byHag) false "exists of a case-folded-only prefix"
    runIs (names <$> Read.all (byPrefix.withWindow { limit := some 1 } byPrefix_exact))
      ["ha1"] "withWindow"
  discard <| expectOk r "typed prefix window"

def run : IO Unit := do
  testTypedWindow

end TestsLdb14
