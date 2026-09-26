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

unique% Wizard.byName := name

schema% School := Wizard

/-- An index with both a name and a collation, declared by hand. -/
structure Muggle where
  name : String
  deriving Repr, LeanDb.Entity

instance : Indexes Muggle where
  indexes := #[{ columns := #["name"], name := some "ix_muggle_by_name",
                 collate := some .nocase }]

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

/-- `schema_json` keeps every index's name next to its collation: an
    index stored without its name differs from the declared one, so every
    open would plan to drop and re-add it. -/
private def testIndexNamesInSchemaJson : IO Unit := do
  let specs := IsSchema.specs School ++ Entity.specs Muggle
  for t in specs do
    for ix in t.indexes do
      match IndexSpec.fromJson? ix.toJson with
      | .ok back =>
          unless back == ix do
            throw <| IO.userError s!"FAIL: index JSON round trip: {repr back} ≠ {repr ix}"
      | .error e => throw <| IO.userError s!"FAIL: index JSON parse: {e}"
  unless specs.any (·.indexes.any (·.name == some "uq_wizard_byName")) do
    throw <| IO.userError "FAIL: the derived unique index is not named"
  fresh dbPath
  discard <| expectOk (← withDb dbPath specs (pure ())) "open"
  let conn ← expectOk (← openDb dbPath specs) "reopen"
  let raw := (← readMeta conn.raw "schema_json").getD ""
  for n in ["uq_wizard_byName", "ix_muggle_by_name"] do
    unless raw.contains n do
      throw <| IO.userError s!"FAIL: schema_json lost the index name {n}: {raw}"
  let some stored ← readStoredSchema conn |
    throw <| IO.userError "FAIL: no stored schema"
  unless stored == specs do
    throw <| IO.userError s!"FAIL: stored schema ≠ declared: {repr stored}"
  match planMigration stored specs with
  | .ok plan =>
      unless plan.steps.isEmpty do
        throw <| IO.userError s!"FAIL: reopening plans {plan.steps.map (·.describe)}"
  | .error e => throw <| IO.userError s!"FAIL: plan: {e}"

/-- `Render.indexLit` of Muggle's index, pasted as `migrate freeze` writes
    it: the literal must elaborate back to the declared index. -/
private def muggleIndexFrozen : IndexSpec :=
  { unique := false, columns := #["name"], name := some ("ix_muggle_by_name"), collate := some (LeanDb.Collate.nocase) }

private def testFrozenCollation : IO Unit := do
  let some ix := (Entity.spec Muggle).indexes[0]? |
    throw <| IO.userError "FAIL: Muggle has no index"
  let lit := Render.indexLit ix
  unless lit == "{ unique := false, columns := #[\"name\"], name := some (\"ix_muggle_by_name\"), \
collate := some (LeanDb.Collate.nocase) }" do
    throw <| IO.userError s!"FAIL: frozen index literal: {lit}"
  unless muggleIndexFrozen == ix do
    throw <| IO.userError "FAIL: the frozen literal does not rebuild the index"
  unless (Render.specsLit (Entity.specs Muggle)).contains "collate := some (LeanDb.Collate.nocase)" do
    throw <| IO.userError "FAIL: the frozen snapshot dropped the collation"

def run : IO Unit := do
  testTypedWindow
  testIndexNamesInSchemaJson
  testFrozenCollation

end TestsLdb14
