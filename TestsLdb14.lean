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

/-- `patch`'s guard and `scan`'s pages are SQL with no Lean re-check at
    all, so a case-folding prefix would write, or hand back, `Hagrid`. -/
private def testGuardAndScan : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    let hagrid ← insert Wizard ⟨"Hagrid"⟩
    for n in ["ha1", "habitat", "Harry"] do
      discard <| insert Wizard ⟨n⟩
    let ha : Pred [Wizard] := .prefix (.here Wizard.Field.name) "ha"
    let res ← patch hagrid.id ⟨#[Assignment.of Wizard.Field.name "Rubeus"]⟩ (guard := ha)
    check' (res == .guardFailed) s!"patch guarded by a prefix: {repr res}"
    let some now ← get hagrid.id | throw (.sqlite "FAIL: Hagrid vanished")
    check' (now.val.name == "Hagrid") s!"the guard wrote {now.val.name}"
    let seen ← IO.mkRef (#[] : Array String)
    scan ha (chunk := 1) fun rows => do
      discard <| (seen.modify (· ++ rows.map (·.val.name)) : IO Unit)
      return true
    let seen ← seen.get
    check' (seen == #["ha1", "habitat"]) s!"scan with a prefix: {seen}"
  discard <| expectOk r "prefix guard and scan"

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

/-! The tactic's string plans are the lambda, row for row: the typed
    layer's meaning *is* the plan, so a leaf that means something else
    changes the answer, not just the fetch. -/

private def plans : List (String × (Stored Wizard → Bool) × Pred [Wizard]) :=
  [("startsWith", fun w => w.val.name.startsWith "ha",
      (by leandb_plan : PlanFor (ts := [Wizard]) fun w => w.val.name.startsWith "ha")),
   ("contains", fun w => w.val.name.contains "ar",
      (by leandb_plan : PlanFor (ts := [Wizard]) fun w => w.val.name.contains "ar")),
   ("toLower.contains", fun w => w.val.name.toLower.contains "AR".toLower,
      (by leandb_plan : PlanFor (ts := [Wizard]) fun w =>
        w.val.name.toLower.contains "AR".toLower)),
   ("toLower.startsWith", fun w => w.val.name.toLower.startsWith "HA".toLower,
      (by leandb_plan : PlanFor (ts := [Wizard]) fun w =>
        w.val.name.toLower.startsWith "HA".toLower)),
   ("!startsWith", fun w => !w.val.name.startsWith "ha",
      (by leandb_plan : PlanFor (ts := [Wizard]) fun w => !w.val.name.startsWith "ha"))]

/-- Case-insensitive prefix, which has no leaf: it must stay residual. -/
private def byLowerPrefix : Query School [Wizard] (Stored Wizard) :=
  (Query.from Wizard).where' (fun w => w.val.name.toLower.startsWith "HA".toLower)

private def testPlansAreTheLambda : IO Unit := do
  let rows : List (Stored Wizard) :=
    ["Hagrid", "ha1", "habitat", "Harry", "", "xHa", "HA"].zipIdx.map fun (n, i) =>
      ⟨⟨Int64.ofNat (i + 1)⟩, ⟨n⟩⟩
  for (label, lam, plan) in plans do
    for r in rows do
      unless plan.denote .empty r == lam r do
        throw <| IO.userError s!"FAIL: plan {label} ≠ lambda on {repr r.val.name}"
  let some (_, _, lowered) := plans.find? (·.1 == "toLower.startsWith") |
    throw <| IO.userError "FAIL: no toLower.startsWith plan"
  unless lowered.residuals == 1 do
    throw <| IO.userError s!"FAIL: a lowered startsWith was pushed: {lowered.renderT.1}"
  fresh dbPath
  let r ← withDb dbPath specs do
    for n in ["Hagrid", "ha1", "xHa", "Harry"] do
      discard <| insert Wizard ⟨n⟩
    runIs (names <$> Read.all byLowerPrefix) ["Hagrid", "ha1", "Harry"] "lowered startsWith"
  discard <| expectOk r "lowered startsWith"

/-- The index DDL SQLite holds for `name`, if the index exists. -/
private def indexSql (path : System.FilePath) (name : String) : IO (Option String) := do
  let db ← SQLite.open path
  let stmt ← db.prepare "SELECT sql FROM sqlite_master WHERE type = 'index' AND name = ?"
  stmt.bindText 1 name
  if ← stmt.step then return some (← stmt.columnText 0) else return none

/-- Declaring `collate` on an existing index keeps its name, so the
    migration must drop the old index before creating the new one: the
    other way round, `CREATE INDEX IF NOT EXISTS` is a no-op and the drop
    then removes the index the schema says exists. -/
private def testCollationChangeRebuildsIndex : IO Unit := do
  let binary : TableSpec :=
    { Entity.spec Muggle with indexes := #[{ columns := #["name"], name := some "ix_muggle_by_name" }] }
  fresh dbPath
  discard <| expectOk (← withDb dbPath [binary] (insert Muggle ⟨"Dursley"⟩)) "open with BINARY"
  let some before ← indexSql dbPath "ix_muggle_by_name" |
    throw <| IO.userError "FAIL: the BINARY index was not created"
  if before.contains "NOCASE" then
    throw <| IO.userError s!"FAIL: the BINARY index is NOCASE: {before}"
  let (plan, _) ← expectOk (← migrate dbPath (Entity.specs Muggle) (apply := true)) "migrate"
  unless (plan.map (·.steps.length)) == some 2 do
    throw <| IO.userError s!"FAIL: expected a drop and an add, got {plan.map (·.steps.map (·.describe))}"
  match ← indexSql dbPath "ix_muggle_by_name" with
  | some after =>
      unless after.contains "COLLATE NOCASE" do
        throw <| IO.userError s!"FAIL: the migrated index is not NOCASE: {after}"
  | none => throw <| IO.userError "FAIL: the migration dropped the index it declares"
  let rows ← expectOk (← withDb dbPath (Entity.specs Muggle) (fetchAll Muggle)) "reopen"
  unless rows.map (·.val.name) == #["Dursley"] do
    throw <| IO.userError "FAIL: the migration lost a row"

def run : IO Unit := do
  testTypedWindow
  testGuardAndScan
  testIndexNamesInSchemaJson
  testFrozenCollation
  testPlansAreTheLambda
  testCollationChangeRebuildsIndex

end TestsLdb14
