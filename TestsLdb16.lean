import LeanDb

/-! LDB-16: an entity's declared invariant, checked on every read and write.

A row that fails it is refused with `.invariant` — on `get`, `fetchAll`,
`insert`, `update`, `patch`, and `append` — and never handed out. The
invariant reads the whole value, child lists included. Its name is part of
the schema: in the fingerprint, in `schema_json`, and a migration step. -/

namespace TestsLdb16

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

private def expectInvariant (r : Except DbError α) (context : String) : IO Unit :=
  match r with
  | .ok _ => throw <| IO.userError s!"FAIL: {context}: expected an invariant refusal, got success"
  | .error (.invariant table name) =>
      check (table == "account" && name == "TestsLdb16.Account.invariant")
        s!"{context}: names the table and the invariant, got {table} {name}"
  | .error e => throw <| IO.userError s!"FAIL: {context}: expected invariant, got {e}"

structure Posting where
  amount : Int64
  deriving Repr, BEq, LeanDb.Inline

/-- The balance is the sum of the postings, and never negative. -/
structure Account where
  name : String
  balance : Int64
  postings : List Posting
  deriving Repr

@[leandb_invariant]
def Account.invariant (a : Account) : Bool :=
  a.balance ≥ 0 && a.balance == (a.postings.map (·.amount)).foldl (· + ·) 0

deriving instance LeanDb.Entity for Account

/-- An entity without a declared invariant. -/
structure Plain where
  name : String
  deriving Repr, LeanDb.Entity

/--
error: @[leandb_invariant]: LeanDb.Entity TestsLdb16.Plain already exists and would not check TestsLdb16.Plain.invariant. Declare the invariant first, then `deriving instance LeanDb.Entity for TestsLdb16.Plain`.
-/
#guard_msgs in
@[leandb_invariant] def Plain.invariant (_ : Plain) : Bool := true

/--
error: @[leandb_invariant]: name the check `<Type>.invariant`, got TestsLdb16.Account.check
-/
#guard_msgs in
@[leandb_invariant] def Account.check (_ : Account) : Bool := true

private def specs : List TableSpec := Entity.specs Account ++ Entity.specs Plain

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb16.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def good : Account := ⟨"alice", 30, [⟨50⟩, ⟨-20⟩]⟩

private def testWrites : IO Unit := do
  fresh dbPath
  let conn ← expectOk (← openDb dbPath specs) "open"
  expectInvariant (← DbM.run conn (insert Account ⟨"bob", -5, [⟨-5⟩]⟩)) "insert negative"
  expectInvariant (← DbM.run conn (insert Account ⟨"bob", 10, [⟨5⟩]⟩)) "insert inconsistent"
  expectInvariant (← DbM.run conn (insertMany Account #[good, ⟨"bob", -1, [⟨-1⟩]⟩])) "insertMany"
  let all ← expectOk (← DbM.run conn (fetchAll Account)) "fetchAll"
  check all.isEmpty "refused writes stored nothing"
  let s ← expectOk (← DbM.run conn (insert Account good)) "insert good"
  expectInvariant (← DbM.run conn (update s { s.val with balance := 31 })) "update to inconsistent"
  expectInvariant (← DbM.run conn (append s { s.val with postings := s.val.postings ++ [⟨-40⟩] }))
    "append that breaks it"
  let ok ← expectOk (← DbM.run conn
    (append s { s.val with balance := 20, postings := s.val.postings ++ [⟨-10⟩] }))
    "append that keeps it"
  check (ok.val.balance == 20) "append kept the invariant"
  -- patch sets a column; the patched row is checked before commit
  let r ← DbM.run conn (patch s.id ⟨#[Assignment.of Account.Field.balance (-1 : Int64)]⟩)
  expectInvariant r "patch to negative"
  let back ← expectOk (← DbM.run conn (get s.id)) "read back"
  check ((back.map (·.val.balance)) == some 20) "refused patch rolled back"
  -- an entity without an invariant is unaffected
  discard <| expectOk (← DbM.run conn (insert Plain ⟨"x"⟩)) "plain insert"

/-- A row corrupted behind LeanDB's back is refused on every read. -/
private def testReads : IO Unit := do
  fresh dbPath
  let conn ← expectOk (← openDb dbPath specs) "open"
  let s ← expectOk (← DbM.run conn (insert Account good)) "insert"
  conn.raw.exec "UPDATE \"account\" SET \"balance\" = -7"
  expectInvariant (← DbM.run conn (get s.id)) "get after corruption"
  expectInvariant (← DbM.run conn (fetchAll Account)) "fetchAll after corruption"
  conn.raw.exec "UPDATE \"account\" SET \"balance\" = 30"
  -- the invariant reads the child list too
  conn.raw.exec "UPDATE \"account_postings\" SET \"amount\" = 1 WHERE \"position\" = 0"
  expectInvariant (← DbM.run conn (get s.id)) "get after child corruption"

/-- The invariant is part of the schema: spec, JSON, fingerprint, migration. -/
private def testSchema : IO Unit := do
  let spec := Entity.spec Account
  check (spec.invariant == some "TestsLdb16.Account.invariant") s!"spec names it: {spec.invariant}"
  check ((Entity.spec Plain).invariant == none) "no invariant, none"
  let bare := { spec with invariant := none }
  check (fingerprint [spec] != fingerprint [bare]) "declaring an invariant changes the fingerprint"
  check (fingerprint [Entity.spec Plain] == fingerprint [{ Entity.spec Plain with invariant := none }])
    "no invariant, fingerprint as before"
  let roundTrips (t : TableSpec) : Bool :=
    match TableSpec.fromJson? t.toJson with
    | .ok back => back == t
    | .error _ => false
  check (roundTrips spec) "JSON round trip keeps it"
  check (roundTrips bare) "JSON without it"
  check ((bare.toJson.getObjVal? "invariant").toOption.isNone) "absent key when none"
  let withIt := Entity.specs Account
  let without := withIt.map fun t => { t with invariant := none }
  match planMigration without withIt with
  | .error m => throw <| IO.userError s!"FAIL: plan: {m}"
  | .ok plan =>
      check (plan.steps.length == 1) s!"one step: {plan.steps.map (·.describe)}"
      check (plan.steps.all fun | .restampInvariant .. => true | _ => false) "restamp step"
      check (plan.steps.all (·.sql.isEmpty)) "no SQL"
  -- apply it to a file shaped without the invariant
  fresh dbPath
  let conn ← expectOk (← openDb dbPath without) "open bare"
  discard <| expectOk (← DbM.run conn (insert Account good)) "insert under bare schema"
  let r ← migrateOn conn withIt { apply := true, backup := none }
  match r with
  | .error e => throw <| IO.userError s!"FAIL: migrate: {e}"
  | .ok (_, some report) =>
      check (report.applied.length == 1) s!"journaled: {report.applied}"
      check (report.fingerprint == fingerprint withIt) "new fingerprint recorded"
  | .ok _ => throw <| IO.userError "FAIL: migrate reported nothing"
  discard <| expectOk (← openDb dbPath withIt) "reopens under the new fingerprint"
  -- and a frozen snapshot keeps it: the rendered literal names the invariant
  check ((Render.specsLit withIt).contains "invariant := some \"TestsLdb16.Account.invariant\"")
    "freeze writes the invariant"

def run : IO Unit := do
  testWrites
  testReads
  testSchema

end TestsLdb16
