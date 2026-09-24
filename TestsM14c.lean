import LeanDb

/-! M14 part C: close gaps against QUERIES.md §3 / §5. -/

namespace TestsM14c

open LeanDb
open LeanDb.Harness

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

structure Team where
  name : String
  deriving Repr, BEq, LeanDb.Entity

structure Tag where
  label : String
  deriving Repr, BEq, LeanDb.Inline

structure User where
  name : String
  email : String
  team : Ref Team
  tags : List Tag
  deriving Repr, BEq

@[leandb_invariant]
def User.invariant (u : User) : Bool := u.name != ""

deriving instance LeanDb.Entity for User

unique% User.byName := name
unique% User.byEmail := email

schema% App := Team, User

private def specs : List TableSpec := IsSchema.specs App

private def dbPath : System.FilePath := ".lake" / "leandb_test_m14c.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

private def mustCheck (u : User) : Except String (Checked User) :=
  match Entity.check User u with
  | .ok c => .ok c
  | .error _ => .error s!"check {u.name}"

private def stateEqApp (a b : DbState App) : Bool :=
  tableEq (DbState.get (α := Team) a) (DbState.get (α := Team) b) &&
    tableEq (DbState.get (α := User) a) (DbState.get (α := User) b)

private def eqEmpty {α} (eq : α → α → Bool) :
    Except Empty α → Except Empty α → Bool
  | .ok a, .ok b => eq a b
  | .error e, _ => nomatch e
  | _, .error e => nomatch e

private def uniqueUserEq (a b : Unique User) : Bool :=
  match a, b with
  | .byName, .byName => true
  | .byEmail, .byEmail => true
  | _, _ => false

private def fkUserEq (a b : ForeignKey User) : Bool :=
  match a, b with
  | .team, .team => true

private def eqSet (fs : Fields User) :
    Except Empty (Except (SetError User fs) (Stored User)) →
    Except Empty (Except (SetError User fs) (Stored User)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error .gone, .error .gone => true
    | .error (.duplicate x h1), .error (.duplicate y h2) => uniqueUserEq x.ix y.ix && h1 == h2
    | .error (.missingRef x), .error (.missingRef y) => fkUserEq x.fk y.fk
    | _, _ => false

private def eqTxn {ε α} (p : {σ : Type} → Txn σ App ε α)
    (eq : Except ε α → Except ε α → Bool) (msg : String) : DbM Unit := do
  let st0 ← DbState.load (s := App)
  match ← Txn.run (s := App) p with
  | .error e => throw (.sqlite s!"FAIL: {msg}: fault {e}")
  | .ok got =>
      let (want, stD) := Txn.denote (σ := Unit) (s := App) (p (σ := Unit)) st0
      unless eq got want do
        throw (.sqlite s!"FAIL: {msg}: run ≠ denote")
      let st1 ← DbState.load (s := App)
      unless stateEqApp st1 stD do
        throw (.sqlite s!"FAIL: {msg}: final state ≠ denote")

/-- `SetError` on a non-ref field: `missingRef` is omitted — `Within` is
    `Empty`, and `IsEmpty` is found. -/
example (e : SetError User (Fields.singleton User.Field.email)) : Nat :=
  match e with
  | .gone => 0
  | .duplicate _ _ => 1

example [IsEmpty (ForeignKey.Within (α := User) (Fields.singleton User.Field.email))] :
    True := trivial

/-- Writing only `team` (a `Ref`, not a unique column): `duplicate` is omitted. -/
example (e : SetError User (Fields.singleton User.Field.team)) : Nat :=
  match e with
  | .gone => 0
  | .missingRef _ => 1

example [IsEmpty (Unique.Touching (α := User) (Fields.singleton User.Field.team))] :
    True := trivial

/-- A residual Lean filter: unwindowed `all` is allowed; `first`/`count`/`exists`
    and `withWindow` are refused. -/
def residualQ : Query App [User] (Stored User) :=
  { Query.from (s := App) User with pred := .opaque fun r => r.val.name == "ada" }

example : Read App (List (Stored User)) := Read.all residualQ

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: this query is not exact: `first`, `count`, `exists`, `page`, and a window need a plan with no opaque leaf (unwindowed `all` may keep a Lean residual)
-/
#guard_msgs in
example : Read App (Option (Stored User)) := Read.first residualQ

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: this query is not exact: `first`, `count`, `exists`, `page`, and a window need a plan with no opaque leaf (unwindowed `all` may keep a Lean residual)
-/
#guard_msgs in
example : Read App Nat := Read.count residualQ

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: this query is not exact: `first`, `count`, `exists`, `page`, and a window need a plan with no opaque leaf (unwindowed `all` may keep a Lean residual)
-/
#guard_msgs in
example : Read App Bool := Read.«exists» residualQ

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: this query is not exact: `first`, `count`, `exists`, `page`, and a window need a plan with no opaque leaf (unwindowed `all` may keep a Lean residual)
-/
#guard_msgs in
example : Query App [User] (Stored User) := residualQ.withWindow { limit := some 1 }

private def usersExact : Query App [User] (Stored User) := Query.from User
private def usersJoin : Query App [User, Team] (Stored User × Stored Team) :=
  (Query.from User).join User.ForeignKey.team

example : residualQ.exact = false := rfl
example : usersExact.exact = true := rfl
example : usersJoin.exact = true := by native_decide
example : Read App (Option (Stored User)) := Read.first usersExact
example : Read App Nat := Read.count usersJoin
example : Query App [User, Team] (Stored User × Stored Team) :=
  usersJoin.withWindow { limit := some 1 }

def patchEmailOnly {σ} (id : _root_.LeanDb.Id User) (new : Checked User) :
    Txn σ App Empty (Except (SetError User (Fields.singleton User.Field.email)) (Stored User)) := do
  match ← Txn.get User id with
  | none =>
      return .error (SetError.gone (α := User) (fs := Fields.singleton User.Field.email))
  | some row =>
      match ← Txn.patch (α := User) row (Fields.singleton User.Field.email) new with
      | .error e => return .error e
      | .ok row => return .ok row.toStored

/-- Meaning: a non-written field in `new` does not replace the stored one. -/
private def testPatchMergeDenote : IO Unit := do
  let st0 := DbState.empty (s := App)
  let (rTeam, st1) :=
    Txn.denote (σ := Unit) (s := App) (ε := Empty)
      (Txn.insertNew (Checked.of (⟨"eng"⟩ : Team) (by unfold Invariant; trivial))) st0
  let team ← match rTeam with
    | .error e => nomatch e
    | .ok row => pure row
  let ada : User := ⟨"ada", "ada@x", team.id, [⟨"lead"⟩]⟩
  let cAda ← match mustCheck ada with
    | .ok c => pure c
    | .error e => throw <| IO.userError s!"FAIL: {e}"
  let (rIns, st2) := Txn.denote (σ := Unit) (s := App) (ε := Empty)
    (Txn.insert (α := User) cAda) st1
  let adaId ← match rIns with
    | .error e => nomatch e
    | .ok (.error _) => throw <| IO.userError "FAIL: insert ada"
    | .ok (.ok row) => pure row.id
  let bogus ← match mustCheck ⟨"zzz", "new@x", team.id, [⟨"gone"⟩]⟩ with
    | .ok c => pure c
    | .error e => throw <| IO.userError s!"FAIL: {e}"
  let (rPatch, st3) :=
    Txn.denote (σ := Unit) (s := App) (ε := Empty) (patchEmailOnly adaId bogus) st2
  match rPatch with
  | .error e => nomatch e
  | .ok (.error _) => throw <| IO.userError "FAIL: patch denote"
  | .ok (.ok row) =>
      check (row.val.name == "ada") "patch keeps stored name"
      check (row.val.email == "new@x") "patch writes email"
      check (row.val.tags == [⟨"lead"⟩]) "patch keeps stored tags"
      check (row.val.team == team.id) "patch keeps stored team"
  match (DbState.get (α := User) st3).rows.find? (·.id == adaId) with
  | none => throw <| IO.userError "FAIL: ada missing after patch"
  | some stored =>
      check (stored.val.name == "ada") "state name survived"
      check (stored.val.email == "new@x") "state email written"
      check (stored.val.tags == [⟨"lead"⟩]) "state tags survived"

private def seedAda : DbM (Stored Team × Stored User) := do
  let eng ← LeanDb.insert Team ⟨"eng"⟩
  let ada ← LeanDb.insert User ⟨"ada", "ada@x", eng.id, [⟨"lead"⟩]⟩
  return (eng, ada)

/-- Run equals denote, and a non-written field in `new` survives in SQLite. -/
private def testPatchSurvivesHarness : IO Unit := do
  fresh dbPath
  let n ← expectOk (← withDb dbPath specs do
    let (eng, ada) ← seedAda
    let bogus ← match mustCheck ⟨"zzz", "new@x", eng.id, [⟨"gone"⟩]⟩ with
      | .ok c => pure c
      | .error e => throw (.sqlite s!"FAIL: {e}")
    eqTxn (patchEmailOnly ada.id bogus)
      (eqSet (Fields.singleton User.Field.email))
      "H patch email survives name"
    let st ← DbState.load (s := App)
    match (DbState.get (α := User) st).rows.find? (·.id == ada.id) with
    | none => throw (.sqlite "FAIL: ada missing")
    | some row =>
        unless row.val.name == "ada" do
          throw (.sqlite "FAIL: sqlite name was overwritten")
        unless row.val.email == "new@x" do
          throw (.sqlite "FAIL: sqlite email not written")
        unless row.val.tags == [⟨"lead"⟩] do
          throw (.sqlite "FAIL: sqlite tags were overwritten")
    return (1 : Nat)
  ) "patch survives"
  IO.println s!"M14c harness cases: {n}"

def run : IO Unit := do
  testPatchMergeDenote
  testPatchSurvivesHarness
  check (!ForeignKey.anyWithin (α := User) (Fields.singleton User.Field.email))
    "email patch does not touch a Ref"
  check (ForeignKey.anyWithin (α := User) (Fields.singleton User.Field.team))
    "team patch touches a Ref"
  check (!Unique.anyTouch (α := User) (Fields.singleton User.Field.team))
    "team patch does not touch a unique index"
  check (Unique.anyTouch (α := User) (Fields.singleton User.Field.email))
    "email patch touches byEmail"
  check usersJoin.exact "join along a foreign key is exact"
  check (!residualQ.exact) "opaque residual is not exact"

end TestsM14c
