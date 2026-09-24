import LeanDb

/-! M14 part C: close gaps against QUERIES.md §3 / §5. -/

namespace TestsM14c

open LeanDb
open LeanDb.Harness

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def check' (condition : Bool) (message : String) : DbM Unit :=
  unless condition do throw (.sqlite s!"FAIL: {message}")

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

structure Note where
  body : String
  author : Ref User
  deriving Repr, BEq

cascade% Note.author
deriving instance LeanDb.Entity for Note

schema% App := Team, User, Note

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
  getEq (α := Team) a b && getEq (α := User) a b && getEq (α := Note) a b

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
  requireWF st0 s!"{msg} (load)"
  match ← Txn.run (s := App) p with
  | .error e => throw (.sqlite s!"FAIL: {msg}: fault {e}")
  | .ok got =>
      let (want, stD) := Txn.denote (σ := Unit) (s := App) (p (σ := Unit)) st0
      unless eq got want do
        throw (.sqlite s!"FAIL: {msg}: run ≠ denote")
      requireWF stD s!"{msg} (denote)"
      let st1 ← DbState.load (s := App)
      requireWF st1 s!"{msg} (load after)"
      unless stateEqApp st1 stD do
        throw (.sqlite s!"FAIL: {msg}: final state ≠ denote")

/-- `SetError` on a non-ref field: `missingRef` is omitted — `Within` is
    `Empty`, and `IsEmpty` is found. -/
example (e : SetError User (Fields.singleton User.Field.email)) : Nat :=
  match e with
  | .gone => 0
  | .duplicate _ _ => 1
  | .invalid _ => 2

example [IsEmpty (ForeignKey.Within (α := User) (Fields.singleton User.Field.email))] :
    True := trivial

/-- Writing only `team` (a `Ref`, not a unique column): `duplicate` is omitted. -/
example (e : SetError User (Fields.singleton User.Field.team)) : Nat :=
  match e with
  | .gone => 0
  | .missingRef _ => 1
  | .invalid _ => 2

example [IsEmpty (Unique.Touching (α := User) (Fields.singleton User.Field.team))] :
    True := trivial

/-- Deleting a `User` cannot be restricted: the only inbound key (`Note.author`)
    cascades, so `restricted` is omitted. -/
example (e : DeleteError App User) : Nat :=
  match e with
  | .gone => 0

example [IsEmpty (ReferencedBy.Restricting App User)] : True := trivial

/-- Deleting a `Team` is still restricted by `User.team`. -/
example (e : DeleteError App Team) : Nat :=
  match e with
  | .gone => 0
  | .restricted w k =>
      match ReferencedBy.Restricting.val w with
      | .user_team => k

/-- A residual Lean filter: unwindowed `all` is allowed; `first`/`count`/`exists`
    and `withWindow` are refused. -/
def residualQ : Query App [User] (Stored User) :=
  { Query.from (s := App) User with pred := .opaque fun r => r.val.name == "ada" }

example : Read App (List (Valid User)) := Read.all residualQ

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: this query is not exact: `first`, `count`, `exists`, `page`, and a window need a plan with no opaque leaf (unwindowed `all` may keep a Lean residual). If `decide` cannot close `q.exact = true`, pass an explicit `Exact` proof.
-/
#guard_msgs in
example : Read App (Option (Valid User)) := Read.first residualQ

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: this query is not exact: `first`, `count`, `exists`, `page`, and a window need a plan with no opaque leaf (unwindowed `all` may keep a Lean residual). If `decide` cannot close `q.exact = true`, pass an explicit `Exact` proof.
-/
#guard_msgs in
example : Read App Nat := Read.count residualQ

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: this query is not exact: `first`, `count`, `exists`, `page`, and a window need a plan with no opaque leaf (unwindowed `all` may keep a Lean residual). If `decide` cannot close `q.exact = true`, pass an explicit `Exact` proof.
-/
#guard_msgs in
example : Read App Bool := Read.«exists» residualQ

/--
error: could not synthesize default value for parameter '_h' using tactics
---
error: this query is not exact: `first`, `count`, `exists`, `page`, and a window need a plan with no opaque leaf (unwindowed `all` may keep a Lean residual). If `decide` cannot close `q.exact = true`, pass an explicit `Exact` proof.
-/
#guard_msgs in
example : Query App [User] (Stored User) := residualQ.withWindow { limit := some 1 }

private def usersExact : Query App [User] (Stored User) := Query.from User
private def usersJoin : Query App [User, Team] (Stored User × Stored Team) :=
  (Query.from User).join User.ForeignKey.team

example : residualQ.exact = false := rfl
example : usersExact.exact = true := rfl
private theorem usersJoin_exact : usersJoin.exact = true := by
  unfold usersJoin Query.exact Query.join Query.from
  simp [Pred.andS, Query.Pred.extend, Query.joinPred, Pred.hasOpaque]
  rfl
example : usersJoin.exact = true := usersJoin_exact
example : Read App (Option (Valid User)) := Read.first usersExact
example : Read App Nat := Read.count usersJoin usersJoin_exact
example : Query App [User, Team] (Stored User × Stored Team) :=
  usersJoin.withWindow { limit := some 1 } usersJoin_exact

def patchEmailOnly {σ} (id : _root_.LeanDb.Id User) (new : Checked User) :
    Txn σ App Empty (Except (SetError User (Fields.singleton User.Field.email)) (Stored User)) := do
  match ← Txn.get User id with
  | none =>
      return .error (SetError.gone (α := User) (fs := Fields.singleton User.Field.email))
  | some row =>
      match ← Txn.patch (α := User) row (Fields.singleton User.Field.email) new with
      | .error e => return .error e
      | .ok row => return .ok row.toStored

/-- Changing email keeps the name, so `row.property` proves the new row. -/
private theorem User.email_preserves (u : User) (email : String)
    (h : Invariant User u) : Invariant User { u with email } := by
  unfold Invariant at h ⊢
  refine ⟨?_, ?_⟩
  · exact h.1
  · have heq : Entity.invariant (α := User) =
        some ("TestsM14c.User.invariant", User.invariant) := rfl
    rw [heq] at h ⊢
    simpa [User.invariant] using h.2

/-- LeanAPI `writeStep`: `Read.first` on a filtered query, then
    `Txn.update` with `Checked.of` from `row.property`. No
    `if … invariant … then … else`. -/
def writeEmail {σ} (want : String) (newEmail : String) :
    Txn σ App Empty (Option (Except (UpdateError User) (Stored User))) := do
  let q := (Query.from (s := App) User).where' fun u => u.val.name == want
  match ← Txn.liftRead (Read.first q) with
  | none => return none
  | some row =>
      let new : User := { row.val with email := newEmail }
      some <$> Txn.update (α := User) row (Checked.of new (User.email_preserves row.val newEmail row.property))

/-- Meaning: a non-written field in `new` does not replace the stored one. -/
private def testPatchMergeDenote : IO Unit := do
  let st0 := DbState.empty (s := App)
  let (rTeam, st1) :=
    Txn.denote (σ := Unit) (s := App) (ε := Empty)
      (Txn.insertNew (Checked.of (⟨"eng"⟩ : Team) (by decide))) st0
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
  check (DbState.checkWF st0) "empty denote state is WF"
  check (DbState.checkWF st3) "after patch denote is WF"

/-- Decidable `checkWF`: empty is WF; duplicate unique, dangling FK,
    and id ≥ next are not. A broken invariant cannot inhabit `Valid`. -/
private def vTeam (r : Stored Team) : Valid Team :=
  Valid.ofStored r (by
    unfold Invariant; simp only [sqlRangeOk]; trivial)

private def vUser (r : Stored User) : Valid User :=
  if h : Invariant User r.val then Valid.ofStored r h
  else
    let dummy : User := ⟨"_", r.val.email, r.val.team, r.val.tags⟩
    Valid.ofStored ⟨r.id, dummy⟩ <| by
      unfold Invariant
      simp only [sqlRangeOk]
      refine ⟨trivial, ?_⟩
      change (dummy.name != "") = true
      rfl

private def testCheckWF : IO Unit := do
  let empty := DbState.empty (s := App)
  check (DbState.checkWF empty) "empty is WF"
  let team : Stored Team := ⟨⟨1⟩, ⟨"eng"⟩⟩
  let ada : Stored User := ⟨⟨1⟩, ⟨"ada", "ada@x", ⟨1⟩, [⟨"lead"⟩]⟩⟩
  let good :=
    empty
      |>.set (α := Team) { next := 2, rows := [vTeam team] }
      |>.set (α := User) { next := 2, rows := [vUser ada] }
  check (DbState.checkWF good) "seeded is WF"
  let dup := good.set (α := User) {
    next := 3
    rows := [vUser ada, vUser ⟨⟨2⟩, ⟨"bob", "ada@x", ⟨1⟩, []⟩⟩]
  }
  check (!DbState.checkWF dup) "duplicate email is not WF"
  let dangling := good.set (α := User) {
    next := 2
    rows := [vUser ⟨⟨1⟩, ⟨"ada", "ada@x", ⟨99⟩, []⟩⟩]
  }
  check (!DbState.checkWF dangling) "missing FK is not WF"
  let badId := good.set (α := Team) { next := 1, rows := [vTeam team] }
  check (!DbState.checkWF badId) "id not < next is not WF"
  check (Valid.ofStored? (⟨⟨1⟩, ⟨"", "ada@x", ⟨1⟩, []⟩⟩ : Stored User)).isNone
    "empty name is not Valid"

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

private def dbPathSvc : System.FilePath := ".lake" / "leandb_test_m14c_svc.sqlite"

private def appBase : Base :=
  { name := "m14c", tables := [CliTable.of Team, CliTable.of User, CliTable.of Note] }

/-- `runRead` uses a reader connection (never the writer); `runTxn` uses
    the writer under `BEGIN IMMEDIATE`. -/
private def testRunRead : IO Unit := do
  fresh dbPathSvc
  let svc ← Runtime.Service.new appBase (Instance.ofPath dbPathSvc) .serve true
    { readers := 0 }
  let p : {σ : Type} → Txn σ App Empty (Stored Team) := fun {_} => do
    let row ← Txn.insertNew (Checked.of (⟨"eng"⟩ : Team) (by decide))
    return row.toStored
  let ins ← svc.runTxn (s := App) p
  let team ← match ins with
    | .error f => throw <| IO.userError s!"FAIL: runTxn: {f}"
    | .ok (.error e) => nomatch e
    | .ok (.ok row) => pure row
  check (team.val.name == "eng") "runTxn insert team"
  match ← svc.runRead (s := App) (Read.get Team team.id) with
  | .error f => throw <| IO.userError s!"FAIL: runRead get: {f}"
  | .ok none => throw <| IO.userError "FAIL: runRead missed team"
  | .ok (some row) =>
      check (row.val.name == "eng") "runRead get team"
  let ro ← svc.withReader fun conn => do
    check conn.readOnly "runRead pool connection is read-only"
    DbM.run conn (insert Team ⟨"nope"⟩)
  match ro with
  | .ok (.error e) =>
      check (e.code == "read_only") s!"write on reader: {e}"
  | .ok (.ok _) =>
      throw <| IO.userError "FAIL: Read/withReader handed out the writer"
  | .error e => throw <| IO.userError s!"FAIL: withReader: {e}"
  match ← svc.runRead (s := App) (Read.count (Query.from Team)) with
  | .error f => throw <| IO.userError s!"FAIL: runRead count: {f}"
  | .ok 1 => pure ()
  | .ok k => throw <| IO.userError s!"FAIL: runRead count {k}"
  svc.close

private def eqDelUser :
    Except Empty (Except (DeleteError App User) (Stored User)) →
    Except Empty (Except (DeleteError App User) (Stored User)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error .gone, .error .gone => true
    | .error (.restricted x _), .error (.restricted _ _) => nomatch x
    | _, _ => false

private def eqDelTeam :
    Except Empty (Except (DeleteError App Team) (Stored Team)) →
    Except Empty (Except (DeleteError App Team) (Stored Team)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error .gone, .error .gone => true
    | .error (.restricted _ n1), .error (.restricted _ n2) => n1 == n2
    | _, _ => false

private def eqInsNote :
    Except Empty (Except (InsertError Note) (Stored Note)) →
    Except Empty (Except (InsertError Note) (Stored Note)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error (.missingRef _), .error (.missingRef _) => true
    | .error (.duplicate ..), .error (.duplicate ..) => true
    | _, _ => false

/-- Harness: `ON DELETE CASCADE` removes notes with the user; `RESTRICT`
    still blocks deleting a team that has users. -/
private def testDeleteCascade : IO Unit := do
  fresh dbPath
  let n ← expectOk (← withDb dbPath specs do
    check' (ForeignKey.cascade (α := Note) Note.ForeignKey.author)
      "Note.author ColumnSpec.cascade"
    check' (!ForeignKey.cascade (α := User) User.ForeignKey.team)
      "User.team is restrict"
    check' (((Entity.spec Note).ddl.splitOn "ON DELETE CASCADE").length == 2)
      "Note.author DDL is CASCADE"
    check' (((Entity.spec User).ddl.splitOn "ON DELETE RESTRICT").length == 2)
      "User.team DDL is RESTRICT"
    let (eng, ada) ← seedAda
    let note := Checked.of (⟨"hi", ada.id⟩ : Note) (by
      unfold Invariant; simp only [sqlRangeOk]; trivial)
    eqTxn (fun {_} => do
        let r ← Txn.insert (α := Note) note
        return r.map Current.toStored)
      eqInsNote "H insert note"
    eqTxn (Txn.delete (α := User) ada.id) eqDelUser "H delete user cascades note"
    let st ← DbState.load (s := App)
    unless (DbState.get (α := Note) st).rows.isEmpty do
      throw (.sqlite "FAIL: note survived cascade")
    unless (DbState.get (α := User) st).rows.isEmpty do
      throw (.sqlite "FAIL: user not deleted")
    let ada2 ← match mustCheck ⟨"ada", "ada@x", eng.id, []⟩ with
      | .ok c => pure c
      | .error e => throw (.sqlite e)
    eqTxn (fun {_} => do
        let r ← Txn.insert (α := User) ada2
        return r.map Current.toStored)
      (eqEmpty fun
        | .ok a, .ok b => storedEq a b
        | .error (.duplicate ..), .error (.duplicate ..) => true
        | .error (.missingRef ..), .error (.missingRef ..) => true
        | _, _ => false)
      "H reinsert user after cascade"
    eqTxn (Txn.delete (α := Team) eng.id) eqDelTeam "H delete team restricted"
    return (4 : Nat)
  ) "delete cascade"
  IO.println s!"M14c delete harness cases: {n}"

private def eqInsUser :
    Except Empty (Except (InsertError User) (Stored User)) →
    Except Empty (Except (InsertError User) (Stored User)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error (.duplicate x h1), .error (.duplicate y h2) => uniqueUserEq x y && h1 == h2
    | .error (.missingRef x), .error (.missingRef y) => fkUserEq x y
    | _, _ => false

private def eqUpdUser :
    Except Empty (Except (UpdateError User) (Stored User)) →
    Except Empty (Except (UpdateError User) (Stored User)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error .gone, .error .gone => true
    | .error (.stale a), .error (.stale b) => storedEq a b
    | .error (.duplicate x h1), .error (.duplicate y h2) => uniqueUserEq x y && h1 == h2
    | .error (.missingRef x), .error (.missingRef y) => fkUserEq x y
    | _, _ => false

private def eqWriteEmail :
    Except Empty (Option (Except (UpdateError User) (Stored User))) →
    Except Empty (Option (Except (UpdateError User) (Stored User))) → Bool :=
  eqEmpty fun
    | none, none => true
    | some a, some b =>
        match a, b with
        | .ok x, .ok y => storedEq x y
        | .error .gone, .error .gone => true
        | .error (.stale x), .error (.stale y) => storedEq x y
        | .error (.duplicate x h1), .error (.duplicate y h2) => uniqueUserEq x y && h1 == h2
        | .error (.missingRef x), .error (.missingRef y) => fkUserEq x y
        | _, _ => false
    | _, _ => false

private def eqJoinList :
    Except Empty (List (Valid User × Valid Team)) →
    Except Empty (List (Valid User × Valid Team)) → Bool :=
  eqEmpty fun as bs =>
    as.length == bs.length &&
      (as.zip bs).all fun (a, b) => validEq a.1 b.1 && validEq a.2 b.2

/-- Random M14c programs: field-subset patch, exact join, cascade delete,
    and `writeEmail` (`Read.first` then `Txn.update` from `row.property`).
    Each case compares `run` to `denote` and `load` to `denote` through `get`. -/
private def harnessRandom (seed : Nat) : DbM Nat := do
  let mut rng := Rng.ofNat seed
  let mut n := 0
  eqTxn (fun {_} => do
      let row ← Txn.insertNew
        (Checked.of (⟨s!"eng{seed}"⟩ : Team) (by
          unfold Invariant; simp only [sqlRangeOk]; trivial))
      return row.toStored)
    (eqEmpty storedEq) s!"H{seed} team"
  n := n + 1
  let st ← DbState.load (s := App)
  let team ← match (DbState.get (α := Team) st).rows.head? with
    | some t => pure t
    | none => throw (.sqlite "FAIL: team missing")
  for i in [0:4] do
    let name := if i == 0 then "ada" else s!"u{seed}_{i}"
    let email := s!"e{seed}_{i}@x"
    let c ← match mustCheck ⟨name, email, team.id, [⟨"t"⟩]⟩ with
      | .ok c => pure c
      | .error e => throw (.sqlite e)
    eqTxn (fun {_} => do
        let r ← Txn.insert (α := User) c
        return r.map Current.toStored)
      eqInsUser s!"H{seed} user {i}"
    n := n + 1
  let st ← DbState.load (s := App)
  let users := (DbState.get (α := User) st).rows
  for u in users do
    let note := Checked.of (⟨s!"n{u.val.name}", u.id⟩ : Note)
      (by unfold Invariant; simp only [sqlRangeOk]; trivial)
    eqTxn (fun {_} => do
        let r ← Txn.insert (α := Note) note
        return r.map Current.toStored)
      eqInsNote s!"H{seed} note {u.val.name}"
    n := n + 1
  for u in users do
    let (r1, k) := rng.nat 0 99
    rng := r1
    let bogus ← match mustCheck ⟨"zzz", s!"p{seed}_{k}@x", team.id, [⟨"gone"⟩]⟩ with
      | .ok c => pure c
      | .error e => throw (.sqlite e)
    eqTxn (patchEmailOnly u.id bogus)
      (eqSet (Fields.singleton User.Field.email))
      s!"H{seed} patch {u.val.name}"
    n := n + 1
  for u in users do
    eqTxn (Txn.ofRead (Read.get User u.id)) (eqEmpty optValidEq)
      s!"H{seed} get {u.val.name}"
    n := n + 1
  eqTxn (Txn.ofRead (Read.all usersJoin)) eqJoinList
    s!"H{seed} join"
  n := n + 1
  eqTxn (writeEmail "ada" s!"w{seed}@x") eqWriteEmail s!"H{seed} writeEmail"
  n := n + 1
  match users[0]? with
  | none => pure ()
  | some u =>
      eqTxn (Txn.delete (α := User) u.id) eqDelUser s!"H{seed} cascade"
      n := n + 1
  return n

private def testM14cRandom : IO Unit := do
  let mut n := 0
  for seed in [0:5] do
    fresh dbPath
    n := n + (← expectOk (← withDb dbPath specs (harnessRandom seed))
      s!"M14c random {seed}")
  IO.println s!"M14c random harness cases: {n}"

def run : IO Unit := do
  testPatchMergeDenote
  testCheckWF
  testPatchSurvivesHarness
  testDeleteCascade
  testM14cRandom
  testRunRead
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
  check (ForeignKey.cascade (α := Note) Note.ForeignKey.author) "Note.author cascades"
  check (!ForeignKey.cascade (α := User) User.ForeignKey.team) "User.team restricts"

end TestsM14c
