import LeanDb

/-! M14 part B: schema-derived write failure types, `Txn`, meaning,
    `Txn.run`, and the execution-equals-meaning harness. -/

namespace TestsM14b

open LeanDb

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

/-- Account with one unique index, no references: `InsertError` match is
    exhaustive on `.duplicate .byName`. -/
structure Account where
  name : String
  email : String
  deriving Repr, BEq, LeanDb.Entity

unique% Account.byName := name

typed% Account

schema% Acct := Account

/-- Adding `unique Account2.byEmail` makes the same match fail. -/
structure Account2 where
  name : String
  email : String
  deriving Repr, BEq, LeanDb.Entity

unique% Account2.byName := name
unique% Account2.byEmail := email

typed% Account2

/-- `Team` has no unique index and no `Ref`, so `InsertError` is empty. -/
example {e : InsertError Team} : False := InsertError.isEmpty e

example [IsEmpty (InsertError Team)] : True := trivial

/-- `insertNew` requires `[IsEmpty (InsertError α)]`; found for `Team`. -/
private theorem insertNewOk {α : Type} [Entity α] [HasUnique α] [HasForeignKey α]
    [IsEmpty (InsertError α)] (_v : Checked α) : True := trivial

example : True :=
  insertNewOk (α := Team) (Checked.of ⟨"eng"⟩ (by unfold Invariant; trivial))

/-- One unique, no references: the match need not mention `missingRef`. -/
example (e : InsertError Account) : Nat :=
  match e with
  | .duplicate .byName _ => 0

inductive RegisterError where
  | invalid
  | nameTaken
  deriving Repr, DecidableEq

/-- QUERIES.md §3.6 register: a clash on the name is a typed domain failure. -/
def register {σ} (u : Account) : Txn σ Acct RegisterError (Current σ Account) := do
  let c ← Entity.check Account u |>.orAbort fun _ => .invalid
  Txn.insert (α := Account) c |>.orAbort fun
    | .duplicate .byName _ => .nameTaken

inductive NoteError where
  | notFound
  | hasUsers (k : Nat)
  deriving Repr, DecidableEq

/-- QUERIES.md §3.6 delete: who blocks it is in the type. -/
def deleteTeam {σ} (id : _root_.LeanDb.Id Team) : Txn σ App NoteError Unit := do
  let _ ← Txn.delete (α := Team) id |>.orAbort fun
    | .gone => .notFound
    | .restricted w k =>
        match ReferencedBy.Restricting.val w with
        | .user_team => .hasUsers k
  return ()

/-- `insertNew` is available for `Team` (no unique, no `Ref`). -/
def addTeam {σ} (t : Team) : Txn σ App Empty (_root_.LeanDb.Id Team) := do
  let row ← Txn.insertNew (Checked.of t (by unfold Invariant; trivial))
  return row.id

/-- `User` has unique indexes, so `IsEmpty (InsertError User)` is not found.
    This would fail to elaborate: `insertNewOk (α := User) …`. -/
example (e : InsertError User) : Nat :=
  match e with
  | .duplicate .byName _ => 0
  | .duplicate .byEmail _ => 1
  | .missingRef .team => 2

/-- `SetError` on a non-unique, non-ref field: `duplicate` / `missingRef`
    take uninhabited `Touching` / `Within` when `Unique`/`ForeignKey` are
    empty (`Team`). -/
example (e : SetError Team (Fields.all Team)) : Nat :=
  match e with
  | .gone => 0

/-- `DeleteError` on `User`: nothing in `App` references `User`. -/
example (e : DeleteError App User) : Nat :=
  match e with
  | .gone => 0

/-- `DeleteError` on `Team`: `User.team` restricts. -/
example (e : DeleteError App Team) : Nat :=
  match e with
  | .gone => 0
  | .restricted w k =>
      match ReferencedBy.Restricting.val w with
      | .user_team => k

/-- `AppendError` on `Team`: no child lists, so `notAppend` is absent. -/
example (e : AppendError Team) : Nat :=
  match e with
  | .stale _ => 0
  | .gone => 1

-- Adding a unique index makes a non-exhaustive `InsertError` match fail.
/--
error: Missing cases:
(InsertError.duplicate Account2.Unique.byEmail (Id.mk (Int64.ofUInt64 (UInt64.ofBitVec (BitVec.ofFin (Fin.mk _ _))))))
-/
#guard_msgs in
example (e : InsertError Account2) : Nat :=
  match e with
  | .duplicate .byName _ => 0

private def testSymbols : IO Unit := do
  check (Unique.touches (α := User) User.Unique.byName (Fields.singleton User.Field.name))
    "byName touches name"
  check (!Unique.touches (α := User) User.Unique.byName (Fields.singleton User.Field.email))
    "byName does not touch email"
  check (Unique.touches (α := User) User.Unique.byEmail (Fields.singleton User.Field.email))
    "byEmail touches email"
  check (!Unique.touches (α := User) User.Unique.byName (Fields.of [User.Field.team]))
    "byName does not touch team"
  check (ForeignKey.within (α := User) User.ForeignKey.team (Fields.singleton User.Field.team))
    "team is within {team}"
  check (!ForeignKey.within (α := User) User.ForeignKey.team (Fields.singleton User.Field.name))
    "team is not within {name}"
  check ((Unique.all User).size == 2) "User has two unique indexes"
  check ((ForeignKey.all User).size == 1) "User has one foreign key"
  check ((ListField.all User).size == 1) "User has one child list"
  check ((ReferencedBy.all App Team).size == 1) "Team is referenced by User.team"
  check ((ReferencedBy.all App User).size == 0) "User is referenced by no one"
  match Entity.check User ⟨"ada", "ada@x", ⟨1⟩, []⟩ with
  | .error _ => throw <| IO.userError "FAIL: ada should check"
  | .ok c => check (c.val.name == "ada") "Checked.val"

private def testDenote : IO Unit := do
  let st0 := DbState.empty (s := App)
  let (r, st1) := Txn.denote (σ := Unit) (s := App) (addTeam ⟨"eng"⟩) st0
  match r with
  | .error e => nomatch e
  | .ok id =>
      check (id.toInt64 == 1) "first team id is 1"
      check ((DbState.get (α := Team) st1).next == 2) "next is 2"
      check ((DbState.get (α := Team) st1).rows.length == 1) "one team"
  let ada : User := ⟨"ada", "ada@x", ⟨99⟩, []⟩
  match Entity.check User ada with
  | .error _ => throw <| IO.userError "FAIL: ada invariant"
  | .ok cAda => do
      let insAda : Txn Unit App Empty (Except (InsertError User) (Current Unit User)) :=
        Txn.insert (α := User) cAda
      let (r2, _) := Txn.denote insAda st1
      match r2 with
      | .error e => nomatch e
      | .ok (.error (.missingRef .team)) => pure ()
      | .ok (.error (.duplicate ..)) => throw <| IO.userError "FAIL: expected missingRef"
      | .ok (.ok _) => throw <| IO.userError "FAIL: insert ada should miss team"
  let (rAbort, stA) :=
    Txn.denote (σ := Unit) (s := App)
      (Txn.throw (σ := Unit) (s := App) (ε := String) (α := Nat) "nope") st1
  match rAbort with
  | .error "nope" => pure ()
  | _ => throw <| IO.userError "FAIL: throw aborts"
  check ((DbState.get (α := Team) stA).rows.length ==
      (DbState.get (α := Team) st1).rows.length) "abort keeps original state"

private def specs : List TableSpec := IsSchema.specs App

private def dbPath : System.FilePath := ".lake" / "leandb_test_m14b.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

private def testRun : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    match ← Txn.run (s := App) (addTeam ⟨"eng"⟩) with
    | .error e => throw (.sqlite s!"FAIL: run addTeam fault {e}")
    | .ok (.error e) => nomatch e
    | .ok (.ok id) =>
        let st ← DbState.load (s := App)
        let (want, stD) := Txn.denote (σ := Unit) (s := App) (addTeam ⟨"eng"⟩)
          (DbState.empty (s := App))
        match want with
        | .error e => nomatch e
        | .ok idD =>
            unless id.toInt64 == idD.toInt64 do
              throw (.sqlite "FAIL: run id ≠ denote id")
            unless (DbState.get (α := Team) st).next ==
                (DbState.get (α := Team) stD).next do
              throw (.sqlite "FAIL: run next ≠ denote next")
  discard <| expectOk r "run addTeam"

open LeanDb.Harness

private def stateEqApp (a b : DbState App) : Bool :=
  getEq (α := Team) a b && getEq (α := User) a b

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

private def eqEmpty {α} (eq : α → α → Bool) :
    Except Empty α → Except Empty α → Bool
  | .ok a, .ok b => eq a b
  | .error e, _ => nomatch e
  | _, .error e => nomatch e

private def insertUser {σ} (c : Checked User) :
    Txn σ App Empty (Except (InsertError User) (Stored User)) := do
  let r ← Txn.insert (α := User) c
  return r.map Current.toStored

private def insertTeam {σ} (t : Team) : Txn σ App Empty (Stored Team) := do
  let row ← Txn.insertNew (Checked.of t (by unfold Invariant; trivial))
  return row.toStored

private def mustValid {α} [Entity α] (r : Stored α) : DbM (Valid α) :=
  match Valid.ofStored? r with
  | some v => return v
  | none => throw (.sqlite "test row failed Invariant")

private def getStored {σ α} [Entity α] [IsSchema.Has App α]
    (id : _root_.LeanDb.Id α) :
    Txn σ App Empty (Option (Stored α)) := do
  let r ← Txn.get α id
  return r.map Current.toStored

private def lookupStored {σ α} [Entity α] [HasUnique α] [IsSchema.Has App α]
    (ix : Unique α) (key : Unique.Key ix) :
    Txn σ App Empty (Option (Stored α)) := do
  let r ← Txn.lookup α ix key
  return r.map Current.toStored

private def mustCheck (u : User) : DbM (Checked User) :=
  match Entity.check User u with
  | .ok c => return c
  | .error _ => throw (.sqlite s!"FAIL: check {u.name}")

private def seedWF : DbM (Stored Team × Stored User × Stored User) := do
  let eng ← LeanDb.insert Team ⟨"eng"⟩
  let ada ← LeanDb.insert User ⟨"ada", "ada@x", eng.id, [⟨"lead"⟩]⟩
  let alonzo ← LeanDb.insert User ⟨"alonzo", "alonzo@x", eng.id, []⟩
  return (eng, ada, alonzo)

private def abortStr {α} (eqA : α → α → Bool) :
    Except String α → Except String α → Bool :=
  exceptEq (fun x y => x == y) eqA

private def noteEq : Except NoteError Unit → Except NoteError Unit → Bool :=
  exceptEq (fun x y => decide (x = y)) (fun (_ _ : Unit) => true)

private def uniqueUserEq (a b : Unique User) : Bool :=
  match a, b with
  | .byName, .byName => true
  | .byEmail, .byEmail => true
  | _, _ => false

private def fkUserEq (a b : ForeignKey User) : Bool :=
  match a, b with
  | .team, .team => true

private def lfUserEq (a b : ListField User) : Bool :=
  match a, b with
  | .tags, .tags => true

private def rbTeamEq (a b : ReferencedBy App Team) : Bool :=
  match a, b with
  | .user_team, .user_team => true

private def eqIns :
    Except Empty (Except (InsertError User) (Stored User)) →
    Except Empty (Except (InsertError User) (Stored User)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error (.duplicate x h1), .error (.duplicate y h2) => uniqueUserEq x y && h1 == h2
    | .error (.missingRef x), .error (.missingRef y) => fkUserEq x y
    | _, _ => false

private def eqUpd :
    Except Empty (Except (UpdateError User) (Stored User)) →
    Except Empty (Except (UpdateError User) (Stored User)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error .gone, .error .gone => true
    | .error (.stale a), .error (.stale b) => storedEq a b
    | .error (.duplicate x h1), .error (.duplicate y h2) => uniqueUserEq x y && h1 == h2
    | .error (.missingRef x), .error (.missingRef y) => fkUserEq x y
    | _, _ => false

private def eqApp :
    Except Empty (Except (AppendError User) (Stored User)) →
    Except Empty (Except (AppendError User) (Stored User)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error .gone, .error .gone => true
    | .error (.stale a), .error (.stale b) => storedEq a b
    | .error (.notAppend x), .error (.notAppend y) => lfUserEq x y
    | .error (.duplicate x h1), .error (.duplicate y h2) => uniqueUserEq x y && h1 == h2
    | .error (.missingRef x), .error (.missingRef y) => fkUserEq x y
    | _, _ => false

private def eqDelTeam :
    Except Empty (Except (DeleteError App Team) (Stored Team)) →
    Except Empty (Except (DeleteError App Team) (Stored Team)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error .gone, .error .gone => true
    | .error (.restricted x n1), .error (.restricted y n2) =>
        rbTeamEq (ReferencedBy.Restricting.val x) (ReferencedBy.Restricting.val y) && n1 == n2
    | _, _ => false

private def eqDelUser :
    Except Empty (Except (DeleteError App User) (Stored User)) →
    Except Empty (Except (DeleteError App User) (Stored User)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error .gone, .error .gone => true
    | .error (.restricted x _), .error (.restricted _ _) => nomatch x
    | _, _ => false

private def eqSet (fs : Fields User) :
    Except Empty (Except (SetError User fs) (Stored User)) →
    Except Empty (Except (SetError User fs) (Stored User)) → Bool :=
  eqEmpty fun
    | .ok a, .ok b => storedEq a b
    | .error .gone, .error .gone => true
    | .error (.duplicate x h1), .error (.duplicate y h2) => uniqueUserEq x.ix y.ix && h1 == h2
    | .error (.missingRef x), .error (.missingRef y) => fkUserEq x.fk y.fk
    | _, _ => false

/-- Hand cases. Returns how many comparisons ran. -/
private def harnessCases : DbM Nat := do
  let mut n := 0
  eqTxn (insertTeam ⟨"eng"⟩) (eqEmpty storedEq) "H insert team"
  n := n + 1
  let c ← mustCheck ⟨"ada", "ada@x", ⟨1⟩, []⟩
  eqTxn (insertUser c) eqIns "H insert ada"
  n := n + 1
  let c ← mustCheck ⟨"ada", "dup@x", ⟨1⟩, []⟩
  eqTxn (insertUser c) eqIns "H duplicate byName"
  n := n + 1
  let c ← mustCheck ⟨"grace", "ada@x", ⟨1⟩, []⟩
  eqTxn (insertUser c) eqIns "H duplicate byEmail"
  n := n + 1
  let c ← mustCheck ⟨"miss", "miss@x", ⟨99⟩, []⟩
  eqTxn (insertUser c) eqIns "H missingRef"
  n := n + 1
  eqTxn (deleteTeam ⟨1⟩) noteEq "H deleteTeam restricted"
  n := n + 1
  eqTxn (Txn.delete (α := Team) ⟨1⟩) eqDelTeam "H delete team restricted"
  n := n + 1
  eqTxn (Txn.delete (α := User) ⟨1⟩) eqDelUser "H delete user"
  n := n + 1
  eqTxn (Txn.delete (α := User) ⟨1⟩) eqDelUser "H delete user gone"
  n := n + 1
  eqTxn (Txn.delete (α := Team) ⟨1⟩) eqDelTeam "H delete team"
  n := n + 1
  eqTxn (insertTeam ⟨"ops"⟩) (eqEmpty storedEq) "H insert ops"
  n := n + 1
  eqTxn (getStored (α := Team) ⟨1⟩) (eqEmpty optStoredEq) "H get team after delete"
  n := n + 1
  eqTxn (do
      let _ ← Txn.insertNew (Checked.of (⟨"tmp"⟩ : Team) (by unfold Invariant; trivial))
      Txn.throw (α := Unit) "rollback"
    ) (abortStr fun _ _ => true) "H insert then abort"
  n := n + 1
  return n

private def harnessSeeded : DbM Nat := do
  let mut n := 0
  let (eng, ada, alonzo) ← seedWF
  eqTxn (Txn.ofRead (Read.get User ada.id)) (eqEmpty optValidEq) "H liftRead get"
  n := n + 1
  let c ← mustCheck ⟨ada.val.name, ada.val.email, ada.val.team, ada.val.tags ++ [⟨"x"⟩]⟩
  let adaV ← mustValid ada
  eqTxn (Txn.append (α := User) adaV c) eqApp "H append tags"
  n := n + 1
  let c ← mustCheck ⟨ada.val.name, ada.val.email, ada.val.team, []⟩
  eqTxn (Txn.append (α := User) adaV c) eqApp "H notAppend"
  n := n + 1
  let c ← mustCheck { ada.val with email := "other@x" }
  eqTxn (Txn.update (α := User) adaV c) eqUpd "H update email"
  n := n + 1
  let goneV ← mustValid ⟨⟨99⟩, ada.val⟩
  eqTxn (Txn.update (α := User) goneV c) eqUpd "H update gone"
  n := n + 1
  eqTxn (Txn.throw (α := Nat) "stop") (abortStr fun a b => a == b) "H throw abort"
  n := n + 1
  let c ← mustCheck ⟨"barb", "barb@x", eng.id, []⟩
  eqTxn (fun {_} => do
      let r ← Txn.insert (α := User) c
      match r with
      | .error _ => return none
      | .ok row => return some row.toStored
    ) (eqEmpty optStoredEq) "H insert then Stored"
  n := n + 1
  eqTxn (Txn.delete (α := User) alonzo.id) eqDelUser "H delete alonzo"
  n := n + 1
  let c ← mustCheck { ada.val with email := "ada2@x" }
  eqTxn (fun {_} => do
      match ← Txn.get User ada.id with
      | none =>
          return (Except.error
            (SetError.gone (α := User) (fs := Fields.singleton User.Field.email)))
      | some row =>
          match ← Txn.patch (α := User) row (Fields.singleton User.Field.email) c with
          | Except.error e => return Except.error e
          | Except.ok row => return Except.ok row.toStored
    ) (eqSet (Fields.singleton User.Field.email)) "H patch email"
  n := n + 1
  eqTxn (fun {_} => do
      match ← Txn.get User ada.id with
      | none =>
          return (Except.error (SetError.gone (α := User) (fs := Fields.all User)))
      | some row =>
          match ← Txn.set (α := User) row c with
          | Except.error e => return Except.error e
          | Except.ok row => return Except.ok row.toStored
    ) (eqSet (Fields.all User)) "H set"
  n := n + 1
  let c ← mustCheck ⟨"barb", "barb2@x", eng.id, []⟩
  eqTxn (Txn.orElse (do
        let r ← Txn.insert (α := User) c
        return r.map fun row => row.id
      ) fun
        | .duplicate _ holder => Txn.pure holder
        | .missingRef _ => Txn.pure ⟨0⟩
    ) (eqEmpty fun a b => a == b) "H orElse duplicate"
  n := n + 1
  return n

private def harnessRandom (seed : Nat) : DbM Nat := do
  let mut rng := Rng.ofNat seed
  let mut n := 0
  for i in [0:8] do
    let (r1, k) := rng.nat 0 2
    rng := r1
    let name := s!"t{seed}_{i}_{k}"
    eqTxn (insertTeam ⟨name⟩) (eqEmpty storedEq) s!"H rand team {i}"
    n := n + 1
  let st ← DbState.load (s := App)
  let teams := (DbState.get (α := Team) st).rows
  if !teams.isEmpty then
    for i in [0:8] do
      let (r1, ti) := rng.nat 0 (teams.length - 1)
      rng := r1
      match teams[ti]? with
      | none => pure ()
      | some team =>
          let (r2, dup) := rng.bool
          rng := r2
          let u : User :=
            if dup && i > 0 then ⟨s!"u{seed}_0", s!"e{seed}_{i}@x", team.id, []⟩
            else ⟨s!"u{seed}_{i}", s!"e{seed}_{i}@x", team.id, []⟩
          let c ← mustCheck u
          eqTxn (insertUser c) eqIns s!"H rand user {i}"
          n := n + 1
    let st ← DbState.load (s := App)
    let users := (DbState.get (α := User) st).rows
    for u in users do
      eqTxn (getStored u.id) (eqEmpty optStoredEq) s!"H rand get {u.val.name}"
      n := n + 1
      eqTxn (lookupStored (α := User) User.Unique.byName u.val.name)
        (eqEmpty optStoredEq) s!"H rand lookup {u.val.name}"
      n := n + 1
  return n

private def testHarness : IO Unit := do
  let mut n := 0
  fresh dbPath
  n := n + (← expectOk (← withDb dbPath specs harnessCases) "harness cases")
  fresh dbPath
  n := n + (← expectOk (← withDb dbPath specs harnessSeeded) "harness seeded")
  for seed in [0:5] do
    fresh dbPath
    n := n + (← expectOk (← withDb dbPath specs (harnessRandom seed))
      s!"harness random {seed}")
  IO.println s!"M14b harness cases: {n}"

def run : IO Unit := do
  testSymbols
  testDenote
  testRun
  testHarness

end TestsM14b
