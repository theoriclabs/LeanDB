import LeanDb

/-! M14 part B: schema-derived write failure types, `Txn`, meaning, and
    `Txn.run`. The execution-equals-meaning harness lands next. -/

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
def register {σ} (u : Account) : Txn σ Unit RegisterError (Current σ Account) := do
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
    | .restricted .user_team k => .hasUsers k
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
  | .restricted .user_team k => k

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

def run : IO Unit := do
  testSymbols
  testDenote
  testRun

end TestsM14b
