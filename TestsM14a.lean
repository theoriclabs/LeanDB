import LeanDb

/-! M14 part A: typed schema symbols, `DbState`, `Query`, `Read`.
    For each read, `run` equals `denote (← load)` on hand-built states,
    including windows and counts over exact foreign-key joins. -/

namespace TestsM14a

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def check' (condition : Bool) (message : String) : DbM Unit :=
  unless condition do throw (.sqlite s!"FAIL: {message}")

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

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

private def dbPath : System.FilePath := ".lake" / "leandb_test_m14a.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def userEq (a b : Stored User) : Bool :=
  a.id == b.id && a.val == b.val

private def teamEq (a b : Stored Team) : Bool :=
  a.id == b.id && a.val == b.val

private def optUser : Option (Stored User) → Option (Stored User) → Bool
  | none, none => true
  | some a, some b => userEq a b
  | _, _ => false

private def optTeam : Option (Stored Team) → Option (Stored Team) → Bool
  | none, none => true
  | some a, some b => teamEq a b
  | _, _ => false

private def listUser (as bs : List (Stored User)) : Bool :=
  as.length == bs.length && (as.zip bs).all fun (a, b) => userEq a b

private def listPair (as bs : List (Stored User × Stored Team)) : Bool :=
  as.length == bs.length && (as.zip bs).all fun (a, b) =>
    userEq a.1 b.1 && teamEq a.2 b.2

private def pageUser (a b : Page (Stored User)) : Bool :=
  a.total == b.total && listUser a.items b.items

private def pagePair (a b : Page (Stored User × Stored Team)) : Bool :=
  a.total == b.total && listPair a.items b.items

/-- `run r` equals `denote r (← load)`. -/
private def eqRun {α} (r : Read App α) (eq : α → α → Bool) (msg : String) : DbM α := do
  let st ← DbState.load (s := App)
  match ← Read.run (s := App) r with
  | .error e => throw (.sqlite s!"FAIL: {msg}: fault {e}")
  | .ok got =>
      let want := Read.denote (s := App) r st
      check' (eq got want) s!"{msg}: run ≠ denote (load)"
      return got

/-- The empty unique type is empty, so `IsEmpty` is found. -/
example (u : Unique Team) : False := nomatch u

private def testSymbols : IO Unit := do
  check (!(Entity.check User ⟨"", "a@x", ⟨1⟩, []⟩).isOk) "empty name fails the invariant"
  match Entity.check User ⟨"ada", "ada@x", ⟨1⟩, []⟩ with
  | .error _ => throw <| IO.userError "FAIL: ada should check"
  | .ok c => check (c.val.name == "ada") "Checked.val"
  let _ := User.ListField.tags
  let u : User := ⟨"ada", "ada@x", ⟨1⟩, [⟨"lead"⟩]⟩
  check (u.tags == [⟨"lead"⟩]) "child list field"

private def seed : DbM (Stored Team × Stored Team × Stored User × Stored User × Stored User) := do
  let eng ← insert Team ⟨"eng"⟩
  let ops ← insert Team ⟨"ops"⟩
  let ada ← insert User ⟨"ada", "ada@x", eng.id, [⟨"lead"⟩]⟩
  let alonzo ← insert User ⟨"alonzo", "alonzo@x", eng.id, []⟩
  let grace ← insert User ⟨"grace", "grace@x", ops.id, [⟨"ops"⟩, ⟨"lang"⟩]⟩
  return (eng, ops, ada, alonzo, grace)

private def usersQ : Query App [User] (Stored User) := Query.from User

private def namedAda : Query App [User] (Stored User) :=
  usersQ.where' (fun r => r.val.name == "ada")

private def namedNope : Query App [User] (Stored User) :=
  usersQ.where' (fun r => r.val.name == "nope")

private def namedDesc : Query App [User] (Stored User) :=
  usersQ.orderBy (.desc (User.Field.name : Entity.Field User))

private def withTeam : Query App [User, Team] (Stored User × Stored Team) :=
  (Query.from User).join User.ForeignKey.team

private def testEmpty : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    discard <| eqRun (Read.get User ⟨1⟩) optUser "empty get"
    discard <| eqRun (Read.all usersQ) listUser "empty all"
    discard <| eqRun (Read.count usersQ) (· == ·) "empty count"
    discard <| eqRun (Read.«exists» usersQ) (· == ·) "empty exists"
    discard <| eqRun (Read.first usersQ) optUser "empty first"
    discard <| eqRun (Read.page usersQ { limit := some 10 }) pageUser "empty page"
    discard <| eqRun (Read.lookup User User.Unique.byName "ada") optUser "empty lookup"
    discard <| eqRun (Read.all withTeam) listPair "empty join"
    let st ← DbState.load (s := App)
    check' (st.slots.size == 2) "empty has two table slots"
    check' ((DbState.get (α := User) st).rows.isEmpty) "empty user rows"
    check' ((DbState.get (α := Team) st).next == 1) "empty next is 1"
  discard <| expectOk r "empty"

private def testSeeded : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    let (eng, ops, ada, alonzo, grace) ← seed
    let stHand :=
      (DbState.empty (s := App)
        |>.set (α := Team) { next := 3, rows := [eng, ops] }
        |>.set (α := User) { next := 4, rows := [ada, alonzo, grace] })
    let st ← DbState.load (s := App)
    check' ((DbState.get (α := User) st).rows.length == 3) "loaded 3 users"
    check' ((DbState.get (α := User) st).next == 4) "user next"
    check' ((DbState.get (α := Team) st).next == 3) "team next"
    match (DbState.get (α := User) st).rows with
    | u :: _ => check' (userEq u ada) "load ada"
    | [] => throw (.sqlite "FAIL: load ada: no users")
    check' (listUser
        (Read.denote (s := App) (Read.all usersQ) stHand)
        (Read.denote (s := App) (Read.all usersQ) st))
      "hand-built denote = load denote"
    discard <| eqRun (Read.get User ada.id) optUser "get ada"
    discard <| eqRun (Read.get User ⟨99⟩) optUser "get missing"
    let got ← eqRun (Read.lookup User User.Unique.byName "ada") optUser "lookup byName"
    check' (match got with | some r => r.id == ada.id | none => false) "lookup ada id"
    discard <| eqRun (Read.lookup User User.Unique.byEmail "grace@x") optUser "lookup byEmail"
    discard <| eqRun (Read.lookup User User.Unique.byName "missing") optUser "lookup miss"
    discard <| eqRun (Read.first usersQ) optUser "first id-order"
    discard <| eqRun (Read.all usersQ) listUser "all users"
    discard <| eqRun (Read.all namedAda) listUser "where name"
    discard <| eqRun (Read.all namedDesc) listUser "orderBy name desc"
    discard <| eqRun (Read.count usersQ) (· == ·) "count 3"
    discard <| eqRun (Read.count namedAda) (· == ·) "count 1"
    discard <| eqRun (Read.«exists» namedAda) (· == ·) "exists ada"
    discard <| eqRun (Read.«exists» namedNope) (· == ·) "exists nope"
    discard <| eqRun (Read.page namedDesc { offset := 1, limit := some 1 }) pageUser
      "page exact order"
    check' (withTeam.exact == true) "join is exact"
    discard <| eqRun (Read.all withTeam) listPair "join all"
    discard <| eqRun (Read.first withTeam) (fun a b => match a, b with
      | none, none => true
      | some x, some y => userEq x.1 y.1 && teamEq x.2 y.2
      | _, _ => false) "join first"
    discard <| eqRun (Read.count withTeam) (· == ·) "join count"
    discard <| eqRun (Read.«exists» withTeam) (· == ·) "join exists"
    let win : Window := { offset := 1, limit := some 1 }
    discard <| eqRun (Read.all (withTeam.withWindow win)) listPair
      "join window"
    discard <| eqRun (Read.page withTeam win) pagePair "join page"
    discard <| eqRun (Read.first (withTeam.withWindow win)) (fun a b => match a, b with
      | none, none => true
      | some x, some y => userEq x.1 y.1 && teamEq x.2 y.2
      | _, _ => false) "join first window"
    let prog : Read App Bool := do
      let a ← Read.get User ada.id
      let b ← Read.lookup User User.Unique.byName "grace"
      pure (a.isSome && b.isSome)
    discard <| eqRun prog (· == ·) "bind get+lookup"
    check' ((DbState.get (α := User) st).rows.find? (·.id == grace.id)).isSome
      "grace present"
    let tags :=
      match (DbState.get (α := User) st).rows.find? (·.id == grace.id) with
      | some r => r.val.tags
      | none => []
    check' (tags == [⟨"ops"⟩, ⟨"lang"⟩]) "child list attached"
  discard <| expectOk r "seeded"

private def testSecondState : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    let (eng, _, ada, _, _) ← seed
    discard <| insert User ⟨"barbara", "barb@x", eng.id, []⟩
    let win : Window := { offset := 2, limit := some 2 }
    discard <| eqRun (Read.all (namedDesc.withWindow win)) listUser
      "second state exact window"
    discard <| eqRun (Read.page withTeam { offset := 1, limit := some 2 }) pagePair
      "second state join page"
    discard <| eqRun (Read.count usersQ) (· == ·) "second state count 4"
    discard <| eqRun (Read.get User ada.id) optUser "second state get"
    let st ← DbState.load (s := App)
    check' ((DbState.get (α := User) st).rows.length == 4) "four users"
  discard <| expectOk r "second state"

def run : IO Unit := do
  testSymbols
  testEmpty
  testSeeded
  testSecondState

end TestsM14a
