import TestsModel.Twin
import CheckAxioms

/- Generality fixture: a library-loans domain, unrelated to any app, built only
from public API (model `deriving Entity`, `constraint` (unique and cascade),
`link`, `internal`, `deriving Changes`, `DB`/`Query` programs,
`derive_requirements`; native `native_schema%`, `migration%`, `Gate`, the
storage hooks). Its programs run on SQLite after a native migration, every step
compared with its pure meaning on the full state, counters included. -/

open LeanDb.Model LeanDb.Native
open LeanDb (Txn Read DbState)

namespace LibraryRuntimeFixture

inductive Shelf where
  | general | reference
  deriving Domain

deriving instance BEq for Shelf

/-! ## The database before books had a shelf -/

namespace V1
structure Member where
  name  : Name
  email : Email
  deriving Entity

structure Book where
  title : Title
  deriving Entity

structure Loan where
  book   : Ref Book
  member : Ref Member
  deriving Entity

constraint Member.uniqueEmail : unique email
constraint Loan.onePerMember : unique (book, member)
-- Deleting a book deletes its loans; a member with loans cannot be deleted.
constraint Loan.removeWithBook : cascade book

native_schema% LibraryV1 := Member, Book, Loan
end V1

/-! ## The current domain -/

structure Member where
  name  : Name
  email : Email
  deriving Entity

structure Book where
  title : Title
  shelf : Shelf
  deriving Entity

structure Loan where
  book   : Ref Book
  member : Ref Member
  deriving Entity

structure MemberCredential where
  member : Ref Member
  hash   : PasswordHash
  deriving Entity

-- Raw loan reads and deletes stay in this module; a member edit cannot change the email.
internal Loan.select, Loan.delete
deriving instance Changes (except := [email]) for Member

constraint Member.uniqueEmail : unique email
constraint Loan.onePerMember : unique (book, member)
constraint Loan.removeWithBook : cascade book
-- The joins this domain reads: a book's borrowers and a member's loan history.
link Loan.book Loan.member
link Loan.member Loan.book
entity_operations Member, Book, Loan, MemberCredential

native_schema% LibrarySchema := Member, Book, Loan, MemberCredential

/-- Books shelved before shelves existed are on the general shelf. -/
migration% addShelf := Book.addField shelf (fill := .general)

/-! ## Programs -/

inductive JoinError where
  | emailTaken
  deriving Domain

def joinLibrary (name : Name) (email : Email) : DB (Except JoinError (Ref Member)) := do
  match ← Member.insert { name, email } with
  | .ok id => return .ok id
  | .error .uniqueEmail => return .error .emailTaken

def addBook (title : Title) (shelf : Shelf) : DB (Ref Book) :=
  Book.insert { title, shelf }

inductive BorrowError where
  | noSuchBook
  deriving Domain

def borrow (book : Ref Book) (member : Ref Member) : DB (Except BorrowError String) := do
  let some _ ← Book.find book | return .error .noSuchBook
  match ← Loan.insert { book, member } with
  | .ok _ => return .ok "borrowed"
  | .error .onePerMember => return .ok "alreadyBorrowed"

/-- Who borrowed a book: names only, by member id. -/
def borrowers (book : Ref Book) : Query (List Name) :=
  Query.linkField Loan.link.book.member Member.namePath book

/-- A member's loan history: titles only, by book id. -/
def loanHistory (member : Ref Member) : Query (List Title) :=
  Query.linkField Loan.link.member.book Book.titlePath member

def hasLoan (book : Ref Book) (member : Ref Member) : Query Bool := do
  return (← Loan.findBy book member).isSome

def memberByEmail (email : Email) : Query (Option (Ref Member)) := do
  return (← Member.findBy email).map (·.id)

def rename (member : Ref Member) (name : Name) : DB Unit := do
  let some m ← Member.find member | pure ()
  Member.patch m { name }

def withdraw (book : Ref Book) : DB Unit := do
  let some b ← Book.find book | pure ()
  Book.delete b

def expel (member : Ref Member) : DB Unit := do
  let some m ← Member.find member | pure ()
  Member.delete m

derive_requirements joinLibrary, addBook, borrow, borrowers, loanHistory, hasLoan, memberByEmail, rename,
  withdraw, expel

abbrev R := storageResources LibrarySchema

-- A server-only value is a column but never an output: no Wire, no column evidence.
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for goal in [
      ← `(Ontology.Wire PasswordHash),
      ← `(LeanDb.Native.HasColumnEvidence LibrarySchema MemberCredential PasswordHash MemberCredential.hashPath),
      ← `(HasColumnResource R MemberCredential PasswordHash HasEntityResource.witness MemberCredential.hashPath)] do
    let type ← Term.elabType goal
    if (← synthInstance? type).isSome then throwError "unexpected evidence: {type}"
run_cmd assertAxioms ``Loan.onePerMember.nativeKeyAgreement

/-! ## Full-state comparison with the pure meaning -/

def sameTable {T} [LeanDb.Entity T] [LeanDb.IsSchema.Has LibrarySchema T] (a b : DbState LibrarySchema) : Bool :=
  let left := a.get (α := T)
  let right := b.get (α := T)
  left.next == right.next && left.rows.length == right.rows.length &&
    (left.rows.zip right.rows).all fun (x, y) =>
      x.id == y.id && LeanDb.Entity.encode x.val == LeanDb.Entity.encode y.val

def same (a b : DbState LibrarySchema) : Bool :=
  sameTable (T := Member) a b && sameTable (T := Book) a b && sameTable (T := Loan) a b &&
    sameTable (T := MemberCredential) a b

open TestsModel (fail check)
open TestsModel.Native (wire)

/-- `ok:<value>`, `domain:<wire error>`, or the storage fault. -/
def outcome {E A : Type} [Ontology.Wire E] (render : A → String) : Except E A → String
  | .ok value => render value
  | .error error => "domain:" ++ wire error

def command {E A : Type} [Ontology.Wire E] (render : A → String)
    (program : {σ : Type} → Program R .command σ (Except E A)) (label : String) :
    LeanDb.Db (String × Except StorageFault (Except E A)) := do
  let (_, result) ← TestsModel.Native.command same (outcome render) program label
  let shown := match result with
    | .ok (.ok value) => "ok:" ++ render value
    | .ok (.error error) => "domain:" ++ wire error
    | .error fault => TestsModel.Native.render (fun (_ : Unit) => "") (.error fault)
  return (shown, result)

/-- A step that cannot fail in the domain channel. -/
def total {A : Type} (render : A → String) (program : {σ : Type} → Program R .command σ A) (label : String) :
    LeanDb.Db (String × Except StorageFault A) :=
  TestsModel.Native.command same render program label

def query {A : Type} (render : A → String) (program : Program R .query Unit A) (label : String) : LeanDb.Db String :=
  TestsModel.Native.query same render program label

def explain (sql : String) (binds : Array LeanDb.Col) : LeanDb.Db (List String) :=
  LeanDb.untrackedSqlite fun db => do
    let stmt ← db.prepare ("EXPLAIN QUERY PLAN " ++ sql)
    LeanDb.bindCols stmt 1 binds
    let mut details : Array String := #[]
    while ← stmt.step do details := details.push (← stmt.columnText 3)
    return details.toList

def parse {α} (label : String) (result : Ontology.Validation α) : IO α :=
  match result with
  | .ok value => pure value
  | .error _ => throw (IO.userError s!"fixture value {label}")

def key {T} (ref : Ref T) : String := ref.key
def unit : Unit → String := fun _ => "()"
def names (values : List Name) : String := toString (values.map (·.value))
def titles (values : List Title) : String := toString (values.map (·.value))

def run : IO Unit := do
  IO.FS.createDirAll ".lake/ddd-m2-scratch"
  let nonce ← IO.monoNanosNow
  let path : System.FilePath := s!".lake/ddd-m2-scratch/leandb-library-runtime-{nonce}.sqlite"
  let [ada, ben, cy, dee] ← ["Ada", "Ben", "Cy", "Dee"].mapM fun n => parse n (Name.parse n)
    | throw (IO.userError "names")
  let [adaEmail, benEmail, cyEmail, deeEmail] ← ["ada@library.test", "ben@library.test", "cy@library.test",
      "dee@library.test"].mapM fun e => parse e (Email.parse e)
    | throw (IO.userError "emails")
  let [dune, emma, fables] ← ["Dune", "Emma", "Fables"].mapM fun t => parse t (Title.parse t)
    | throw (IO.userError "titles")
  let adele ← parse "Adele" (Name.parse "Adele")
  -- 1. A database from before books had a shelf, with loans out of member order.
  match ← LeanDb.withDb path (LeanDb.IsSchema.specs V1.LibraryV1) do
    for (name, email) in [(ada, adaEmail), (ben, benEmail), (cy, cyEmail)] do
      discard <| LeanDb.insert V1.Member ⟨name, email⟩
    for title in [dune, emma] do discard <| LeanDb.insert V1.Book ⟨title⟩
    for (book, member) in [(2, 3), (2, 1), (1, 2)] do
      let .ok bookRef := idToRef (T := V1.Book) ⟨book⟩ | throw (.sqlite "book ref")
      let .ok memberRef := idToRef (T := V1.Member) ⟨member⟩ | throw (.sqlite "member ref")
      discard <| LeanDb.insert V1.Loan ⟨bookRef, memberRef⟩
  with
  | .error e => throw (IO.userError s!"seed: {e}")
  | .ok () => pure ()
  -- 2. The gate refuses the new required field until the migration fills it.
  let target := LeanDb.Gate.Target.ofSchema LibrarySchema
  let raw ← match ← LeanDb.openDbRaw path with
    | .ok conn => pure conn
    | .error e => throw (IO.userError s!"raw: {e}")
  match ← LeanDb.Gate.check raw target [] with
  | .ok (.refused [.missingFill "Book" "book" "shelf"]) => pure ()
  | .ok status => throw (IO.userError s!"expected the shelf refusal:\n{status.render}")
  | .error e => throw (IO.userError s!"check: {e}")
  let conn ← match ← LeanDb.Gate.openDb path target [addShelf] with
    | .ok (conn, .applied ..) => pure conn
    | _ => throw (IO.userError "the shelf migration did not apply")
  match ← LeanDb.DbM.run conn (show LeanDb.Db Unit from do
    let migrated ← DbState.load (s := LibrarySchema)
    check ((migrated.get (α := Book)).rows.all (·.val.shelf == .general) &&
      (migrated.get (α := Book)).rows.length == 2 && (migrated.get (α := Loan)).rows.length == 3)
      "existing books are on the general shelf, loans kept"
    let refOf {T} [Ontology.HasTypeId T] (n : Int64) : LeanDb.Db (Ref T) :=
      match idToRef (T := T) ⟨n⟩ with
      | .ok r => pure r
      | .error why => fail why
    let adaRef : Ref Member ← refOf 1
    let benRef : Ref Member ← refOf 2
    let duneRef : Ref Book ← refOf 1
    let emmaRef : Ref Book ← refOf 2
    -- Members: a new one, and the unique email as a domain error with nothing written.
    let (joined, result) ← command key (joinLibrary.withResources joinLibrary.Requirements.infer dee deeEmail) "join"
    check (joined == "ok:4") s!"join: {joined}"
    let .ok (.ok deeRef) := result | fail "join result"
    let before ← DbState.load (s := LibrarySchema)
    let (taken, _) ← command key (joinLibrary.withResources joinLibrary.Requirements.infer adele adaEmail) "join taken"
    check (taken == "domain:\"emailTaken\"") s!"email taken: {taken}"
    check (same before (← DbState.load (s := LibrarySchema))) "the conflict wrote nothing"
    let found ← query (fun r => match r with | some r => key r | none => "none")
      (memberByEmail.withResources memberByEmail.Requirements.infer adaEmail) "Member.findBy"
    check (found == "ok:1") s!"findBy email: {found}"
    -- Books and loans: the composite unique is a conflict value.
    let (added, result) ← total key (addBook.withResources addBook.Requirements.infer fables .reference) "addBook"
    check (added == "ok:3") s!"addBook: {added}"
    let .ok fablesRef := result | fail "book result"
    let (borrowed, _) ← command id (borrow.withResources borrow.Requirements.infer fablesRef deeRef) "borrow"
    check (borrowed == "ok:borrowed") s!"borrow: {borrowed}"
    let before ← DbState.load (s := LibrarySchema)
    let (again, _) ← command id (borrow.withResources borrow.Requirements.infer fablesRef deeRef) "borrow again"
    check (again == "ok:alreadyBorrowed") s!"(book, member) unique: {again}"
    check (same before (← DbState.load (s := LibrarySchema))) "the duplicate loan wrote nothing"
    let missing : Ref Book ← refOf 999
    let (noBook, _) ← command id (borrow.withResources borrow.Requirements.infer missing deeRef) "borrow missing"
    check (noBook == "domain:\"noSuchBook\"") s!"no such book: {noBook}"
    for (book, member, want) in [(emmaRef, adaRef, "ok:true"), (duneRef, adaRef, "ok:false")] do
      let has ← query toString (hasLoan.withResources hasLoan.Requirements.infer book member) "Loan.findBy"
      check (has == want) s!"composite findBy: {has}"
    -- The joins, both directions: one column, by target id.
    let emmaBorrowers ← query names (borrowers.withResources borrowers.Requirements.infer emmaRef) "borrowers"
    check (emmaBorrowers == "ok:[Ada, Cy]") s!"borrowers by member id (Cy borrowed first): {emmaBorrowers}"
    let adaHistory ← query titles (loanHistory.withResources loanHistory.Requirements.infer adaRef) "loan history"
    check (adaHistory == "ok:[Emma]") s!"loan history: {adaHistory}"
    let deeHistory ← query titles (loanHistory.withResources loanHistory.Requirements.infer deeRef) "loan history"
    check (deeHistory == "ok:[Fables]") s!"loan history: {deeHistory}"
    let links := HasLinkStorage.storage (s := LibrarySchema) (Edge := Loan) (parentField := "book") (targetField := "member")
    let history := HasLinkStorage.storage (s := LibrarySchema) (Edge := Loan) (parentField := "member") (targetField := "book")
    let memberName := HasFieldStorage.storage (s := LibrarySchema) (T := Member) (field := "name") (Value := Name)
    let bookTitle := HasFieldStorage.storage (s := LibrarySchema) (T := Book) (field := "title") (Value := Title)
    let borrowersPlan ← explain (@Read.linkFieldSql _ _ _ links.parent.entity links.target.entity links.edge.entity
      links.relation memberName.field) #[.int 2]
    check (borrowersPlan.any (·.contains "COVERING INDEX uq_loan_onePerMember (book=?)") &&
      !(borrowersPlan.any (·.startsWith "SCAN"))) s!"borrowers plan: {borrowersPlan}"
    let historyPlan ← explain (@Read.linkFieldSql _ _ _ history.parent.entity history.target.entity history.edge.entity
      history.relation bookTitle.field) #[.int 1]
    check (historyPlan.any (·.contains "INDEX _leandb_fk_loan_member (member=?)") &&
      !(historyPlan.any (·.startsWith "SCAN"))) s!"history plan: {historyPlan}"
    -- Changes: a member edit without the email.
    let (renamed, _) ← total unit (rename.withResources rename.Requirements.infer adaRef adele) "Member.patch"
    check (renamed == "ok:()") s!"rename: {renamed}"
    let emmaBorrowers ← query names (borrowers.withResources borrowers.Requirements.infer emmaRef) "borrowers"
    check (emmaBorrowers == "ok:[Adele, Cy]") s!"renamed borrower: {emmaBorrowers}"
    -- A member with loans is restricted; withdrawing a book cascades its loans.
    let before ← DbState.load (s := LibrarySchema)
    let (expelled, _) ← total unit (expel.withResources expel.Requirements.infer benRef) "expel restricted"
    check (expelled == "storage:storage.restricted:loan.foreignKey.member") s!"restrict: {expelled}"
    check (same before (← DbState.load (s := LibrarySchema))) "the restricted delete rolled back"
    let (withdrawn, _) ← total unit (withdraw.withResources withdraw.Requirements.infer emmaRef) "withdraw cascades"
    check (withdrawn == "ok:()") s!"withdraw: {withdrawn}"
    let after ← DbState.load (s := LibrarySchema)
    check ((after.get (α := Loan)).rows.length == 2 && (after.get (α := Member)).rows.length == 4 &&
      (after.get (α := Loan)).next == (before.get (α := Loan)).next)
      "Emma's two loans went; members and the loan counter stay"
    let adaHistory ← query titles (loanHistory.withResources loanHistory.Requirements.infer adaRef) "loan history"
    check (adaHistory == "ok:[]") s!"history after withdraw: {adaHistory}"
    -- A PasswordHash column (TEXT) round-trips through the storage hooks.
    let credentials := HasEntityStorage.storage (s := LibrarySchema) (T := MemberCredential)
    check ((LeanDb.Entity.spec MemberCredential).columns.any fun c => c.name == "hash" && c.sqlType == .text)
      "the hash is a TEXT column"
    let hashText := "scrypt$16384$8$1$bGlicmFyeQ$aGFzaA"
    let insert : {σ : Type} → Txn σ LibrarySchema StorageFault (Except Empty (Ref MemberCredential)) :=
      credentials.insert { member := deeRef, hash := Ontology.Trusted.passwordHash hashText }
        ([] : List (Constraint Empty)) id
    let stored ← match ← Txn.run insert with
      | .ok (.ok (.ok ref)) => pure ("ok:" ++ key ref)
      | _ => fail "credential insert"
    check (stored == "ok:1") s!"credential stored: {stored}"
    let .ok (.ok rows) ← Read.run (EntityStorage.select (Scope := Unit) credentials) | fail "credential select"
    check (rows.map (fun r => Ontology.Trusted.passwordHashText r.value.hash) == [hashText]) "the hash reads back exactly"
  ) with
  | .error e => throw (IO.userError e.message)
  | .ok () => IO.println "library runtime on SQLite: migration, unique conflicts, findBy, joins, Changes, restrict, cascade, hash column PASS"

end LibraryRuntimeFixture
