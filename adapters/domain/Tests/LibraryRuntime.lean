import LeanApp.Domain
import LeanDbDomain
import CheckAxioms

/- Generality fixture: a library-loans domain, unrelated to Partiful, built only
from public API (portable `deriving Entity`, `constraint` (unique and cascade),
`link`, `credential`, `internal`,
`deriving Changes`, plain operations, `derive_operation`; native
`native_schema%`, `migration%`, `Gate`, the storage hooks). It runs
natively on SQLite through the shared `Flow.run`, every step compared with its
pure meaning on the full state, counters included. -/

open LeanApp.Domain LeanDb.Domain
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
-- A member's password hash (a column no read can select).
credential MemberCredential.member MemberCredential.hash
entity_operations Member, Book, Loan, MemberCredential

native_schema% LibrarySchema := Member, Book, Loan, MemberCredential

/-- Books shelved before shelves existed are on the general shelf. -/
migration% addShelf := Book.addField shelf (fill := .general)

/-! ## Operations -/

inductive JoinError where
  | emailTaken

def joinLibrary (name : Name) (email : Email) : Op JoinError (Ref Member) := do
  match ← Member.insert { name, email } with
  | .ok id => pure id
  | .error .uniqueEmail => throw .emailTaken

def addBook (title : Title) (shelf : Shelf) : Op Empty (Ref Book) :=
  Book.insert { title, shelf }

inductive BorrowError where
  | noSuchBook

def borrow (book : Ref Book) (member : Ref Member) : Op BorrowError String := do
  let some _ ← Book.find book | throw .noSuchBook
  match ← Loan.insert { book, member } with
  | .ok _ => pure "borrowed"
  | .error .onePerMember => pure "alreadyBorrowed"

/-- Who borrowed a book: names only, by member id. -/
def borrowers (book : Ref Book) : ReadOp Empty (List Name) := do
  return ← Query.linkField Loan.link.book.member Member.namePath book

/-- A member's loan history: titles only, by book id. -/
def loanHistory (member : Ref Member) : ReadOp Empty (List Title) := do
  return ← Query.linkField Loan.link.member.book Book.titlePath member

def hasLoan (book : Ref Book) (member : Ref Member) : ReadOp Empty Bool := do
  return (← Loan.findBy book member).isSome

def memberByEmail (email : Email) : ReadOp Empty (Option (Ref Member)) := do
  return (← Member.findBy email).map (·.id)

def rename (member : Ref Member) (name : Name) : Op Empty Unit := do
  let some m ← Member.find member | pure ()
  Member.patch m { name }

def withdraw (book : Ref Book) : Op Empty Unit := do
  let some b ← Book.find book | pure ()
  Book.delete b

def expel (member : Ref Member) : Op Empty Unit := do
  let some m ← Member.find member | pure ()
  Member.delete m

derive_operation joinLibrary
derive_operation addBook
derive_operation borrow
derive_operation borrowers
derive_operation loanHistory
derive_operation hasLoan
derive_operation memberByEmail
derive_operation rename
derive_operation withdraw
derive_operation expel

abbrev R := storageResources LibrarySchema

def joinRequirements : joinLibrary.Requirements R := joinLibrary.Requirements.infer
def addBookRequirements : addBook.Requirements R := addBook.Requirements.infer
def borrowRequirements : borrow.Requirements R := borrow.Requirements.infer
def borrowersRequirements : borrowers.Requirements R := borrowers.Requirements.infer
def historyRequirements : loanHistory.Requirements R := loanHistory.Requirements.infer
def hasLoanRequirements : hasLoan.Requirements R := hasLoan.Requirements.infer
def emailRequirements : memberByEmail.Requirements R := memberByEmail.Requirements.infer
def renameRequirements : rename.Requirements R := rename.Requirements.infer
def withdrawRequirements : withdraw.Requirements R := withdraw.Requirements.infer
def expelRequirements : expel.Requirements R := expel.Requirements.infer

-- A server-only value is a column but never an output: no Wire, no column evidence.
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  for goal in [
      ← `(Ontology.Wire PasswordHash),
      ← `(LeanDb.Domain.HasColumnEvidence LibrarySchema MemberCredential PasswordHash MemberCredential.hashPath),
      ← `(HasColumnResource R MemberCredential PasswordHash HasEntityResource.witness MemberCredential.hashPath)] do
    let type ← Term.elabType goal
    if (← synthInstance? type).isSome then throwError "unexpected evidence: {type}"
run_cmd assertAxioms ``Loan.onePerMember.nativeKeyAgreement

/-! ## The test algebra (generic in the schema) -/

inductive Failure (E : Type) where
  | domain (error : E)
  | storage (fault : StorageFault)
  | unsupported (what : String)

def Failure.render {E} [Ontology.Wire E] : Failure E → String
  | .domain error => "domain:" ++ (Ontology.Wire.codec.encode error).compress
  | .storage fault => "storage:" ++ fault.code ++
      (match fault with
        | .restricted c | .missingReference c | .unmappedConflict c => ":" ++ c.identity
        | _ => "")
  | .unsupported what => "unsupported:" ++ what

section
variable {s : Type} [LeanDb.IsSchema s]

def commandRequest {σ E A : Type} (now : Instant) :
    RequestF (storageResources s) σ E .command A → Txn σ s (Failure E) A
  | .now => pure now
  | @RequestF.find _ _ _ _ _ inst storage reference =>
      letI := inst
      match storage.find reference with
      | .error why => Txn.throw (.storage (.invalidReference why))
      | .ok read => Txn.ofRead read
  | @RequestF.insert _ _ _ _ _ inst storage value conflicts =>
      letI := inst
      storage.insert value conflicts .storage
  | @RequestF.update _ _ _ _ _ inst storage row patch conflicts =>
      letI := inst
      storage.update row patch conflicts .storage
  | @RequestF.delete _ _ _ _ inst storage row =>
      letI := inst
      storage.delete row .storage
  | @RequestF.findBy _ _ _ _ _ _ inst storage _ lookup key => do
      letI := inst
      match ← Txn.ofRead (storage.findBy lookup key) with
      | .ok row => pure row
      | .error fault => Txn.throw (.storage fault)
  | @RequestF.select _ _ _ _ _ inst storage => do
      letI := inst
      match ← Txn.ofRead storage.select with
      | .ok rows => pure rows
      | .error fault => Txn.throw (.storage fault)
  | @RequestF.linkField _ _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent =>
      match link.project targets column parent with
      | .error why => Txn.throw (.storage (.invalidReference why))
      | .ok read => Txn.ofRead read
  | .hashPassword _ => Txn.throw (.unsupported "hashPassword")
  | @RequestF.verifyCredential _ _ _ _ _ _ _ _ _ _ _ => Txn.throw (.unsupported "verifyCredential")
  | @RequestF.startSession _ _ _ _ _ _ _ _ => Txn.throw (.unsupported "startSession")
  | _ => Txn.throw (.unsupported "milestone-1 request")

def commandAlgebra {σ E : Type} (now : Instant) :
    Algebra (Txn σ s (Failure E)) .command σ E (storageResources s) where
  request := fun request => do return .ok (← commandRequest now request)
  contains := fun _ _ => Txn.throw (.unsupported "contains")
  project := fun _ => Txn.throw (.unsupported "project")

def queryRequest {E A : Type} (now : Instant) :
    RequestF (storageResources s) Unit E .query A → ExceptT (Failure E) (Read s) A
  | .now => pure now
  | @RequestF.find _ _ _ _ _ inst storage reference =>
      letI := inst
      match storage.find reference with
      | .error why => throw (.storage (.invalidReference why))
      | .ok read => liftM read
  | @RequestF.findBy _ _ _ _ _ _ inst storage _ lookup key => do
      letI := inst
      match ← (liftM (storage.findBy lookup key) : ExceptT (Failure E) (Read s) _) with
      | .ok row => pure row
      | .error fault => throw (.storage fault)
  | @RequestF.select _ _ _ _ _ inst storage => do
      letI := inst
      match ← (liftM storage.select : ExceptT (Failure E) (Read s) _) with
      | .ok rows => pure rows
      | .error fault => throw (.storage fault)
  | @RequestF.linkField _ _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent =>
      match link.project targets column parent with
      | .error why => throw (.storage (.invalidReference why))
      | .ok read => liftM read

def queryAlgebra {E : Type} (now : Instant) :
    Algebra (ExceptT (Failure E) (Read s)) .query Unit E (storageResources s) where
  request := fun request => do return .ok (← queryRequest now request)
  contains := fun _ _ => throw (.unsupported "contains")
  project := fun _ => throw (.unsupported "project")
end

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

def fail (label : String) : LeanDb.Db α := throw (.sqlite s!"LibraryRuntime check failed: {label}")

def check (ok : Bool) (label : String) : LeanDb.Db Unit := unless ok do fail label

def runProgram {E A : Type} [Ontology.Wire E] (render : A → String)
    (program : {σ : Type} → Txn σ LibrarySchema (Failure E) A) (label : String) :
    LeanDb.Db (String × Except (Failure E) A) := do
  let before ← DbState.load (s := LibrarySchema)
  check before.checkWF (label ++ ": WF before")
  let expected := Txn.denote (program (σ := Unit)) before
  let show' : Except (Failure E) A → String
    | .ok value => "ok:" ++ render value
    | .error failure => failure.render
  match ← Txn.run program with
  | .error fault => fail s!"{label}: executor fault {fault}"
  | .ok actual =>
      let after ← DbState.load (s := LibrarySchema)
      check after.checkWF (label ++ ": WF after")
      check (show' actual == show' expected.1) s!"{label}: answer {show' actual} vs meaning {show' expected.1}"
      check (same after expected.2) (label ++ ": every table and counter equals the meaning")
      return (show' actual, actual)

def command {E A : Type} [Ontology.Wire E] (now : Instant) (render : A → String)
    (flow : {σ : Type} → Flow .command σ E A R) (label : String) :
    LeanDb.Db (String × Except (Failure E) A) :=
  runProgram render (fun {σ} => do
    match ← Flow.run (commandAlgebra now) (flow (σ := σ)) with
    | .ok value => pure value
    | .error error => Txn.throw (.domain error)) label

def query {E A : Type} [Ontology.Wire E] (now : Instant) (render : A → String)
    (flow : Flow .query Unit E A R) (label : String) : LeanDb.Db String := do
  let program := (Flow.run (queryAlgebra now) flow).run
  let before ← DbState.load (s := LibrarySchema)
  let expected := Read.denote program before
  let show' : Except (Failure E) (Except E A) → String
    | .ok (.ok value) => "ok:" ++ render value
    | .ok (.error error) => "domain:" ++ (Ontology.Wire.codec.encode error).compress
    | .error failure => failure.render
  match ← Read.run program with
  | .error fault => fail s!"{label}: executor fault {fault}"
  | .ok actual =>
      check (show' actual == show' expected) s!"{label}: answer {show' actual} vs meaning {show' expected}"
      check (same before (← DbState.load (s := LibrarySchema))) (label ++ ": a read writes nothing")
      return show' actual

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

def main : IO Unit := do
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
  let now ← parse "now" (Instant.ofEpochSeconds 1000)
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
    let (joined, result) ← command now key (joinLibrary.flowWithResources joinRequirements dee deeEmail) "join"
    check (joined == "ok:4") s!"join: {joined}"
    let .ok deeRef := result | fail "join result"
    let before ← DbState.load (s := LibrarySchema)
    let (taken, _) ← command now key (joinLibrary.flowWithResources joinRequirements adele adaEmail) "join taken"
    check (taken == "domain:\"emailTaken\"") s!"email taken: {taken}"
    check (same before (← DbState.load (s := LibrarySchema))) "the conflict wrote nothing"
    let found ← query now (fun r => match r with | some r => key r | none => "none")
      (memberByEmail.flowWithResources emailRequirements adaEmail) "Member.findBy"
    check (found == "ok:1") s!"findBy email: {found}"
    -- Books and loans: the composite unique is a conflict value.
    let (added, result) ← command now key (addBook.flowWithResources addBookRequirements fables .reference) "addBook"
    check (added == "ok:3") s!"addBook: {added}"
    let .ok fablesRef := result | fail "book result"
    let (borrowed, _) ← command now id (borrow.flowWithResources borrowRequirements fablesRef deeRef) "borrow"
    check (borrowed == "ok:borrowed") s!"borrow: {borrowed}"
    let before ← DbState.load (s := LibrarySchema)
    let (again, _) ← command now id (borrow.flowWithResources borrowRequirements fablesRef deeRef) "borrow again"
    check (again == "ok:alreadyBorrowed") s!"(book, member) unique: {again}"
    check (same before (← DbState.load (s := LibrarySchema))) "the duplicate loan wrote nothing"
    let missing : Ref Book ← refOf 999
    let (noBook, _) ← command now id (borrow.flowWithResources borrowRequirements missing deeRef) "borrow missing"
    check (noBook == "domain:\"noSuchBook\"") s!"no such book: {noBook}"
    for (book, member, want) in [(emmaRef, adaRef, "ok:true"), (duneRef, adaRef, "ok:false")] do
      let has ← query now toString (hasLoan.flowWithResources hasLoanRequirements book member) "Loan.findBy"
      check (has == want) s!"composite findBy: {has}"
    -- The joins, both directions: one column, by target id.
    let emmaBorrowers ← query now names (borrowers.flowWithResources borrowersRequirements emmaRef) "borrowers"
    check (emmaBorrowers == "ok:[Ada, Cy]") s!"borrowers by member id (Cy borrowed first): {emmaBorrowers}"
    let adaHistory ← query now titles (loanHistory.flowWithResources historyRequirements adaRef) "loan history"
    check (adaHistory == "ok:[Emma]") s!"loan history: {adaHistory}"
    let deeHistory ← query now titles (loanHistory.flowWithResources historyRequirements deeRef) "loan history"
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
    let (renamed, _) ← command now unit (rename.flowWithResources renameRequirements adaRef adele) "Member.patch"
    check (renamed == "ok:()") s!"rename: {renamed}"
    let emmaBorrowers ← query now names (borrowers.flowWithResources borrowersRequirements emmaRef) "borrowers"
    check (emmaBorrowers == "ok:[Adele, Cy]") s!"renamed borrower: {emmaBorrowers}"
    -- A member with loans is restricted; withdrawing a book cascades its loans.
    let before ← DbState.load (s := LibrarySchema)
    let (expelled, _) ← command now unit (expel.flowWithResources expelRequirements benRef) "expel restricted"
    check (expelled == "storage:storage.restricted:loan.foreignKey.member") s!"restrict: {expelled}"
    check (same before (← DbState.load (s := LibrarySchema))) "the restricted delete rolled back"
    let (withdrawn, _) ← command now unit (withdraw.flowWithResources withdrawRequirements emmaRef) "withdraw cascades"
    check (withdrawn == "ok:()") s!"withdraw: {withdrawn}"
    let after ← DbState.load (s := LibrarySchema)
    check ((after.get (α := Loan)).rows.length == 2 && (after.get (α := Member)).rows.length == 4 &&
      (after.get (α := Loan)).next == (before.get (α := Loan)).next)
      "Emma's two loans went; members and the loan counter stay"
    let adaHistory ← query now titles (loanHistory.flowWithResources historyRequirements adaRef) "loan history"
    check (adaHistory == "ok:[]") s!"history after withdraw: {adaHistory}"
    -- A PasswordHash column (TEXT) round-trips through the storage hooks.
    let credentials := HasEntityStorage.storage (s := LibrarySchema) (T := MemberCredential)
    check ((LeanDb.Entity.spec MemberCredential).columns.any fun c => c.name == "hash" && c.sqlType == .text)
      "the hash is a TEXT column"
    let hashText := "scrypt$16384$8$1$bGlicmFyeQ$aGFzaA"
    let (stored, _) ← runProgram (E := Empty) (fun r => match r with | .ok r => key r | .error e => nomatch e)
      (credentials.insert { member := deeRef, hash := Trusted.passwordHash hashText }
        ([] : List (Constraint Empty)) .storage) "credential insert"
    check (stored == "ok:1") s!"credential stored: {stored}"
    let .ok (.ok rows) ← Read.run (EntityStorage.select (Scope := Unit) credentials) | fail "credential select"
    check (rows.map (fun r => Trusted.passwordHashText r.value.hash) == [hashText]) "the hash reads back exactly"
  ) with
  | .error e => throw (IO.userError e.message)
  | .ok () => IO.println "library runtime on SQLite: migration, unique conflicts, findBy, joins, Changes, restrict, cascade, hash column PASS"

end LibraryRuntimeFixture

def main : IO Unit := LibraryRuntimeFixture.main
