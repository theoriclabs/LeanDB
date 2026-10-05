/- Generality fixture (libraries stay general): a lending library, unrelated to the post,
   built only from the public `LeanDb.Model` API. It exercises what the post's data model
   uses: a composite unique constraint, a cascade, a link join, `internal` raw operations, a
   `Changes` record, and a rule that takes a proof. Ported from LeanReact's
   `tests/domain/Loans.lean` (its model part); `MemoryRun`/`NativeRun` run it. -/
import LeanDb.Model
open LeanDb.Model

namespace Loans

/-! ## Entities and declarations -/

inductive MemberRole where
  | reader
  | librarian
  deriving DecidableEq

structure Member where
  name  : Name
  email : Email
  role  : MemberRole
  deriving Entity

structure Book where
  title   : Title
  notes   : Text
  addedBy : Ref Member
  deriving Entity

structure Loan where
  book   : Ref Book
  member : Ref Member
  deriving Entity

-- The loan history joins loans to the members who borrowed.
link Loan.book Loan.member
-- Raw loan reads/writes and book deletion stay in this module.
internal Loan.select, Loan.insert, Book.delete
-- An edit cannot change who added the book.
deriving instance Changes (except := [addedBy]) for Book

constraint Member.uniqueEmail : unique email
constraint Loan.oneActive : unique (book, member)
-- Removing a book removes its loans.
constraint Loan.removeWithBook : cascade book
entity_operations Member, Book, Loan

/-- info: Loans.Loan.insert : Loan → DB (Except Loan.Conflict (Ref Loan)) -/
#guard_msgs in #check Loan.insert
/-- info: Loans.Loan.findBy : Ref Book → Ref Member → Query (Option (Row Loan)) -/
#guard_msgs in #check Loan.findBy
/-- info: Loans.Book.patch : Row Book → Book.Changes → DB Unit -/
#guard_msgs in #check Book.patch
/-- info: Loans.Loan.link.book.member : LinkKey Loan Book Member -/
#guard_msgs in #check Loan.link.book.member
/-- info: Loans.Member.update : Row Member → Member → DB (Except Member.Conflict Unit) -/
#guard_msgs in #check Member.update
/-- info: Loans.Book.select : Query (List (Row Book)) -/
#guard_msgs in #check Book.select
#guard (HasRecord.fieldMetadata (T := Book.Changes)).map (·.name) == ["title", "notes"]
#guard Loan.link.book.member.identity == "Loans.Loan.book.member"
#guard Loan.oneActive.key.fields == ["book", "member"]
#guard (Domain.fields (T := Book)).map (fun f => (f.name, f.kind == .reference ⟨"domain", "Loans.Member"⟩)) ==
  [("title", false), ("notes", false), ("addedBy", true)]

/--
info: inductive Loan.Conflict where
  | oneActive
-/
#guard_msgs in #print Loan.Conflict

/-! ## Rules -/

/-- Only librarians add, edit and retire books, and see a book's loan history. -/
abbrev IsLibrarian (m : Row Member) : Prop :=
  m.role = .librarian

/-- Who borrowed this book, by member id: one typed join (Loan ⋈ Member) selecting `name`.
Takes the proof that the viewer is a librarian. -/
def Book.history (b : Row Book) (viewer : Row Member) (_h : IsLibrarian viewer) : Query (List Name) :=
  Query.linkField Loan.link.book.member Member.namePath b.id

/-- The only way to delete a book; its loans go with it (`Loan.removeWithBook`). -/
def Book.retire (b : Row Book) (librarian : Row Member) (_h : IsLibrarian librarian) : DB Unit :=
  Book.delete b

/-- Borrow as yourself. -/
def Loan.open (b : Row Book) (me : Ref Member) : DB (Except Loan.Conflict Unit) := do
  match ← Loan.insert { book := b.id, member := me } with
  | .ok _ => return .ok ()
  | .error conflict => return .error conflict

/-! ## Programs (the storage halves of the library's operations) -/

inductive LoanError where
  | emailTaken
  | notFound
  | notLibrarian
  | alreadyBorrowed
  deriving Repr, BEq, DecidableEq

def join (name : Name) (email : Email) (role : MemberRole) : DB (Except LoanError (Ref Member)) := do
  match ← Member.insert { name, email, role } with
  | .ok id => return .ok id
  | .error .uniqueEmail => return .error .emailTaken

def memberByEmail (email : Email) : Query (Option (Ref Member)) := do
  return (← Member.findBy email).map (·.id)

def addBook (me : Ref Member) (title : Title) (notes : Text) : DB (Except LoanError (Ref Book)) := do
  let some member ← Member.find me | return .error .notLibrarian
  if IsLibrarian member then return .ok (← Book.insert { title, notes, addedBy := me })
  else return .error .notLibrarian

def borrow (me : Ref Member) (book : Ref Book) : DB (Except LoanError Unit) := do
  let some b ← Book.find book | return .error .notFound
  match ← Loan.open b me with
  | .ok _ => return .ok ()
  | .error .oneActive => return .error .alreadyBorrowed

def hasLoan (book : Ref Book) (member : Ref Member) : Query Bool := do
  return (← Loan.findBy book member).isSome

/-- The loan history, for librarians only (`none` otherwise). -/
def history (viewer : Ref Member) (book : Ref Book) : Query (Except LoanError (Option (List Name))) := do
  let some b ← Book.find book | return .error .notFound
  let some m ← Member.find viewer | return .ok none
  if h : IsLibrarian m then return .ok (some (← Book.history b m h)) else return .ok none

def editBook (me : Ref Member) (book : Ref Book) (changes : Book.Changes) : DB (Except LoanError Unit) := do
  let some b ← Book.find book | return .error .notFound
  let some member ← Member.find me | return .error .notLibrarian
  if IsLibrarian member then
    Book.patch b changes
    return .ok ()
  else return .error .notLibrarian

def retire (me : Ref Member) (book : Ref Book) : DB (Except LoanError Unit) := do
  let some b ← Book.find book | return .error .notFound
  let some member ← Member.find me | return .error .notLibrarian
  if h : IsLibrarian member then
    Book.retire b member h
    return .ok ()
  else return .error .notLibrarian

/-- A raw delete of a member: restricted while a loan references them. -/
def expel (member : Ref Member) : DB Bool := do
  let some m ← Member.find member | return false
  Member.delete m
  return true

def bookTitles : Query (List String) := do
  return (← Book.select).map (·.title.value)

def loanCount : Query Nat := do
  return (← Loan.select).length

derive_requirements join, memberByEmail, addBook, borrow, hasLoan, history, editBook, retire, expel,
  bookTitles, loanCount

/--
info: @history.Requirements.infer : {resources : StorageResources} →
  [capability0 : HasEntityResource resources Book] →
    [capability1 : HasEntityResource resources Member] →
      [capability2 : HasEntityResource resources Loan] →
        [capability3 : HasLinkResource resources Loan Book Member HasEntityResource.witness Loan.link.book.member] →
          [capability4 : HasColumnResource resources Member Name HasEntityResource.witness Member.namePath] →
            history.Requirements resources
-/
#guard_msgs in #check @history.Requirements.infer

end Loans
