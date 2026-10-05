/- The lending library on both backends: every step in memory and on SQLite, same answers,
   same tables. Unique conflicts (single and composite), findBy, the link join, `Changes`,
   restrict and cascade. -/
import TestsModel.Loans
import TestsModel.Twin
open LeanDb.Model

namespace LoansRun
open Loans TestsModel
open LeanDb.Native (storageResources)

native_schema% LoansSchema := Member, Book, Loan

abbrev R := storageResources LoansSchema

def tables : List (TestsModel.Table LoansSchema) :=
  [.of LoansSchema Member, .of LoansSchema Book, .of LoansSchema Loan]

def key {T} (ref : Ref T) : String := ref.key
def unit : Unit → String := fun _ => "()"
def result (render : α → String) : Except LoanError α → String
  | .ok value => "ok:" ++ render value
  | .error error => "error:" ++ reprStr error
def names (values : List Name) : String := toString (values.map (·.value))

def run : IO Unit := do
  let [rui, sol, lena, adele] ← ["Rui", "Sol", "Lena", "Adele"].mapM fun n => parse n (Name.parse n)
    | throw (IO.userError "names")
  let [ruiEmail, solEmail, lenaEmail] ← ["rui@example.org", "sol@example.org", "lena@example.org"].mapM
      fun e => parse e (Email.parse e)
    | throw (IO.userError "emails")
  let [dune, emma, dune2] ← ["Dune", "Emma", "Dune (2nd ed.)"].mapM fun t => parse t (Title.parse t)
    | throw (IO.userError "titles")
  let empty ← parse "notes" (Text.parse "")
  let hardcover ← parse "notes" (Text.parse "Hardcover")
  scenario LoansSchema "loans" do
    let step := fun {α} (label : String) (render : α → String) (portable : DB α)
        (native : {σ : Type} → LeanDb.Model.Program R .command σ α) =>
      TestsModel.command tables label render portable native
    let read := fun {α} (label : String) (render : α → String) (portable : Query α)
        (native : LeanDb.Model.Program R .query Unit α) =>
      TestsModel.query tables label render portable native
    -- Members; a duplicate email is a conflict value and writes nothing.
    let r ← step "join Rui" (result key) (join rui ruiEmail .reader) (join.withResources join.Requirements.infer rui ruiEmail .reader)
    check (r == "ok:1") s!"join Rui: {r}"
    let r ← step "join Sol" (result key) (join sol solEmail .reader) (join.withResources join.Requirements.infer sol solEmail .reader)
    check (r == "ok:2") s!"join Sol: {r}"
    let r ← step "join Lena" (result key) (join lena lenaEmail .librarian)
      (join.withResources join.Requirements.infer lena lenaEmail .librarian)
    check (r == "ok:3") s!"join Lena: {r}"
    let r ← step "join taken" (result key) (join adele ruiEmail .reader) (join.withResources join.Requirements.infer adele ruiEmail .reader)
    check (r == "error:Loans.LoanError.emailTaken") s!"duplicate email: {r}"
    let r ← read "findBy email" (fun r => (r.map key).getD "none") (memberByEmail solEmail)
      (memberByEmail.withResources memberByEmail.Requirements.infer solEmail)
    check (r == "2") s!"findBy: {r}"
    let ruiRef ← match Ontology.Ref.parse (T := Member) "1" with | .ok r => pure r | .error _ => fail "ref"
    let solRef ← match Ontology.Ref.parse (T := Member) "2" with | .ok r => pure r | .error _ => fail "ref"
    let lenaRef ← match Ontology.Ref.parse (T := Member) "3" with | .ok r => pure r | .error _ => fail "ref"
    -- A rule that takes a proof: only librarians add books.
    let r ← step "reader adds" (result key) (addBook ruiRef dune empty) (addBook.withResources addBook.Requirements.infer ruiRef dune empty)
    check (r == "error:Loans.LoanError.notLibrarian") s!"reader adds: {r}"
    let r ← step "add Dune" (result key) (addBook lenaRef dune empty) (addBook.withResources addBook.Requirements.infer lenaRef dune empty)
    check (r == "ok:1") s!"add Dune: {r}"
    let r ← step "add Emma" (result key) (addBook lenaRef emma empty) (addBook.withResources addBook.Requirements.infer lenaRef emma empty)
    check (r == "ok:2") s!"add Emma: {r}"
    let duneRef ← match Ontology.Ref.parse (T := Book) "1" with | .ok r => pure r | .error _ => fail "ref"
    let emmaRef ← match Ontology.Ref.parse (T := Book) "2" with | .ok r => pure r | .error _ => fail "ref"
    -- Composite unique (book, member): borrowing twice is a conflict value.
    for (who, book, want) in [(solRef, duneRef, "ok:()"), (ruiRef, duneRef, "ok:()"),
        (ruiRef, duneRef, "error:Loans.LoanError.alreadyBorrowed"), (ruiRef, emmaRef, "ok:()")] do
      let r ← step "borrow" (result unit) (borrow who book) (borrow.withResources borrow.Requirements.infer who book)
      check (r == want) s!"borrow: {r}, expected {want}"
    let r ← read "loans" toString loanCount (loanCount.withResources loanCount.Requirements.infer)
    check (r == "3") s!"three loans: {r}"
    for (book, member, want) in [(emmaRef, ruiRef, "true"), (emmaRef, solRef, "false")] do
      let r ← read "Loan.findBy" toString (hasLoan book member) (hasLoan.withResources hasLoan.Requirements.infer book member)
      check (r == want) s!"composite findBy: {r}"
    -- The join: names by member id (Rui is 1, Sol is 2), for librarians only.
    let history := fun (viewer : Ref Member) (book : Ref Book) =>
      read "history" (result fun h => match h with | some ns => names ns | none => "hidden")
        (Loans.history viewer book) (Loans.history.withResources Loans.history.Requirements.infer viewer book)
    let r ← history lenaRef duneRef
    check (r == "ok:[Rui, Sol]") s!"history by member id: {r}"
    let r ← history ruiRef duneRef
    check (r == "ok:hidden") s!"readers see no history: {r}"
    -- Changes: an edit cannot touch `addedBy`.
    let changes : Book.Changes := { title := dune2, notes := hardcover }
    let r ← step "reader edits" (result unit) (editBook ruiRef duneRef changes)
      (editBook.withResources editBook.Requirements.infer ruiRef duneRef changes)
    check (r == "error:Loans.LoanError.notLibrarian") s!"reader edits: {r}"
    let r ← step "edit" (result unit) (editBook lenaRef duneRef changes)
      (editBook.withResources editBook.Requirements.infer lenaRef duneRef changes)
    check (r == "ok:()") s!"edit: {r}"
    let r ← read "titles" toString bookTitles (bookTitles.withResources bookTitles.Requirements.infer)
    check (r == "[Dune (2nd ed.), Emma]") s!"edited title: {r}"
    -- A member with loans is restricted (a fault on both backends, nothing written).
    let r ← step "expel restricted" toString (expel ruiRef) (expel.withResources expel.Requirements.infer ruiRef)
    check (r == "fault:storage.restricted") s!"restrict: {r}"
    -- Retiring a book cascades its loans: three loans become one.
    let r ← step "reader retires" (result unit) (retire solRef duneRef) (retire.withResources retire.Requirements.infer solRef duneRef)
    check (r == "error:Loans.LoanError.notLibrarian") s!"reader retires: {r}"
    let r ← step "retire" (result unit) (retire lenaRef duneRef) (retire.withResources retire.Requirements.infer lenaRef duneRef)
    check (r == "ok:()") s!"retire: {r}"
    let r ← read "loans" toString loanCount (loanCount.withResources loanCount.Requirements.infer)
    check (r == "1") s!"its two loans went with it: {r}"
    let r ← step "borrow retired" (result unit) (borrow solRef duneRef) (borrow.withResources borrow.Requirements.infer solRef duneRef)
    check (r == "error:Loans.LoanError.notFound") s!"retired book: {r}"
    -- Sol has no loan left: the member delete is allowed now.
    let r ← step "expel" toString (expel solRef) (expel.withResources expel.Requirements.infer solRef)
    check (r == "true") s!"expel: {r}"
  IO.println "loans on memory and SQLite: unique and composite conflicts, findBy, link join, Changes, restrict, cascade PASS"

end LoansRun
