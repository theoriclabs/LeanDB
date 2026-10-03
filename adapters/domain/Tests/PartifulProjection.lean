import Partiful.Domain
import LeanDbDomain.Schema
import LeanDbDomain.Access
import LeanDbDomain.Operations
import CheckAxioms

/- The actual authored business domain is imported unchanged. This fixture only
supplies a query algebra to TEST shared Flow.run; production algebra is API-owned.
No per-operation native handler or second Flow interpreter is implemented. -/
namespace PartifulProjectionFixture
open LeanApp.Domain LeanDb.Domain
open Partiful Ontology

native_schema% S := Partiful.Person, Partiful.Party

def requirements : partyPage.Requirements (storageResources S) := partyPage.Requirements.infer (resources := storageResources S)

/-- Exercise API's composition pattern without supplying or simulating auth.
    Any API-owned dependent auth slot must leave DB column evidence intact. -/
@[reducible] def withAuth (authSlot : {T : Type} → EntityStorage S T → Type 1) : ResourceFamily :=
  { storageResources S with auth := authSlot }

instance {T} (authSlot : {T : Type} → EntityStorage S T → Type 1) [HasEntityStorage S T] :
    HasEntityResource (withAuth authSlot) T := ⟨HasEntityStorage.storage⟩
instance {P T field} (authSlot : {T : Type} → EntityStorage S T → Type 1) [HasMemberStorage S P field T] :
    HasMemberResource (withAuth authSlot) P field T :=
  ⟨HasMemberStorage.storage (s := S) (Parent := P) (field := field) (Target := T)⟩
instance {P T member field V} (authSlot : {T : Type} → EntityStorage S T → Type 1)
    [EditableField T field V] (storage : (withAuth authSlot).member P member T)
    [source : HasProjectionResource (storageResources S) P T member storage field V] :
    HasProjectionResource (withAuth authSlot) P T member storage field V := ⟨source.witness⟩

def composedRequirements (authSlot : {T : Type} → EntityStorage S T → Type 1) :
    partyPage.Requirements (withAuth authSlot) :=
  partyPage.Requirements.infer (resources := withAuth authSlot)

#check ProjectionStorage
#check ProjectionStorage.getter_agrees
#check ProjectionStorage.project
#check HasFieldProjection
#synth HasFieldProjection S Person "name" Name
  (HasMemberStorage.storage (s := S) (Parent := Party) (field := "guests") (Target := Person)).target

#synth HasProjectionResource (storageResources S) Party Person "guests"
  (HasMemberStorage.storage (s := S) (Parent := Party) (field := "guests") (Target := Person)) "name" Name

run_cmd assertAxioms ``ProjectionStorage.getter_agrees
run_cmd assertAxioms ``instHasFieldProjectionSPersonNameStorage

abbrev TestM := ExceptT String (LeanDb.Read S)

private def checkedRead (plan : Except String (LeanDb.Read S A)) : TestM A :=
  match plan with | .error error => throw error | .ok read => liftM read

private def project {Scope A} : Projection Scope A (storageResources S) → TestM A
  | @ProjectionF.members _ _ _ _ _ _ relation _path selection => checkedRead (selection.project relation.parent)
  | .map plan f => f <$> project plan

private def queryAlgebra {Scope Error} (now : Instant) : Algebra TestM .query Scope Error (storageResources S) where
  request := fun req => match req with
    | .now => pure (.ok now)
    | @RequestF.find _ _ _ _ T _ storage ref => do return .ok (← checkedRead (storage.find ref))
    -- Milestone 2 query requests (not built by this milestone-1 domain).
    | @RequestF.findBy _ _ _ _ _ _ inst storage _ lookup key => do
        letI := inst
        match ← (liftM (storage.findBy lookup key) : TestM _) with
        | .ok row => return .ok row
        | .error fault => throw fault.code
    | @RequestF.select _ _ _ _ _ inst storage => do
        letI := inst
        match ← (liftM storage.select : TestM _) with
        | .ok rows => return .ok rows
        | .error fault => throw fault.code
    | @RequestF.linkField _ _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent => do
        return .ok (← checkedRead (link.project targets column parent))
  contains := fun relation person => checkedRead (relation.storage.contains relation.parent person)
  project := project

private def page (now : Instant) (viewer : Viewer Unit Person) (id : Ref Party) :
    LeanDb.Read S (Except String (Except partyPage.Error PartyPage)) :=
  (Flow.run (queryAlgebra now) (partyPage.flowWithResources requirements viewer ⟨id⟩)).run

private def pageBytes : Except String (Except partyPage.Error PartyPage) → String
  | .error error => "infrastructure:" ++ error
  | .ok (.error error) => "domain:" ++ reprStr error
  | .ok (.ok value) => (Wire.codec.encode value).compress

private def sameTable {T} [LeanDb.Entity T] [LeanDb.IsSchema.Has S T]
    (a b : LeanDb.DbState S) : Bool :=
  let left := a.get (α := T)
  let right := b.get (α := T)
  left.next == right.next && left.rows.length == right.rows.length &&
    (left.rows.zip right.rows).all (fun (x, y) =>
      x.id == y.id && LeanDb.Entity.encode x.val == LeanDb.Entity.encode y.val)

private def same (a b : LeanDb.DbState S) : Bool :=
  sameTable (T := Person) a b && sameTable (T := Party) a b && sameTable (T := Party.Guests) a b

private def verifyPage (plan : LeanDb.Read S (Except String (Except partyPage.Error PartyPage)))
    (expectedNames : Option (List Name)) : LeanDb.Db Unit := do
  let before ← LeanDb.DbState.load (s := S)
  let expected := LeanDb.Read.denote plan before
  let .ok actual ← LeanDb.Read.run plan | throw (.sqlite "Partiful page executor fault")
  unless pageBytes actual == pageBytes expected do throw (.sqlite "Partiful page denotation mismatch")
  let .ok (.ok value) := actual | throw (.sqlite "Partiful page unexpected failure")
  match expectedNames, value.guests with
  | none, .hidden =>
    -- A payload-free constructor is a bare string on the wire (decision 15).
    unless (Wire.codec.encode value.guests).compress == "\"hidden\"" do
      throw (.sqlite "hidden disclosure carries payload/count")
  | some names, .visible guests =>
    unless guests.map (·.name) == names do throw (.sqlite "Partiful names/target-ID order")
  | _, _ => throw (.sqlite "Partiful disclosure policy mismatch")
  let after ← LeanDb.DbState.load (s := S)
  unless before.checkWF && after.checkWF && same before after do
    throw (.sqlite "Partiful read changed complete state/counters or WF")

def main : IO Unit := do
  let .ok hostName := Name.parse "Host" | throw (IO.userError "host name")
  let .ok ada := Name.parse "Ada" | throw (IO.userError "Ada name")
  let .ok grace := Name.parse "Grace" | throw (IO.userError "Grace name")
  let .ok hostEmail := Email.parse "host@example.test" | throw (IO.userError "host email")
  let .ok adaEmail := Email.parse "ada@example.test" | throw (IO.userError "Ada email")
  let .ok graceEmail := Email.parse "grace@example.test" | throw (IO.userError "Grace email")
  let .ok title := Title.parse "Actual Partiful" | throw (IO.userError "title")
  let .ok description := Text.parse "Original domain, generated storage" | throw (IO.userError "description")
  let .ok now := Instant.ofEpochSeconds 100 | throw (IO.userError "now")
  let .ok future := Instant.ofEpochSeconds 1000 | throw (IO.userError "future")
  let nonce ← IO.monoNanosNow
  match ← LeanDb.withDb s!"/tmp/leandb-partiful-projection-{nonce}.sqlite" (LeanDb.IsSchema.specs S) do
    let host ← LeanDb.insert Person ⟨hostName, hostEmail⟩
    let adaRow ← LeanDb.insert Person ⟨ada, adaEmail⟩
    let graceRow ← LeanDb.insert Person ⟨grace, graceEmail⟩
    let .ok hostRef := idToRef host.id | throw (.sqlite "host ref")
    let .ok adaRef := idToRef adaRow.id | throw (.sqlite "Ada ref")
    let .ok graceRef := idToRef graceRow.id | throw (.sqlite "Grace ref")
    let party ← LeanDb.insert Party ⟨hostRef, title, future, description, .public, {}⟩
    let .ok partyRef := idToRef party.id | throw (.sqlite "party ref")
    let members := HasMemberStorage.storage (s := S) (Parent := Party) (field := "guests") (Target := Person)
    let includePerson (person : LeanDb.Stored Person) : LeanDb.Db Unit := do
      let .ok ref := idToRef person.id | throw (.sqlite "include ref")
      match ← LeanDb.Txn.run (s := S) (ε := String) (do
        let actor := Trusted.signedIn (Trusted.row ref person.val)
        let .ok plan := members.includeActor partyRef actor "partyMissing"
          | LeanDb.Txn.throw "include plan"
        plan.orAbort (fun _ => "include FK")) with
      | .ok (.ok ()) => pure ()
      | _ => throw (.sqlite "generated exact-set include failed")
    includePerson graceRow
    includePerson adaRow
    includePerson adaRow
    let anonymous : Viewer Unit Person := Trusted.viewer none
    let hostViewer : Viewer Unit Person := Trusted.viewer (some (Trusted.row hostRef host.val))
    let adaViewer : Viewer Unit Person := Trusted.viewer (some (Trusted.row adaRef adaRow.val))
    let graceViewer : Viewer Unit Person := Trusted.viewer (some (Trusted.row graceRef graceRow.val))
    verifyPage (page now anonymous partyRef) (some [ada, grace])
    verifyPage (page now hostViewer partyRef) (some [ada, grace])
    let setVisibility (visibility : GuestListVisibility) : LeanDb.Db Unit := do
      match ← LeanDb.Txn.run (s := S) (ε := String) (do
        let some current ← LeanDb.Txn.get Party party.id | LeanDb.Txn.throw "missing party"
        let updated := { current.val with visibility := visibility }
        let .ok checked := LeanDb.Entity.check Party updated | LeanDb.Txn.throw "invalid party"
        let _ ← (LeanDb.Txn.patch Party current (LeanDb.Fields.singleton Party.DbField.visibility) checked).orAbort
          (fun _ => "visibility patch")
        pure ()) with
      | .ok (.ok _) => pure ()
      | _ => throw (.sqlite "visibility evolution")
    setVisibility .attendees
    verifyPage (page now anonymous partyRef) none
    verifyPage (page now hostViewer partyRef) none
    verifyPage (page now adaViewer partyRef) (some [ada, grace])
    verifyPage (page now graceViewer partyRef) (some [ada, grace])
    includePerson host
    setVisibility .private
    for viewer in [anonymous, hostViewer, adaViewer, graceViewer] do
      verifyPage (page now viewer partyRef) none
    let .ok missing := Ref.parse (T := Party) "999" | throw (.sqlite "missing ref")
    let missingPlan := page now anonymous missing
    let before ← LeanDb.DbState.load (s := S)
    let .ok (.ok (.error .partyMissing)) ← LeanDb.Read.run missingPlan
      | throw (.sqlite "authored closed partyMissing error")
    unless pageBytes (LeanDb.Read.denote missingPlan before) == "domain:Partiful.partyPage.Error.partyMissing" do
      throw (.sqlite "missing page denotation")
    -- A malformed EMAIL proves projection never hydrates complete Person rows.
    -- This intentionally corrupts storage; no WF claim is made for this phase.
    setVisibility .public
    let _ ← LeanDb.untrackedSqlite fun db => db.exec "UPDATE person SET email = 'broken-' || id"
    let .ok (.ok (.ok namesOnly)) ← LeanDb.Read.run (page now anonymous partyRef)
      | throw (.sqlite "names projection hydrated invalid emails")
    match namesOnly.guests with
    | .visible guests => unless guests.map (·.name) == [hostName, ada, grace] do
        throw (.sqlite "names-only output after email corruption")
    | .hidden => throw (.sqlite "public list unexpectedly hidden")
    setVisibility .private
    let _ ← LeanDb.untrackedSqlite fun db => db.exec "DROP TABLE party_guests"
    let .ok (.ok (.ok hidden)) ← LeanDb.Read.run (page now hostViewer partyRef)
      | throw (.sqlite "denied authored flow prepared protected projection")
    match hidden.guests with | .hidden => pure () | .visible _ => throw (.sqlite "private host list exposed")
  with
  | .error error => throw (IO.userError error.message)
  | .ok () => IO.println "actual Partiful shared Flow projection: populated ordering/policies/denotation/WF/closed error/no email hydration/no denied query PASS"

end PartifulProjectionFixture

def main : IO Unit := PartifulProjectionFixture.main
