/- The post's data model on both backends: every step in memory and on SQLite (same answers,
   same tables), then the native-only properties: the declared evidence, the SQL and query
   plans of the join and of the composite lookup, and that a denied disclosure prepares no
   statement. Ported from the bridge's `PostRuntime` fixture. -/
import TestsModel.Post
import TestsModel.Twin
import CheckAxioms
open LeanDb.Model

native_schema% PostSchema := Person, Party, Rsvp

namespace PostRun
open TestsModel
open LeanDb (Read DbState)
open LeanDb.Native (storageResources HasLinkStorage HasFieldStorage HasUniqueStorage HasEntityStorage refToId)

abbrev R := storageResources PostSchema

/-! ## Test programs over the post's generated storage steps -/

/-- `Rsvp.add`, reporting the conflict value that `rsvp` swallows. -/
def tryRsvp (me : Ref Person) (now : Time) (party : Ref Party) : DB String := do
  let some p ← Party.find party | return "missing"
  if isOpen : MayRsvp now p then
    match ← Rsvp.add p me now isOpen with
    | .ok _ => return "inserted"
    | .error .onePerGuest => return "onePerGuest"
  else return "started"

/-- `T.update` with a touched-field conflict. -/
def changeEmail (person : Ref Person) (email : Email) : DB String := do
  let some p ← Person.find person | return "missing"
  match ← Person.update p { p.toPerson with email } with
  | .ok () => return "updated"
  | .error .uniqueEmail => return "uniqueEmail"

/-- Delete a person: restricted while their RSVPs exist. -/
def removePerson (person : Ref Person) : DB Unit := do
  let some p ← Person.find person | return ()
  Person.delete p

def partyTitles : Query (List String) := do
  return (← Party.select).map (·.title.value)

derive_requirements tryRsvp, changeEmail, removePerson, partyTitles

/-! ## Evidence: declared, and only declared -/

example : HasUniqueResource R Rsvp (Ref Party × Ref Person) HasEntityResource.witness Rsvp.onePerGuest.key :=
  inferInstance
example : HasUniqueResource R Person Email HasEntityResource.witness Person.uniqueEmail.key := inferInstance
#guard (HasEntityStorage.storage (s := PostSchema) (T := Rsvp)).sourceUnique Rsvp.Unique.onePerGuest ==
  "Rsvp.onePerGuest"
#guard (HasEntityStorage.storage (s := PostSchema) (T := Person)).sourceUnique Person.Unique.uniqueEmail ==
  "Person.uniqueEmail"
-- Links are explicit: only the declared `link Rsvp.party Rsvp.guest` has evidence.
open Lean Elab Command Meta in
run_cmd liftTermElabM do
  let declared ← Term.elabType (← `(HasLinkStorage PostSchema Rsvp "party" "guest" Party Person))
  let reverse ← Term.elabType (← `(HasLinkStorage PostSchema Rsvp "guest" "party" Person Party))
  unless (← synthInstance? declared).isSome do throwError "declared link has no evidence"
  if (← synthInstance? reverse).isSome then throwError "an undeclared link has evidence"
run_cmd assertAxioms ``Rsvp.onePerGuest.nativeKeyAgreement
run_cmd assertAxioms ``Person.uniqueEmail.nativeKeyAgreement

def tables : List (Table PostSchema) := [.of PostSchema Person, .of PostSchema Party, .of PostSchema Rsvp]

def key {T} (ref : Ref T) : String := ref.key
def unit : Unit → String := fun _ => "()"
def result (render : α → String) : Except PostError α → String
  | .ok value => "ok:" ++ render value
  | .error error => "error:" ++ reprStr error
def pageGuests (page : PartyPage) : String :=
  match page.guests with
  | .hidden => "hidden"
  | .visible guests => "visible " ++ toString (guests.map (·.name.value))

def explain (sql : String) (binds : Array LeanDb.Col) : LeanDb.Db (List String) :=
  LeanDb.untrackedSqlite fun db => do
    let stmt ← db.prepare ("EXPLAIN QUERY PLAN " ++ sql)
    LeanDb.bindCols stmt 1 binds
    let mut details : Array String := #[]
    while ← stmt.step do details := details.push (← stmt.columnText 3)
    return details.toList

def run : IO Unit := do
  let names ← ["Asha", "Ben", "Cleo", "Dev"].mapM fun n => parse n (Name.parse n)
  let emails ← ["asha@example.test", "ben@example.test", "cleo@example.test", "dev@example.test"].mapM
    fun e => parse e (Email.parse e)
  let ashaCanonical ← parse "canonical" (Email.parse "Asha@Example.TEST")
  let titles ← ["Housewarming", "Picnic", "Dinner"].mapM fun t => parse t (Title.parse t)
  let text ← parse "text" (Text.parse "Bring a plant")
  let date ← parse "date" (Instant.ofEpochSeconds 5000)
  let now ← parse "now" (Instant.ofEpochSeconds 1000)
  let later ← parse "later" (Instant.ofEpochSeconds 6000)
  let fresh ← parse "fresh" (Email.parse "benjamin@example.test")
  let newTitle ← parse "title" (Title.parse "Housewarming!")
  let [ashaName, _, _, _] := names | throw (IO.userError "names")
  let [housewarmingTitle, _, _] := titles | throw (IO.userError "titles")
  let [ashaEmail, _, _, _] := emails | throw (IO.userError "emails")
  scenario PostSchema "post" do
    let step := fun {α} (label : String) (render : α → String) (portable : DB α)
        (native : {σ : Type} → Program R .command σ α) => command tables label render portable native
    let read := fun {α} (label : String) (render : α → String) (portable : Query α)
        (native : Program R .query Unit α) => query tables label render portable native
    -- createPerson: four people, then the unique email conflict (also in canonical form).
    let mut people : Array (Ref Person) := #[]
    for (name, email) in names.zip emails do
      let reply ← step "createPerson" (result key) (createPerson name email)
        (createPerson.withResources createPerson.Requirements.infer name email)
      check (reply == s!"ok:{people.size + 1}") s!"createPerson id: {reply}"
      people := people.push (← match Ontology.Ref.parse (T := Person) (toString (people.size + 1)) with
        | .ok r => pure r | .error _ => fail "ref")
    let #[asha, ben, cleo, dev] := people | fail "four people"
    for email in [ashaEmail, ashaCanonical] do
      let taken ← step "createPerson duplicate" (result key) (createPerson ashaName email)
        (createPerson.withResources createPerson.Requirements.infer ashaName email)
      check (taken == "error:PostError.emailTaken") s!"uniqueEmail → emailTaken: {taken}"
    -- Person.findBy finds exactly the stored person.
    for (email, person) in emails.zip people.toList do
      let reply ← read "personByEmail" (fun r => (r.map key).getD "none") (personByEmail email)
        (personByEmail.withResources personByEmail.Requirements.infer email)
      check (reply == key person) s!"findBy email: {reply}"
    -- hostParty: one party per visibility, all hosted by Asha; a past date is refused.
    let past := step "hostParty past" (result key) (hostParty asha later housewarmingTitle text date .everyone)
      (hostParty.withResources hostParty.Requirements.infer asha later housewarmingTitle text date .everyone)
    check ((← past) == "error:PostError.dateInPast") "a party in the past is refused"
    let mut parties : Array (Ref Party) := #[]
    for (title, visibility) in titles.zip [GuestListVisibility.everyone, .attendees, .hostOnly] do
      let reply ← step "hostParty" (result key) (hostParty asha now title text date visibility)
        (hostParty.withResources hostParty.Requirements.infer asha now title text date visibility)
      check (reply == s!"ok:{parties.size + 1}") s!"hostParty: {reply}"
      parties := parties.push (← match Ontology.Ref.parse (T := Party) (toString (parties.size + 1)) with
        | .ok r => pure r | .error _ => fail "ref")
    let titlesReply ← read "Party.select" toString partyTitles (partyTitles.withResources partyTitles.Requirements.infer)
    check (titlesReply == "[Housewarming, Picnic, Dinner]") s!"select by id: {titlesReply}"
    let #[housewarming, picnic, dinner] := parties | fail "three parties"
    -- rsvp: Dev then Ben to every party (RSVP ids out of guest-id order).
    for party in parties do
      for guest in [dev, ben] do
        let reply ← step "rsvp" (result unit) (rsvp guest now party) (rsvp.withResources rsvp.Requirements.infer guest now party)
        check (reply == "ok:()") s!"rsvp: {reply}"
    let again ← step "rsvp again" (result unit) (rsvp ben now picnic) (rsvp.withResources rsvp.Requirements.infer ben now picnic)
    check (again == "ok:()") "a second yes is fine"
    let conflict ← step "Rsvp.add duplicate" id (tryRsvp ben now picnic)
      (tryRsvp.withResources tryRsvp.Requirements.infer ben now picnic)
    check (conflict == "onePerGuest") s!"duplicate (party, guest) is the typed conflict value: {conflict}"
    let started ← step "rsvp started" (result unit) (rsvp cleo later picnic)
      (rsvp.withResources rsvp.Requirements.infer cleo later picnic)
    check (started == "error:PostError.alreadyStarted") s!"rsvp after the start: {started}"
    let missing ← match Ontology.Ref.parse (T := Party) "999" with | .ok r => pure r | .error _ => fail "ref"
    let notFound ← step "rsvp missing" (result unit) (rsvp ben now missing) (rsvp.withResources rsvp.Requirements.infer ben now missing)
    check (notFound == "error:PostError.notFound") s!"missing party: {notFound}"
    -- getParty: the 3×3 visibility matrix (host, attendee, visitor) plus signed out.
    let viewers : List (String × Option (Ref Person)) :=
      [("host", some asha), ("attendee", some ben), ("visitor", some cleo), ("signed out", none)]
    let expected : List (List String) := [
      ["visible [Ben, Dev]", "visible [Ben, Dev]", "visible [Ben, Dev]", "visible [Ben, Dev]"],
      ["visible [Ben, Dev]", "visible [Ben, Dev]", "hidden", "hidden"],
      ["visible [Ben, Dev]", "hidden", "hidden", "hidden"]]
    for (party, row) in [housewarming, picnic, dinner].zip expected do
      for ((label, viewer), want) in viewers.zip row do
        let reply ← read s!"getParty {label}" (result pageGuests) (getParty viewer party)
          (getParty.withResources getParty.Requirements.infer viewer party)
        check (reply == "ok:" ++ want) s!"getParty {label} on {key party}: {reply}, want {want}"
    -- The native join directly: the same names, by guest id although Dev's RSVP came first.
    let link := HasLinkStorage.storage (s := PostSchema) (Edge := Rsvp) (parentField := "party")
      (targetField := "guest")
    let column := HasFieldStorage.storage (s := PostSchema) (T := Person) (field := "name") (Value := Name)
    let .ok plan := link.project column housewarming | fail "link plan"
    let state ← DbState.load (s := PostSchema)
    let .ok joined ← Read.run plan | fail "linkField executor fault"
    check (joined == Read.denote plan state && joined.map (·.value) == ["Ben", "Dev"])
      s!"join names by guest id: {joined.map (·.value)}"
    let joinSql := @Read.linkFieldSql _ _ _ link.parent.entity link.target.entity link.edge.entity
      link.relation column.field
    check (joinSql.startsWith "SELECT t.\"name\" FROM \"person\"") "the join selects the name column alone"
    let partyId ← match refToId housewarming with
      | .ok id => pure id
      | .error why => fail why
    let joinPlan ← explain joinSql #[.int partyId.toInt64]
    check (joinPlan.any (·.contains "COVERING INDEX uq_rsvp_onePerGuest (party=?)") &&
      !(joinPlan.any (·.startsWith "SCAN"))) s!"join plan: {joinPlan}"
    let lookup := (HasUniqueStorage.lookup (s := PostSchema) (T := Rsvp) (key := Rsvp.onePerGuest.key))
    let (pairSql, pairBinds) := @Read.lookupSql Rsvp (HasEntityStorage.storage (s := PostSchema) (T := Rsvp)).entity
      (HasEntityStorage.storage (s := PostSchema) (T := Rsvp)).unique lookup.index (lookup.encode (housewarming, ben))
    let pairPlan ← explain pairSql pairBinds
    check (pairPlan.any (·.contains "INDEX uq_rsvp_onePerGuest (party=? AND guest=?)"))
      s!"Rsvp.findBy probes the composite unique index: {pairPlan}"
    -- edit: `Party.Changes` (no host, no date), only by the host.
    let changes : Party.Changes := { title := newTitle, description := text, guestList := .hostOnly }
    let refused ← step "edit by a guest" (result unit) (edit ben dinner changes) (edit.withResources edit.Requirements.infer ben dinner changes)
    check (refused == "error:PostError.notHost") s!"edit by a guest: {refused}"
    let edited ← step "edit" (result unit) (edit asha dinner changes) (edit.withResources edit.Requirements.infer asha dinner changes)
    check (edited == "ok:()") s!"edit: {edited}"
    -- reschedule: the raw `Party.update` behind a rule with two proofs.
    let moved ← step "reschedule" (result unit) (reschedule asha now dinner later)
      (reschedule.withResources reschedule.Requirements.infer asha now dinner later)
    check (moved == "ok:()") s!"reschedule: {moved}"
    let tooLate ← step "reschedule started" (result unit) (reschedule asha later dinner later)
      (reschedule.withResources reschedule.Requirements.infer asha later dinner later)
    check (tooLate == "error:PostError.alreadyStarted") s!"reschedule after the start: {tooLate}"
    -- update: only constraints over changed fields are checked; a clash is a value.
    let clash ← step "Person.update clash" id (changeEmail ben ashaEmail)
      (changeEmail.withResources changeEmail.Requirements.infer ben ashaEmail)
    check (clash == "uniqueEmail") s!"update to a taken email: {clash}"
    let updated ← step "Person.update" id (changeEmail ben fresh) (changeEmail.withResources changeEmail.Requirements.infer ben fresh)
    check (updated == "updated") s!"update to a free email: {updated}"
    -- delete: a guest with RSVPs is restricted; cancelling cascades only its RSVPs.
    let restricted ← step "Person.delete restricted" unit (removePerson ben)
      (removePerson.withResources removePerson.Requirements.infer ben)
    check (restricted == "fault:storage.restricted") s!"restrict: {restricted}"
    let notHost ← step "cancel by a guest" (result unit) (cancel ben picnic) (cancel.withResources cancel.Requirements.infer ben picnic)
    check (notHost == "error:PostError.notHost") s!"cancel by a guest: {notHost}"
    let cancelled ← step "cancel" (result unit) (cancel asha picnic) (cancel.withResources cancel.Requirements.infer asha picnic)
    check (cancelled == "ok:()") s!"cancel: {cancelled}"
    let count ← read "RSVPs" toString rsvpCount (rsvpCount.withResources rsvpCount.Requirements.infer)
    check (count == "4") s!"the cancelled party's two RSVPs went, four stay: {count}"
    let gone ← read "getParty cancelled" (result pageGuests) (getParty (some asha) picnic)
      (getParty.withResources getParty.Requirements.infer (some asha) picnic)
    check (gone == "error:PostError.notFound") s!"cancelled party: {gone}"
    -- Denial prepares nothing: with the RSVP table gone, the denied join still answers
    -- `hidden`, and the allowed one fails (it really reads the table).
    let _ ← LeanDb.untrackedSqlite fun db => db.exec "DROP TABLE rsvp"
    let .ok denied := link.projectIf column housewarming False (some ·) none | fail "denied plan"
    match ← Read.run denied with
    | .ok none => pure ()
    | _ => fail "the denied join prepared protected SQL"
    let .ok allowed := link.projectIf column housewarming True (some ·) none | fail "allowed plan"
    match ← Read.run allowed with
    | .error _ => pure ()
    | .ok _ => fail "the allowed join did not read the RSVP table"
  IO.println "post on memory and SQLite: people, parties, RSVPs, visibility, join plans, Changes, update, restrict, cascade PASS"

end PostRun
