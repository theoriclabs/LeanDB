import PostPart1
import LeanDbDomain
import CheckAxioms

/- The Part 1 post's domain (LeanReact's `tests/domain/PostPart1.lean`, imported
unchanged) runs natively on SQLite. This fixture only supplies a TEST algebra for
the shared `Flow.run`, lowering each storage request to one LeanDB hook
(`EntityStorage.insert/update/delete/find/findBy/select`); the production algebra
is LeanAPI's. Every operation is compared with its pure meaning on the full state,
counters included. -/

open LeanApp.Domain LeanDb.Domain
open LeanDb (Txn Read DbState)

-- Decision 8 is the domain's own `constraint Rsvp.cancelWithParty : cascade party`;
-- `native_schema%` reads it. `Rsvp.guest` keeps RESTRICT.
native_schema% PostSchema := Person, Party, Rsvp, Credential

namespace PostRuntimeFixture

abbrev R := storageResources PostSchema

/-! ## Test-only operations over the post's generated storage steps -/

inductive TryRsvpError where
  | missing
  | started

/-- The post's `Rsvp.add` (the raw insert is `internal`), reporting the conflict
    value that `rsvp` swallows. -/
def tryRsvp (me : _root_.SignedIn) (party : Ref Party) : Op TryRsvpError String := do
  let some p ← Party.find party | throw .missing
  let now ← Clock.now
  let ⟨isOpen⟩ ← require (MayRsvp now p) .started
  match ← Rsvp.add p me now isOpen with
  | .ok _ => pure "inserted"
  | .error .onePerGuest => pure "onePerGuest"

/-- `T.update` with a touched-field conflict. -/
def changeEmail (person : Ref Person) (email : Email) : Op Empty String := do
  let some p ← Person.find person | pure "missing"
  match ← Person.update p { p.toPerson with email } with
  | .ok () => pure "updated"
  | .error .uniqueEmail => pure "uniqueEmail"

/-- Delete a person: restricted while their RSVPs exist. -/
def removePerson (person : Ref Person) : Op Empty Unit := do
  let some p ← Person.find person | pure ()
  Person.delete p

/-- `Person.findBy`, the single-field lookup sign-in uses. -/
def lookupEmail (email : Email) : ReadOp Empty (Option (Ref Person)) := do
  let some p ← Person.findBy email | pure none
  pure (some p.id)

/-- `T.select`. -/
def partyTitles : ReadOp Empty (List Title) := do
  return (← Party.select).map (·.title)

derive_operation tryRsvp
derive_operation changeEmail
derive_operation removePerson
derive_operation lookupEmail
derive_operation partyTitles

/-! ## Requirements resolve against the native family -/

def createRequirements : createPerson.Requirements R := createPerson.Requirements.infer
def hostRequirements : hostPartyAs.Requirements R := hostPartyAs.Requirements.infer
def rsvpRequirements : rsvpAs.Requirements R := rsvpAs.Requirements.infer
-- The instance pinned as missing in LeanReact's `NativePost.lean`:
def pageRequirements : getParty.Requirements R := getParty.Requirements.infer
def tryRsvpRequirements : tryRsvp.Requirements R := tryRsvp.Requirements.infer
def changeEmailRequirements : changeEmail.Requirements R := changeEmail.Requirements.infer
def editRequirements : edit.Requirements R := edit.Requirements.infer
def removeRequirements : removePerson.Requirements R := removePerson.Requirements.infer
def lookupRequirements : lookupEmail.Requirements R := lookupEmail.Requirements.infer
def titlesRequirements : partyTitles.Requirements R := partyTitles.Requirements.infer

#synth HasUniqueResource R Rsvp (Ref Party × Ref Person) HasEntityResource.witness Rsvp.onePerGuest.key
#synth HasUniqueResource R Person Email HasEntityResource.witness Person.uniqueEmail.key
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

/-! ## The test algebra -/

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

abbrev CommandM (E σ : Type) := Txn σ PostSchema (Failure E)

def commandRequest {σ E A : Type} (now : Instant) : RequestF R σ E .command A → CommandM E σ A
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
  -- Authentication steps are LeanAPI's (KDF under KDFGate); this test refuses them.
  | .hashPassword _ => Txn.throw (.unsupported "hashPassword")
  | @RequestF.verifyCredential _ _ _ _ _ _ _ _ _ _ _ => Txn.throw (.unsupported "verifyCredential")
  | @RequestF.startSession _ _ _ _ _ _ _ _ => Txn.throw (.unsupported "startSession")
  | _ => Txn.throw (.unsupported "milestone-1 request")

def commandAlgebra {σ E : Type} (now : Instant) : Algebra (CommandM E σ) .command σ E R where
  request := fun request => do return .ok (← commandRequest now request)
  contains := fun _ _ => Txn.throw (.unsupported "contains")
  project := fun _ => Txn.throw (.unsupported "project")

/-- One operation in one writer transaction; a domain error rolls back. -/
def runOp {E A : Type} (now : Instant) (flow : {σ : Type} → Flow .command σ E A R) :
    {σ : Type} → CommandM E σ A := do
  match ← Flow.run (commandAlgebra now) flow with
  | .ok value => pure value
  | .error error => Txn.throw (.domain error)

abbrev QueryM (E : Type) := ExceptT (Failure E) (Read PostSchema)

def queryRequest {E A : Type} (now : Instant) : RequestF R Unit E .query A → QueryM E A
  | .now => pure now
  | @RequestF.find _ _ _ _ _ inst storage reference =>
      letI := inst
      match storage.find reference with
      | .error why => throw (.storage (.invalidReference why))
      | .ok read => liftM read
  | @RequestF.findBy _ _ _ _ _ _ inst storage _ lookup key => do
      letI := inst
      match ← (liftM (storage.findBy lookup key) : QueryM E _) with
      | .ok row => pure row
      | .error fault => throw (.storage fault)
  | @RequestF.select _ _ _ _ _ inst storage => do
      letI := inst
      match ← (liftM storage.select : QueryM E _) with
      | .ok rows => pure rows
      | .error fault => throw (.storage fault)
  | @RequestF.linkField _ _ _ _ _ _ _ _ _ _ _ _ link targets _ column parent =>
      match link.project targets column parent with
      | .error why => throw (.storage (.invalidReference why))
      | .ok read => liftM read

def queryAlgebra {E : Type} (now : Instant) : Algebra (QueryM E) .query Unit E R where
  request := fun request => do return .ok (← queryRequest now request)
  contains := fun _ _ => throw (.unsupported "contains")
  project := fun _ => throw (.unsupported "project")

def runRead {E A : Type} (now : Instant) (flow : Flow .query Unit E A R) :
    Read PostSchema (Except (Failure E) (Except E A)) :=
  (Flow.run (queryAlgebra now) flow).run

/-! ## Full-state comparison with the pure meaning -/

def sameTable {T} [LeanDb.Entity T] [LeanDb.IsSchema.Has PostSchema T] (a b : DbState PostSchema) : Bool :=
  let left := a.get (α := T)
  let right := b.get (α := T)
  left.next == right.next && left.rows.length == right.rows.length &&
    (left.rows.zip right.rows).all fun (x, y) =>
      x.id == y.id && LeanDb.Entity.encode x.val == LeanDb.Entity.encode y.val

def same (a b : DbState PostSchema) : Bool :=
  sameTable (T := Person) a b && sameTable (T := Party) a b && sameTable (T := Rsvp) a b &&
    sameTable (T := Credential) a b

def fail (label : String) : LeanDb.Db α := throw (.sqlite s!"PostRuntime check failed: {label}")

def check (ok : Bool) (label : String) : LeanDb.Db Unit := unless ok do fail label

/-- Run a writer program natively; answer and every table/counter must equal the
    pure meaning. Returns the rendered answer. -/
def runProgram {E A : Type} [Ontology.Wire E] (render : A → String)
    (program : {σ : Type} → CommandM E σ A) (label : String) :
    LeanDb.Db (String × Except (Failure E) A) := do
  let before ← DbState.load (s := PostSchema)
  check before.checkWF (label ++ ": WF before")
  let expected := Txn.denote (program (σ := Unit)) before
  let show' : Except (Failure E) A → String
    | .ok value => "ok:" ++ render value
    | .error failure => failure.render
  match ← Txn.run program with
  | .error fault => fail s!"{label}: executor fault {fault}"
  | .ok actual =>
      let after ← DbState.load (s := PostSchema)
      check after.checkWF (label ++ ": WF after")
      check (show' actual == show' expected.1) s!"{label}: answer {show' actual} vs meaning {show' expected.1}"
      check (same after expected.2) (label ++ ": every table and counter equals the meaning")
      return (show' actual, actual)

/-- A published command, through the test algebra. -/
def command {E A : Type} [Ontology.Wire E] (now : Instant) (render : A → String)
    (flow : {σ : Type} → Flow .command σ E A R) (label : String) :
    LeanDb.Db (String × Except (Failure E) A) :=
  runProgram render (runOp now flow) label

def query {E A : Type} [Ontology.Wire E] (now : Instant) (render : A → String)
    (flow : Flow .query Unit E A R) (label : String) : LeanDb.Db (String × Option A) := do
  let program := runRead now flow
  let before ← DbState.load (s := PostSchema)
  let expected := Read.denote program before
  let show' : Except (Failure E) (Except E A) → String
    | .ok (.ok value) => "ok:" ++ render value
    | .ok (.error error) => "domain:" ++ (Ontology.Wire.codec.encode error).compress
    | .error failure => failure.render
  match ← Read.run program with
  | .error fault => fail s!"{label}: executor fault {fault}"
  | .ok actual =>
      check (show' actual == show' expected) s!"{label}: answer {show' actual} vs meaning {show' expected}"
      check (same before (← DbState.load (s := PostSchema))) (label ++ ": a read writes nothing")
      return (show' actual, match actual with | .ok (.ok value) => some value | _ => none)

def refKey {T} (ref : Ref T) : String := ref.key

def pageGuests : PartyPage → String
  | page => match page.guests with
    | .hidden => "hidden"
    | .visible guests => "visible " ++ toString (guests.map (·.name.value))

def parse {α} (label : String) (result : Ontology.Validation α) : IO α :=
  match result with
  | .ok value => pure value
  | .error _ => throw (IO.userError s!"fixture value {label}")

def main : IO Unit := do
  let nonce ← IO.monoNanosNow
  let path : System.FilePath := s!".lake/ddd-m2-scratch/leandb-post-runtime-{nonce}.sqlite"
  let names ← ["Asha", "Ben", "Cleo", "Dev"].mapM fun n => parse n (Name.parse n)
  let emails ← ["asha@example.test", "ben@example.test", "cleo@example.test", "dev@example.test"].mapM
    fun e => parse e (Email.parse e)
  let ashaCanonical ← parse "canonical" (Email.parse "Asha@Example.TEST")
  let titles ← ["Housewarming", "Picnic", "Dinner"].mapM fun t => parse t (Title.parse t)
  let text ← parse "text" (Text.parse "Bring a plant")
  let date ← parse "date" (Instant.ofEpochSeconds 5000)
  let now ← parse "now" (Instant.ofEpochSeconds 1000)
  let .ok (conn, _) ← LeanDb.Gate.openDb path (LeanDb.Gate.Target.ofSchema PostSchema) []
    | throw (IO.userError "open")
  let unit : Unit → String := fun _ => "()"
  let [ashaName, benName, cleoName, _] := names | throw (IO.userError "names")
  let [ashaEmail, benEmail, cleoEmail, _] := emails | throw (IO.userError "emails")
  match ← LeanDb.DbM.run conn (show LeanDb.Db Unit from do
    -- createPerson: four people, then the unique email conflict.
    let mut people : Array (Ref Person) := #[]
    for (name, email) in names.zip emails do
      let (reply, result) ← command now refKey
        (createPerson.flowWithResources createRequirements name email) "createPerson"
      check (reply == s!"ok:{people.size + 1}") s!"createPerson id: {reply}"
      let .ok person := result | fail "createPerson result"
      people := people.push person
    let #[asha, ben, cleo, dev] := people | fail "four people"
    let signed (person : Ref Person) (name : Name) (email : Email) : _root_.SignedIn :=
      Principal.trusted person { name, email }
    let before ← DbState.load (s := PostSchema)
    let (taken, _) ← command now refKey
      (createPerson.flowWithResources createRequirements ashaName ashaEmail) "createPerson duplicate"
    check (taken == "domain:\"emailTaken\"") s!"uniqueEmail → emailTaken: {taken}"
    let (canonical, _) ← command now refKey
      (createPerson.flowWithResources createRequirements ashaName ashaCanonical) "createPerson canonical"
    check (canonical == "domain:\"emailTaken\"") s!"canonical email collides: {canonical}"
    check (same before (← DbState.load (s := PostSchema))) "the email conflicts left every table and counter as before"
    -- Person.findBy (single-field unique) finds exactly the stored person.
    for (email, person) in emails.zip people.toList do
      let (reply, _) ← query now (fun r => match r with | some r => refKey r | none => "none")
        (lookupEmail.flowWithResources lookupRequirements email) "lookupEmail"
      check (reply == "ok:" ++ refKey person) s!"findBy email: {reply}"
    -- hostPartyAs: one party per visibility, all hosted by Asha.
    let mut parties : Array (Ref Party) := #[]
    for (title, visibility) in titles.zip [GuestListVisibility.everyone, .attendees, .hostOnly] do
      let (_, result) ← command now refKey
        (hostPartyAs.flowWithResources hostRequirements asha title text date visibility) "hostPartyAs"
      let .ok party := result | fail "hostPartyAs result"
      parties := parties.push party
    let (titlesReply, _) ← query now (fun ts => toString (ts.map (·.value)))
      (partyTitles.flowWithResources titlesRequirements) "Party.select"
    check (titlesReply == "ok:[Housewarming, Picnic, Dinner]") s!"select by id: {titlesReply}"
    let #[housewarming, picnic, dinner] := parties | fail "three parties"
    -- rsvpAs: Dev then Ben to every party (RSVP ids out of guest-id order).
    for party in parties do
      for guest in [dev, ben] do
        let (reply, _) ← command now unit (rsvpAs.flowWithResources rsvpRequirements guest party) "rsvpAs"
        check (reply == "ok:()") s!"rsvpAs: {reply}"
    let before ← DbState.load (s := PostSchema)
    let (again, _) ← command now unit (rsvpAs.flowWithResources rsvpRequirements ben picnic) "rsvpAs again"
    check (again == "ok:()") "a second yes is fine"
    let (conflict, _) ← command now id (tryRsvp.flowWithResources tryRsvpRequirements (signed ben benName benEmail) picnic) "Rsvp.add duplicate"
    check (conflict == "ok:onePerGuest") s!"duplicate (party, guest) is the typed conflict value: {conflict}"
    check (same before (← DbState.load (s := PostSchema))) "duplicate RSVPs left every table and counter as before"
    let missing ← parse "missing" (Ref.parse (T := Party) "999")
    let (notFound, _) ← command now unit (rsvpAs.flowWithResources rsvpRequirements ben missing) "rsvpAs missing"
    check (notFound == "domain:\"notFound\"") s!"missing party: {notFound}"
    -- getParty: the 3×3 visibility matrix (host, attendee, visitor) plus signed out.
    let viewers : List (String × Option _root_.SignedIn) :=
      [("host", some (signed asha ashaName ashaEmail)), ("attendee", some (signed ben benName benEmail)),
       ("visitor", some (signed cleo cleoName cleoEmail)), ("signed out", none)]
    let expected : List (List String) := [
      ["visible [Ben, Dev]", "visible [Ben, Dev]", "visible [Ben, Dev]", "visible [Ben, Dev]"],
      ["visible [Ben, Dev]", "visible [Ben, Dev]", "hidden", "hidden"],
      ["visible [Ben, Dev]", "hidden", "hidden", "hidden"]]
    for (party, row) in [housewarming, picnic, dinner].zip expected do
      for ((label, viewer), want) in viewers.zip row do
        let (reply, _) ← query now pageGuests
          (getParty.flowWithResources pageRequirements viewer party) s!"getParty {label}"
        check (reply == "ok:" ++ want) s!"getParty {label} on {refKey party}: {reply}, want {want}"
    -- The native join hook directly: the same names getParty answered above,
    -- by guest id although Dev's RSVP came first.
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
    let explain (sql : String) (binds : Array LeanDb.Col) : LeanDb.Db (List String) :=
      LeanDb.untrackedSqlite fun db => do
        let stmt ← db.prepare ("EXPLAIN QUERY PLAN " ++ sql)
        LeanDb.bindCols stmt 1 binds
        let mut details : Array String := #[]
        while ← stmt.step do details := details.push (← stmt.columnText 3)
        return details.toList
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
    -- edit: `Party.Changes` (no host, no date) through the update hook.
    let newTitle ← match Title.parse "Housewarming!" with
      | .ok t => pure t
      | .error _ => fail "title"
    let beforeEdit ← DbState.load (s := PostSchema)
    let (edited, _) ← command now unit (edit.flowWithResources editRequirements (signed asha ashaName ashaEmail)
      dinner { title := newTitle, description := text, guestList := .hostOnly }) "edit"
    check (edited == "ok:()") s!"edit: {edited}"
    let afterEdit ← DbState.load (s := PostSchema)
    let partyOf (st : DbState PostSchema) := (st.get (α := Party)).rows.find? (fun r => r.id.toInt64 == 3)
    match partyOf beforeEdit, partyOf afterEdit with
    | some old, some new =>
        check (new.val.title == newTitle && new.val.host == old.val.host && new.val.date == old.val.date)
          "edit wrote the title and kept host and date"
    | _, _ => fail "edited party"
    -- Credential: a PasswordHash column (TEXT) through the bridge codec; it round-trips.
    let credentialStorage := HasEntityStorage.storage (s := PostSchema) (T := Credential)
    check ((LeanDb.Entity.spec Credential).columns.any fun c => c.name == "hash" && c.sqlType == .text)
      "the hash is a TEXT column"
    let hashText := "scrypt$16384$8$1$c2FsdA$aGFzaA"
    let store : {σ : Type} → CommandM Empty σ (Except Empty (Ref Credential)) :=
      credentialStorage.insert { person := asha, hash := Trusted.passwordHash hashText }
        ([] : List (Constraint Empty)) .storage
    let (stored, _) ← runProgram (fun r => match r with | .ok r => refKey r | .error e => nomatch e) store
      "Credential insert"
    check (stored == "ok:1") s!"credential stored: {stored}"
    let .ok (.ok rows) ← Read.run (EntityStorage.select (Scope := Unit) credentialStorage) | fail "credential select"
    check (rows.map (fun r => Trusted.passwordHashText r.value.hash) == [hashText] &&
      rows.map (fun r => refKey r.value.person) == [refKey asha]) "the stored hash reads back exactly"
    -- update: only constraints over changed fields are checked; a clash is a value.
    let before ← DbState.load (s := PostSchema)
    let (clash, _) ← command now id
      (changeEmail.flowWithResources changeEmailRequirements ben ashaEmail) "Person.update clash"
    check (clash == "ok:uniqueEmail") s!"update to a taken email: {clash}"
    check (same before (← DbState.load (s := PostSchema))) "the clashing update wrote nothing"
    let fresh ← parse "fresh" (Email.parse "benjamin@example.test")
    let (updated, _) ← command now id
      (changeEmail.flowWithResources changeEmailRequirements ben fresh) "Person.update"
    check (updated == "ok:updated") s!"update to a free email: {updated}"
    -- delete: a guest with RSVPs is restricted; cancelling cascades only its RSVPs.
    let before ← DbState.load (s := PostSchema)
    let (restricted, _) ← command now unit
      (removePerson.flowWithResources removeRequirements ben) "Person.delete restricted"
    check (restricted == "storage:storage.restricted:rsvp.foreignKey.guest") s!"restrict: {restricted}"
    check (same before (← DbState.load (s := PostSchema))) "the restricted delete rolled back"
    -- `Party.delete` is `internal` to the domain module; the native hook it
    -- lowers to (`EntityStorage.delete`) cascades the party's RSVPs.
    let partyStorage := HasEntityStorage.storage (s := PostSchema) (T := Party)
    let cancel : {σ : Type} → CommandM Empty σ Unit := fun {σ} =>
      match partyStorage.find (Scope := σ) picnic with
      | .error why => Txn.throw (.storage (.invalidReference why))
      | .ok read => do
          let some row ← Txn.ofRead read | Txn.throw (.storage .gone)
          partyStorage.delete row .storage
    let (cancelled, _) ← runProgram unit cancel "EntityStorage.delete cascades"
    check (cancelled == "ok:()") s!"cancel: {cancelled}"
    let after ← DbState.load (s := PostSchema)
    check ((after.get (α := Rsvp)).rows.length == 4) "the cancelled party's two RSVPs went, four stay"
    check ((after.get (α := Party)).rows.length == 2 && (after.get (α := Person)).rows.length == 4)
      "other parties and every person stay"
    check ((after.get (α := Rsvp)).next == (before.get (α := Rsvp)).next) "RSVP counter unchanged"
    let (gone, _) ← query now pageGuests
      (getParty.flowWithResources pageRequirements (some (signed asha ashaName ashaEmail)) picnic) "getParty cancelled"
    check (gone == "domain:\"notFound\"") s!"cancelled party: {gone}"
    -- Denial prepares nothing: with the RSVP table gone, the denied join still
    -- answers `hidden`, and the allowed one fails (it really reads the table).
    let _ ← LeanDb.untrackedSqlite fun db => db.exec "DROP TABLE rsvp"
    let .ok denied := link.projectIf column housewarming False (some ·) none | fail "denied plan"
    match ← Read.run denied with
    | .ok none => pure ()
    | _ => fail "the denied join prepared protected SQL"
    let .ok allowed := link.projectIf column housewarming True (some ·) none | fail "allowed plan"
    match ← Read.run allowed with
    | .error _ => pure ()
    | .ok _ => fail "the allowed join did not read the RSVP table"
  ) with
  | .error e => throw (IO.userError e.message)
  | .ok () => IO.println "post runtime on SQLite: createPerson/hostPartyAs/rsvpAs/getParty, conflicts, update, cascade PASS"

end PostRuntimeFixture

def main : IO Unit := PostRuntimeFixture.main
