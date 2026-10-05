import LeanDb

/-! # DDD milestone 2, native half

Populated SQLite checks for the post's entity-based RSVP (`Rsvp` with a
composite unique and a cascading `party` reference, the typed semi-join
projection, unique-key lookups, field-excluding patches) and for the
migration gate (refusal, typed backfill, duplicate preflight, atomicity).
Every write is compared with its pure meaning on the full state, counters
included, as in `TestsDdd`.
-/

namespace TestsDddM2
open LeanDb

inductive GuestListVisibility where
  | everyone | attendees | hostOnly
  deriving Repr, BEq, DecidableEq, LeanDb.ClosedEnum

/-! ## The database as it was before `guestList` -/

namespace V1
structure Person where
  name : String
  email : String
  phone : String
  deriving Repr, BEq, LeanDb.Entity
unique% Person.uniqueEmail := email

structure Party where
  host : Ref Person
  title : String
  description : String
  date : Int64
  deriving Repr, BEq, LeanDb.Entity

structure Rsvp where
  party : Ref Party
  guest : Ref Person
  deriving Repr, BEq
cascade% Rsvp.party
deriving instance LeanDb.Entity for Rsvp
unique% Rsvp.onePerGuest := (party, guest)

schema% S := Person, Party, Rsvp
end V1

/-! ## The post's schema -/

structure Person where
  name : String
  email : String
  phone : String
  deriving Repr, BEq, LeanDb.Entity
unique% Person.uniqueEmail := email

structure Party where
  host : Ref Person
  title : String
  description : String
  date : Int64
  guestList : GuestListVisibility
  deriving Repr, BEq, LeanDb.Entity

structure Rsvp where
  party : Ref Party
  guest : Ref Person
  deriving Repr, BEq
-- Decision 8: the cascade is declared on the `Rsvp.party` reference.
cascade% Rsvp.party
deriving instance LeanDb.Entity for Rsvp
unique% Rsvp.onePerGuest := (party, guest)

schema% S := Person, Party, Rsvp

/-- Existing parties behaved as if everyone could see the guest list. -/
migration% addGuestList := Party.addField guestList (fill := .everyone)

/-! ## A later change: phones become unique (duplicate preflight) -/

namespace V3
structure Person where
  name : String
  email : String
  phone : String
  deriving Repr, BEq, LeanDb.Entity
unique% Person.uniqueEmail := email
unique% Person.uniquePhone := phone

structure Party where
  host : Ref Person
  title : String
  description : String
  date : Int64
  guestList : GuestListVisibility
  deriving Repr, BEq, LeanDb.Entity

structure Rsvp where
  party : Ref Party
  guest : Ref Person
  deriving Repr, BEq
cascade% Rsvp.party
deriving instance LeanDb.Entity for Rsvp
unique% Rsvp.onePerGuest := (party, guest)

schema% S := Person, Party, Rsvp

def canonicalEmail (raw : String) : Except String String :=
  if raw.contains '@' then .ok raw.toLower else .error "not an email address"

migration% emailsCanonical := Person.checkCanonical email canonicalEmail
end V3

/-! ## Atomicity: a write to `person`, a fill rewrite of `party`, then a
    unique index the data violates -/

namespace V4
structure Person where
  name : String
  email : String
  phone : String
  nickname : Option String
  deriving Repr, BEq, LeanDb.Entity
unique% Person.uniqueEmail := email

structure Party where
  host : Ref Person
  title : String
  description : String
  date : Int64
  guestList : GuestListVisibility
  deriving Repr, BEq, LeanDb.Entity
unique% Party.oneTitlePerHost := (host, title)

structure Rsvp where
  party : Ref Party
  guest : Ref Person
  deriving Repr, BEq
cascade% Rsvp.party
deriving instance LeanDb.Entity for Rsvp
unique% Rsvp.onePerGuest := (party, guest)

schema% S := Person, Party, Rsvp

migration% addGuestList := Party.addField guestList (fill := .everyone)
end V4

/-! ## The programmatic cascade hook

What `native_schema%` will call in wave 2 for a portable reference declared
`onDelete := cascade`: the same stored action as `cascade%`, idempotent. -/

structure Invite where
  party : Ref Party
  guest : Ref Person
  deriving Repr, BEq
run_cmd LeanDb.Derive.declareCascade ``Invite `party
run_cmd LeanDb.Derive.declareCascade ``Invite `party
deriving instance LeanDb.Entity for Invite

/-! ## The post's domain code, natively -/

inductive Role where
  | host | attendee | visitor
  deriving Repr, BEq, DecidableEq

def CanSeeGuests : GuestListVisibility → Role → Bool
  | .everyone,  _         => true
  | .attendees, .host     => true
  | .attendees, .attendee => true
  | .attendees, .visitor  => false
  | .hostOnly,  .host     => true
  | .hostOnly,  .attendee => false
  | .hostOnly,  .visitor  => false

/-- `Rsvp ⋈ Person`: the RSVP entity read as a link from a party to people. -/
def Party.guestLinks : LinkRelation Party Person Rsvp where
  parentField := Rsvp.Field.party
  targetField := Rsvp.Field.guest
  getParent := (·.party)
  getTarget := (·.guest)
  parentColumn := fun _ => rfl
  targetColumn := fun _ => rfl

/-- `Viewer.of`: the role comes from the session and the RSVP table, through
    the composite unique lookup. -/
def roleOf (viewer : Option (LeanDb.Id Person)) (row : Valid Party) : Read S Role := do
  match viewer with
  | none => return .visitor
  | some me =>
      if row.val.host == me then return .host
      match ← Read.findBy Rsvp Rsvp.Unique.onePerGuest (row.id, me) with
      | some _ => return .attendee
      | none => return .visitor

/-- The post's `Party.guests`: it cannot be called without the proof. -/
def Party.guests (row : Valid Party) (role : Role)
    (_h : CanSeeGuests row.val.guestList role = true) : Read S (List String) :=
  .linkField Party.guestLinks row.id Person.Field.name

/-- `getParty`'s guest list: `none` = no party, `some none` = hidden. -/
def guestList (party : LeanDb.Id Party) (viewer : Option (LeanDb.Id Person)) :
    Read S (Option (Option (List String))) := do
  let some row ← Read.get Party party | return none
  let role ← roleOf viewer row
  some <$> Read.discloseIf (CanSeeGuests row.val.guestList role = true)
    (Party.guests row role) some none

/-- The post's `rsvp`: a second yes is fine. -/
def rsvp (guest : LeanDb.Id Person) (party : LeanDb.Id Party) : {σ : Type} → Txn σ S String Unit := do
  let some _ ← Txn.get Party party | Txn.throw "notFound"
  let .ok row := Entity.check Rsvp ⟨party, guest⟩ | Txn.throw "invalid"
  match ← Txn.insertUnique row (fun (fk : Rsvp.ForeignKey) => s!"missingRef:{repr fk}") with
  | .ok _               => pure ()
  | .error .onePerGuest => pure ()  -- already going

/-- The raw insert, reporting the typed conflict. -/
def addRsvp (party : LeanDb.Id Party) (guest : LeanDb.Id Person) : {σ : Type} → Txn σ S String String := do
  let .ok row := Entity.check Rsvp ⟨party, guest⟩ | Txn.throw "invalid"
  match ← Txn.insertUnique row (fun (fk : Rsvp.ForeignKey) => s!"missingRef:{repr fk}") with
  | .ok current => return s!"inserted {current.id.toInt64}"
  | .error .onePerGuest => return "conflict onePerGuest"

/-- Cancelling a party cannot be restricted: its only inbound reference
    cascades, so `DeleteError S Party` has no inhabited `restricted`. -/
def cancel (party : LeanDb.Id Party) : {σ : Type} → Txn σ S String Unit := do
  match ← Txn.delete Party party with
  | .ok _ => pure ()
  | .error .gone => Txn.throw "gone"
  | .error (.restricted who _) => nomatch who

def removePerson (person : LeanDb.Id Person) : {σ : Type} → Txn σ S String String := do
  match ← Txn.delete Person person with
  | .ok _ => return "deleted"
  | .error .gone => Txn.throw "gone"
  | .error (.restricted who n) =>
      return s!"restricted {(ReferencedBy.metadata who.val).identity} {n}"

/-- The post's `Party.Changes`: what `edit` may change. No host, no date. -/
structure PartyChanges where
  title : String
  description : String
  guestList : GuestListVisibility

def editable : Fields Party :=
  Fields.of [Party.Field.title, Party.Field.description, Party.Field.guestList]

/-- An edit can only write the editable columns. Even a full row that carries
    another host and date writes neither; and the patch's failure type has no
    unique or reference alternative, because no editable field has one. -/
def edit (party : LeanDb.Id Party) (changes : PartyChanges) (smuggledHost : LeanDb.Id Person) :
    {σ : Type} → Txn σ S String Unit := do
  let some row ← Txn.get Party party | Txn.throw "notFound"
  let value := { row.val with
    title := changes.title, description := changes.description, guestList := changes.guestList
    host := smuggledHost, date := 0 }
  let .ok checked := Entity.check Party value | Txn.throw "invalid"
  match ← Txn.patch Party row editable checked with
  | .ok _ => pure ()
  | .error .gone => Txn.throw "gone"
  | .error (.invalid _) => Txn.throw "invalid"
  | .error (.duplicate touching _) => nomatch touching
  | .error (.missingRef within) => nomatch within

/-! Static facts the tests rely on. -/

example : ForeignKey.anyWithin (α := Party) editable = false := rfl
example : HasReferencedBy.anyRestrict (s := S) (α := Party) = false := rfl
example : HasReferencedBy.anyRestrict (s := S) (α := Person) = true := rfl
example (row : Valid Party) (role : Role) (h : ¬ CanSeeGuests row.val.guestList role = true) :
    Read.discloseIf (CanSeeGuests row.val.guestList role = true) (Party.guests row role)
      (some : List String → Option (List String)) none = .pure none :=
  Read.discloseIf_denied _ _ _ _ h

/-! ## Harness -/

private instance {ε α} [BEq ε] [BEq α] : BEq (Except ε α) := ⟨Harness.exceptEq (· == ·) (· == ·)⟩

private instance {α} [Entity α] [BEq α] : BEq (Valid α) := ⟨Harness.validEq⟩

private def check (b : Bool) (label : String) : DbM Unit :=
  unless b do throw (.sqlite s!"DDD M2 check failed: {label}")

private def checkIO (b : Bool) (label : String) : IO Unit :=
  unless b do throw (IO.userError s!"DDD M2 check failed: {label}")

private def stateEq (a b : DbState S) : Bool :=
  Harness.getEq (α := Person) a b && Harness.getEq (α := Party) a b && Harness.getEq (α := Rsvp) a b

private def v1Eq (a b : DbState V1.S) : Bool :=
  Harness.getEq (α := V1.Person) a b && Harness.getEq (α := V1.Party) a b &&
    Harness.getEq (α := V1.Rsvp) a b

private def compareTxn {α} [BEq α]
    (program : {σ : Type} → Txn σ S String α) (label : String) : DbM (Except String α) := do
  let before ← DbState.load (s := S)
  Harness.requireWF before (label ++ ":before")
  let expected := Txn.denote (program (σ := Unit)) before
  match ← Txn.run program with
  | .error fault => throw (.sqlite s!"{label}: unexpected fault {fault}")
  | .ok actual =>
      let after ← DbState.load (s := S)
      Harness.requireWF after (label ++ ":after")
      check (Harness.exceptEq (· == ·) (· == ·) actual expected.1) (label ++ ":result and failure payload")
      check (stateEq after expected.2) (label ++ ":all tables and counters")
      return actual

private def compareRead {α} [BEq α] (program : Read S α) (label : String) : DbM α := do
  let before ← DbState.load (s := S)
  Harness.requireWF before (label ++ ":before")
  let expected := Read.denote program before
  match ← Read.run program with
  | .error fault => throw (.sqlite s!"{label}: unexpected fault {fault}")
  | .ok actual =>
      check (actual == expected) (label ++ ":answer equals meaning")
      check (stateEq before (← DbState.load (s := S))) (label ++ ":no writes")
      return actual

private def explain (sql : String) (binds : Array Col) : DbM (List String) :=
  untrackedSqlite fun db => do
    let stmt ← db.prepare ("EXPLAIN QUERY PLAN " ++ sql)
    bindCols stmt 1 binds
    let mut details : Array String := #[]
    while ← stmt.step do details := details.push (← stmt.columnText 3)
    return details.toList

private def must {α} (label : String) (x : IO (Except DbError α)) : IO α := do
  match ← x with
  | .ok a => return a
  | .error e => throw (IO.userError s!"{label}: {e}")

private def scalar (conn : Conn) (sql : String) : IO Int64 := do
  let stmt ← conn.raw.prepare sql
  if ← stmt.step then stmt.columnInt64 0 else return 0

private def columnsOf (conn : Conn) (table : String) : IO (List String) := do
  let stmt ← conn.raw.prepare s!"PRAGMA table_info({quoteIdent table})"
  let mut out : Array String := #[]
  while ← stmt.step do out := out.push (← stmt.columnText 1)
  return out.toList

/-! ## B: the Rsvp entity on populated data -/

private def entityChecks (nonce : Nat) : IO Unit := do
  -- Composite unique: typed alternative and exact physical identity.
  let md := Unique.metadata (α := Rsvp) Rsvp.Unique.onePerGuest
  checkIO (Unique.identity (α := Rsvp) Rsvp.Unique.onePerGuest == "uq_rsvp_onePerGuest" &&
    md.identity == "uq_rsvp_onePerGuest" && md.table == "rsvp" &&
    md.columns == #["party", "guest"] && md.kind == .unique &&
    md.sourcePaths == ["TestsDddM2.Rsvp.party", "TestsDddM2.Rsvp.guest"])
    "composite unique keeps its typed alternative and physical identity"
  let spec := Entity.spec Rsvp
  checkIO (spec.indexes.any (fun i => i.unique && i.columns == #["party", "guest"] &&
    i.name == some "uq_rsvp_onePerGuest")) "composite unique index declared"
  checkIO (spec.columns[0]?.any (fun c => c.fkTable == some "party" && c.cascade) &&
    spec.columns[1]?.any (fun c => c.fkTable == some "person" && !c.cascade))
    "Rsvp.party cascades, Rsvp.guest restricts"
  let invite := Entity.spec Invite
  checkIO (invite.columns[0]?.any (fun c => c.fkTable == some "party" && c.cascade) &&
    invite.columns[1]?.any (fun c => c.fkTable == some "person" && !c.cascade))
    "Derive.declareCascade stores the same delete action as cascade%"
  let path : System.FilePath := s!"/tmp/leandb-ddd-m2-rsvp-{nonce}.sqlite"
  let (_, outcome) ← must "open fresh" (Gate.openDb path (Gate.Target.ofSchema S) [addGuestList])
  checkIO (outcome matches .fresh) "a fresh file is created, not migrated"
  let conn ← must "reopen" (openDb path (IsSchema.specs S))
  match ← DbM.run conn (show DbM Unit from do
    let host ← LeanDb.insert Person ⟨"Asha", "asha@example.test", "100"⟩
    let ada ← LeanDb.insert Person ⟨"Ada", "ada@example.test", "101"⟩
    let grace ← LeanDb.insert Person ⟨"Grace", "grace@example.test", "102"⟩
    let ben ← LeanDb.insert Person ⟨"Ben", "ben@example.test", "103"⟩
    let p1 ← LeanDb.insert Party ⟨host.id, "Housewarming", "Bring a plant", 2000, .attendees⟩
    let p2 ← LeanDb.insert Party ⟨host.id, "Picnic", "Bring food", 3000, .everyone⟩
    -- Insert in reverse id order; reads must still come back by guest id.
    check ((← compareTxn (addRsvp p1.id grace.id) "insert Grace") == .ok "inserted 1") "first RSVP"
    check ((← compareTxn (addRsvp p1.id ada.id) "insert Ada") == .ok "inserted 2") "second RSVP"
    let before ← DbState.load (s := S)
    check ((← compareTxn (addRsvp p1.id ada.id) "duplicate pair") == .ok "conflict onePerGuest")
      "duplicate (party, guest) returns the typed conflict"
    check (stateEq before (← DbState.load (s := S))) "duplicate leaves every table and counter unchanged"
    check ((← compareTxn (addRsvp p2.id ada.id) "distinct pair") == .ok "inserted 3") "distinct pairs insert"
    let before ← DbState.load (s := S)
    check ((← compareTxn (rsvp ada.id p1.id) "idempotent RSVP") == .ok ()) "second yes is fine"
    check (stateEq before (← DbState.load (s := S))) "RSVP retry changes nothing"
    check ((← compareTxn (rsvp ben.id ⟨999⟩) "missing party") == .error "notFound") "notFound"
    let missing ← compareTxn (addRsvp p1.id ⟨999⟩) "missing guest aborts"
    check (missing == .error "missingRef:TestsDddM2.Rsvp.ForeignKey.guest")
      "a missing reference is not a conflict: it aborts with the typed key"
    check (stateEq before (← DbState.load (s := S))) "aborted insert restores the state"
    let aborted ← compareTxn (do
      rsvp ben.id p1.id
      edit p1.id ⟨"changed", "changed", .everyone⟩ host.id
      (Txn.throw "injected" : Txn _ S String Unit)) "rollback after RSVP and edit"
    check (aborted == .error "injected") "abort payload"
    check (stateEq before (← DbState.load (s := S))) "full rollback"
    -- Unique-key lookups, single and composite: answer = meaning, and SQLite
    -- answers them from the unique index.
    let found ← compareRead (Read.findBy Person Person.Unique.uniqueEmail "ada@example.test") "findBy email"
    check (found.map (·.id) == some ada.id) "single-field findBy"
    check ((← compareRead (Read.findBy Person Person.Unique.uniqueEmail "nobody@example.test") "findBy none").isNone)
      "findBy absent"
    let pair ← compareRead (Read.findBy Rsvp Rsvp.Unique.onePerGuest (p1.id, ada.id)) "findBy pair"
    check (pair.map (·.val.guest) == some ada.id) "composite findBy"
    check ((← compareRead (Read.findBy Rsvp Rsvp.Unique.onePerGuest (p1.id, ben.id)) "findBy pair none").isNone)
      "composite findBy absent"
    let (emailSql, emailBinds) := Read.lookupSql (α := Person) Person.Unique.uniqueEmail "ada@example.test"
    let emailPlan ← explain emailSql emailBinds
    check (emailPlan.any (·.contains "INDEX uq_person_uniqueEmail (email=?)"))
      s!"email lookup uses its unique index: {emailPlan}"
    let (pairSql, pairBinds) := Read.lookupSql (α := Rsvp) Rsvp.Unique.onePerGuest (p1.id, ada.id)
    let pairPlan ← explain pairSql pairBinds
    check (pairPlan.any (·.contains "INDEX uq_rsvp_onePerGuest (party=? AND guest=?)"))
      s!"pair lookup uses the composite unique index: {pairPlan}"
    -- The typed semi-join: names only, by guest id, from the covering index.
    let names ← compareRead (.linkField Party.guestLinks p1.id Person.Field.name) "guest names"
    check (names == ["Ada", "Grace"]) "names ordered by guest id despite insertion order"
    let sql := Read.linkFieldSql Party.guestLinks Person.Field.name
    check (sql.startsWith "SELECT t.\"name\" FROM \"person\"") "SQL selects the name column alone"
    let plan ← explain sql #[.int p1.id.toInt64]
    check (plan.any (·.contains "COVERING INDEX uq_rsvp_onePerGuest (party=?)"))
      s!"RSVP side answered from the covering pair index: {plan}"
    check (plan.any (·.contains "INTEGER PRIMARY KEY")) s!"people fetched by id: {plan}"
    check (!(plan.any (·.startsWith "SCAN"))) s!"no table scan: {plan}"
    let (observedBefore, observed, observedAfter) ← Read.observe (s := S)
      (.linkField Party.guestLinks p1.id Person.Field.name)
    check (observed == names && stateEq observedBefore observedAfter && observedAfter.checkWF)
      "instrumented read observation"
    -- No email hydration: an unreadable email does not disturb the names.
    let _ ← untrackedSqlite fun db => db.exec s!"UPDATE person SET email = X'00' WHERE id = {grace.id.toInt64}"
    match ← Read.run (s := S) (.linkField Party.guestLinks p1.id Person.Field.name) with
    | .ok corruptNames => check (corruptNames == names) "names read without decoding emails"
    | .error fault => throw (.sqlite s!"name projection hydrated people: {fault}")
    match ← Read.run (s := S) (Read.get Person grace.id) with
    | .ok _ => throw (.sqlite "corruption fixture did not corrupt the email")
    | .error _ => pure ()
    let _ ← untrackedSqlite fun db =>
      db.exec s!"UPDATE person SET email = 'grace@example.test' WHERE id = {grace.id.toInt64}"
    -- The visibility matrix, decided before the projection.
    let visible := some (some names)
    let hidden : Option (Option (List String)) := some none
    check ((← compareRead (guestList p1.id none) "attendees, signed out") == hidden) "visitor hidden"
    check ((← compareRead (guestList p1.id (some ben.id)) "attendees, not going") == hidden) "non-attendee hidden"
    check ((← compareRead (guestList p1.id (some ada.id)) "attendees, going") == visible) "attendee sees"
    check ((← compareRead (guestList p1.id (some host.id)) "attendees, host") == visible) "host sees"
    check ((← compareRead (guestList p2.id none) "everyone") == some (some ["Ada"])) "everyone sees"
    check ((← compareRead (guestList ⟨999⟩ none) "no party") == none) "missing party"
    -- Party.Changes: title/description/guestList only.
    let before ← DbState.load (s := S)
    discard <| compareTxn (edit p1.id ⟨"Housewarming!", "Bring two plants", .hostOnly⟩ ben.id) "edit"
    let after ← DbState.load (s := S)
    let some edited := (after.get (α := Party)).rows.find? (·.id == p1.id) | throw (.sqlite "edited party")
    let some original := (before.get (α := Party)).rows.find? (·.id == p1.id) | throw (.sqlite "party")
    check (edited.val.host == original.val.host && edited.val.date == original.val.date &&
      edited.val.title == "Housewarming!" && edited.val.guestList == .hostOnly)
      "edit writes the editable fields and never host or date"
    check ((← compareRead (guestList p1.id (some ada.id)) "hostOnly, attendee") == hidden) "hostOnly hides attendees"
    check ((← compareRead (guestList p1.id (some host.id)) "hostOnly, host") == visible) "hostOnly shows host"
    -- References: a guest with RSVPs restricts; cancelling cascades.
    check ((← compareTxn (removePerson ada.id) "delete attendee") == .ok "restricted rsvp.foreignKey.guest 2")
      "a guest with RSVPs cannot be deleted; typed restricting key and count"
    discard <| compareTxn (cancel p1.id) "cancel cascades"
    let st ← DbState.load (s := S)
    check ((st.get (α := Rsvp)).rows.map (·.val.party) == [p2.id]) "only the cancelled party's RSVPs are gone"
    check ((st.get (α := Person)).rows.length == 4) "people stay"
    check ((st.get (α := Rsvp)).next == 4) "RSVP counter unchanged by the cascade"
    check ((← compareTxn (removePerson grace.id) "delete former guest") == .ok "deleted")
      "once the RSVPs cascaded, the person is free"
    -- Denial prepares nothing: with the RSVP table gone, a denied read still
    -- succeeds, and an allowed one fails (so the projection really reads it).
    discard <| compareTxn (edit p2.id ⟨"Picnic", "Bring food", .hostOnly⟩ host.id) "p2 hostOnly"
    let _ ← untrackedSqlite fun db => db.exec "DROP TABLE rsvp"
    match ← Read.run (guestList p2.id none) with
    | .ok result => check (result == hidden) "denied read with the table gone"
    | .error fault => throw (.sqlite s!"denied read prepared protected SQL: {fault}")
    match ← Read.run (guestList p2.id (some host.id)) with
    | .ok _ => throw (.sqlite "allowed read did not touch the RSVP table")
    | .error _ => pure ()
  ) with
  | .error e => throw (IO.userError e.message)
  | .ok () => IO.println "DDD M2: Rsvp entity, findBy, semi-join, Changes, cascade: passed"

/-! ## A: the migration gate -/

private def gateRefusalAndBackfill (nonce : Nat) : IO Unit := do
  let path : System.FilePath := s!"/tmp/leandb-ddd-m2-gate-{nonce}.sqlite"
  let target := Gate.Target.ofSchema S
  match ← withDb path (IsSchema.specs V1.S) do
    let asha ← LeanDb.insert V1.Person ⟨"Asha", "asha@example.test", "100"⟩
    let ben ← LeanDb.insert V1.Person ⟨"Ben", "ben@example.test", "101"⟩
    let p1 ← LeanDb.insert V1.Party ⟨asha.id, "Housewarming", "Bring a plant", 2000⟩
    let p2 ← LeanDb.insert V1.Party ⟨asha.id, "Picnic", "Bring food", 3000⟩
    let p3 ← LeanDb.insert V1.Party ⟨ben.id, "Gone", "Deleted before the change", 4000⟩
    let _ ← LeanDb.insert V1.Rsvp ⟨p1.id, ben.id⟩
    let _ ← LeanDb.insert V1.Rsvp ⟨p2.id, ben.id⟩
    LeanDb.delete (α := V1.Party) p3.id
  with
  | .error e => throw (IO.userError s!"seed: {e}")
  | .ok () => pure ()
  -- What happens today, without the gate: a fingerprint mismatch that names
  -- nothing (DbConns.open / app% serve surface exactly this).
  match ← openDb path (IsSchema.specs S) with
  | .error (.schemaMismatch _ _) => pure ()
  | other => throw (IO.userError s!"baseline open changed: {repr (other.toOption.isSome)}")
  let raw ← must "raw" (openDbRaw path)
  let before ← must "load V1" (DbM.run raw (DbState.load (s := V1.S)))
  let fpBefore ← readMeta raw.raw "schema_fingerprint"
  let journalBefore ← scalar raw "SELECT COUNT(*) FROM _leandb_migrations"
  -- 1. Refusal on the old database, naming Party.guestList.
  match ← must "check" (Gate.check raw target []) with
  | .refused [.missingFill "Party" "party" "guestList"] => pure ()
  | status => throw (IO.userError s!"expected exactly one missing fill:\n{status.render}")
  match ← Gate.openDb path target [] with
  | .error (.migrate message) =>
      checkIO (message.contains "Party.guestList" && message.contains "Nothing was changed")
        s!"refusal names Party.guestList: {message}"
  | .error e => throw (IO.userError s!"wrong refusal: {e}")
  | .ok _ => throw (IO.userError "opened a changed schema without a migration")
  checkIO ((← Gate.command? path target [] ["migrate", "--check"]) == some Gate.refusedExit)
    "migrate --check exits refused"
  checkIO ((← Gate.command? path target [] ["serve"]) == none) "other arguments are not migrate commands"
  let after ← must "reload V1" (DbM.run raw (DbState.load (s := V1.S)))
  checkIO (v1Eq before after && after.checkWF) "refusal changed no table or counter"
  checkIO ((← readMeta raw.raw "schema_fingerprint") == fpBefore) "refusal kept the fingerprint"
  checkIO ((← scalar raw "SELECT COUNT(*) FROM _leandb_migrations") == journalBefore) "refusal journaled nothing"
  -- 2. With the migration: check is pending, then the open backfills.
  checkIO ((← Gate.command? path target [addGuestList] ["migrate", "--check"]) == some 0)
    "migrate --check accepts a covered change"
  match ← must "pending" (Gate.check raw target [addGuestList]) with
  | .pending plan =>
      checkIO (plan.migrations == ["addGuestList"] &&
        plan.steps.any (·.contains "Party.guestList := 'everyone'")) s!"plan:\n{(Gate.Status.pending plan).render}"
  | status => throw (IO.userError s!"expected pending:\n{status.render}")
  let (conn, outcome) ← must "migrate" (Gate.openDb path target [addGuestList])
  match outcome with
  | .applied plan report =>
      checkIO (plan.fromVersion == 1 && report.toVersion == some 2) "version 1 → 2"
  | _ => throw (IO.userError "expected the migration to apply")
  let st ← must "load S" (DbM.run conn (DbState.load (s := S)))
  checkIO st.checkWF "migrated state is well formed"
  let parties := (st.get (α := Party)).rows
  let oldParties := (before.get (α := V1.Party)).rows
  checkIO (parties.length == oldParties.length &&
    (parties.zip oldParties).all fun (p, o) =>
      p.id.toInt64 == o.id.toInt64 && p.val.host.toInt64 == o.val.host.toInt64 &&
      p.val.title == o.val.title && p.val.description == o.val.description &&
      p.val.date == o.val.date && p.val.guestList == .everyone)
    "existing parties read back as .everyone with every other field kept"
  checkIO ((st.get (α := Party)).next == (before.get (α := V1.Party)).next &&
    (st.get (α := Party)).next == 4) "the AUTOINCREMENT counter survives the rewrite (deleted id 3 is not reused)"
  checkIO ((st.get (α := Person)).rows.map (·.val.email) ==
      (before.get (α := V1.Person)).rows.map (·.val.email) &&
    (st.get (α := Rsvp)).rows.map (fun r => (r.id.toInt64, r.val.party.toInt64, r.val.guest.toInt64)) ==
      (before.get (α := V1.Rsvp)).rows.map (fun r => (r.id.toInt64, r.val.party.toInt64, r.val.guest.toInt64)) &&
    (st.get (α := Person)).next == (before.get (α := V1.Person)).next &&
    (st.get (α := Rsvp)).next == (before.get (α := V1.Rsvp)).next) "people and RSVPs untouched"
  checkIO ((← Gate.appliedMigrations conn) == ["addGuestList"]) "applied migration recorded by name"
  checkIO ((← readMeta conn.raw "schema_fingerprint") == some (fingerprint (IsSchema.specs S)))
    "fingerprint is the compiled schema's"
  checkIO ((← scalar conn "SELECT COUNT(*) FROM _leandb_migrations") == journalBefore + 1) "one journal entry"
  checkIO ((← scalar conn "SELECT COUNT(*) FROM sqlite_master WHERE name = 'uq_person_uniqueEmail'") == 1)
    "indexes intact"
  checkIO ((← scalar conn "SELECT COUNT(*) FROM sqlite_master WHERE name IN \
('_leandb_fk_party_host', '_leandb_fk_rsvp_guest')") == 2)
    "foreign-key indexes exist after the party table was rewritten"
  match ← DbM.run conn (Txn.run (s := S) (ε := String) (do
      let .ok party := Entity.check Party ⟨⟨1⟩, "New", "After", 5000, .attendees⟩ | Txn.throw "invalid"
      match ← Txn.insertUnique party (fun _ => "missingRef") with
      | .ok row => return row.id.toInt64
      | .error ix => nomatch ix)) with
  | .ok (.ok (.ok 4)) => pure ()
  | _ => throw (IO.userError "the next party after the migration is not id 4")
  match ← must "reopen" (Gate.openDb path target [addGuestList]) with
  | (_, .upToDate) => pure ()
  | _ => throw (IO.userError "a migrated database is not up to date")
  checkIO ((← Gate.command? path target [addGuestList] ["migrate", "--check"]) == some 0) "check after"
  IO.println "DDD M2: gate refusal on an old database and typed backfill: passed"

private def duplicatePreflight (nonce : Nat) : IO Unit := do
  let path : System.FilePath := s!"/tmp/leandb-ddd-m2-unique-{nonce}.sqlite"
  let target := Gate.Target.ofSchema V3.S
  let migrations := [V3.emailsCanonical]
  match ← withDb path (IsSchema.specs S) do
    for (name, email, phone) in [("A", "a@x.test", "555"), ("B", "b@x.test", "777"),
        ("C", "c@x.test", "555"), ("D", "A@X.TEST", "999"), ("E", "e@x.test", "777"),
        ("F", "f@x.test", "777")] do
      discard <| LeanDb.insert Person ⟨name, email, phone⟩
  with
  | .error e => throw (IO.userError s!"seed: {e}")
  | .ok () => pure ()
  let raw ← must "raw" (openDbRaw path)
  let before ← must "load" (DbM.run raw (DbState.load (s := S)))
  match ← must "check" (Gate.check raw target migrations) with
  | .refused [.duplicates "Person" "person" "uq_person_uniquePhone" #["phone"] groups,
      .preflight "emailsCanonical" "Person.email" problems] =>
      checkIO (groups.map (·.rows) == [[1, 3], [2, 5, 6]] &&
        groups.map (·.key) == [[("phone", .text "555")], [("phone", .text "777")]])
        s!"every colliding row, grouped by key: {repr groups}"
      checkIO (problems == ["rows [1, 4] collide after canonicalization: \"a@x.test\", \"A@X.TEST\""])
        s!"canonicalization preflight: {problems}"
  | status => throw (IO.userError s!"expected duplicate and canonical refusals:\n{status.render}")
  match ← Gate.openDb path target migrations with
  | .error (.migrate message) =>
      checkIO (message.contains "rows 1, 3" && message.contains "rows 2, 5, 6" &&
        message.contains "No row is picked") s!"refusal lists the rows: {message}"
  | _ => throw (IO.userError "a duplicate unique constraint was applied")
  checkIO (stateEq before (← must "reload" (DbM.run raw (DbState.load (s := S))))) "nothing applied"
  checkIO ((← scalar raw "SELECT COUNT(*) FROM sqlite_master WHERE name = 'uq_person_uniquePhone'") == 0)
    "no index created"
  -- Resolve the data; the same declaration now applies.
  let _ ← raw.raw.exec "UPDATE person SET phone = '556' WHERE id = 3"
  let _ ← raw.raw.exec "UPDATE person SET phone = '778' WHERE id = 5"
  let _ ← raw.raw.exec "UPDATE person SET phone = '779' WHERE id = 6"
  let _ ← raw.raw.exec "UPDATE person SET email = 'd@x.test' WHERE id = 4"
  let (conn, outcome) ← must "apply" (Gate.openDb path target migrations)
  checkIO (outcome matches .applied ..) "applied after the data was resolved"
  checkIO ((← Gate.appliedMigrations conn) == ["emailsCanonical"]) "recorded"
  -- And the new constraint now reaches authored code as a typed conflict.
  match ← DbM.run conn (Txn.run (s := V3.S) (ε := String) (do
      let .ok person := Entity.check V3.Person ⟨"G", "g@x.test", "555"⟩ | Txn.throw "invalid"
      match ← Txn.insertUnique person (fun _ => "missingRef") with
      | .ok _ => return "inserted"
      | .error .uniqueEmail => return "uniqueEmail"
      | .error .uniquePhone => return "uniquePhone")) with
  | .ok (.ok (.ok "uniquePhone")) => pure ()
  | _ => throw (IO.userError "new unique does not produce its typed conflict")
  IO.println "DDD M2: duplicate preflight lists every row and applies nothing: passed"

private def atomicity (nonce : Nat) : IO Unit := do
  let path : System.FilePath := s!"/tmp/leandb-ddd-m2-atomic-{nonce}.sqlite"
  let target := Gate.Target.ofSchema V4.S
  match ← withDb path (IsSchema.specs V1.S) do
    let asha ← LeanDb.insert V1.Person ⟨"Asha", "asha@example.test", "100"⟩
    let _ ← LeanDb.insert V1.Party ⟨asha.id, "Dinner", "first", 2000⟩
    let _ ← LeanDb.insert V1.Party ⟨asha.id, "Brunch", "other", 2500⟩
    let _ ← LeanDb.insert V1.Party ⟨asha.id, "Dinner", "second", 3000⟩
  with
  | .error e => throw (IO.userError s!"seed: {e}")
  | .ok () => pure ()
  let raw ← must "raw" (openDbRaw path)
  let before ← must "load" (DbM.run raw (DbState.load (s := V1.S)))
  let fpBefore ← readMeta raw.raw "schema_fingerprint"
  let versionBefore ← readMeta raw.raw "schema_version"
  let journalBefore ← scalar raw "SELECT COUNT(*) FROM _leandb_migrations"
  match ← must "check" (Gate.check raw target [V4.addGuestList]) with
  | .refused [.duplicates "Party" "party" "uq_party_oneTitlePerHost" _ [group]] =>
      checkIO (group.rows == [1, 3]) "both parties named, no survivor"
  | status => throw (IO.userError s!"expected the (host, title) refusal:\n{status.render}")
  -- Without the preflight the plan runs: person gains a column, party is
  -- rewritten with the fill, then the unique index fails. All of it rolls back.
  match ← Gate.apply raw target [V4.addGuestList] { preflight := false } with
  | .error (.migrate message) =>
      checkIO (message.toLower.contains "unique constraint failed") s!"failed inside the migration: {message}"
  | .error e => throw (IO.userError s!"wrong failure: {e}")
  | .ok _ => throw (IO.userError "a violating unique index was applied")
  let after ← must "reload" (DbM.run raw (DbState.load (s := V1.S)))
  checkIO (v1Eq before after && after.checkWF) "every table and counter as before"
  checkIO (!(← columnsOf raw "person").contains "nickname") "the person column was rolled back"
  checkIO (!(← columnsOf raw "party").contains "guestList") "the party rewrite was rolled back"
  checkIO ((← scalar raw "SELECT COUNT(*) FROM sqlite_master WHERE name LIKE '\\_leandb\\_new\\_%' ESCAPE '\\'") == 0)
    "no scratch table left"
  checkIO ((← readMeta raw.raw "schema_fingerprint") == fpBefore &&
    (← readMeta raw.raw "schema_version") == versionBefore) "fingerprint and version unchanged"
  checkIO ((← scalar raw "SELECT COUNT(*) FROM _leandb_migrations") == journalBefore) "no journal entry"
  checkIO ((← Gate.appliedMigrations raw).isEmpty) "no migration recorded"
  -- The original schema still opens.
  discard <| must "V1 still opens" (openDb path (IsSchema.specs V1.S))
  IO.println "DDD M2: atomic apply rolls back every step on failure: passed"

/-! ## Foreign-key access paths (wave 1.5) -/

private def planUses (plan : List String) (index column : String) : Bool :=
  plan.any (·.contains s!"INDEX {index} ({column}=?)") && !(plan.any (·.startsWith "SCAN"))

private def fkIndexChecks (nonce : Nat) : IO Unit := do
  -- Exactly the reference columns that no declared index leads get one.
  let rsvpDdl := (Entity.spec Rsvp).fkIndexDdl
  checkIO (rsvpDdl == #["CREATE INDEX IF NOT EXISTS \"_leandb_fk_rsvp_guest\" ON \"rsvp\" (\"guest\")"])
    s!"Rsvp.guest gets an index; Rsvp.party is led by the pair index: {rsvpDdl}"
  checkIO ((Entity.spec Party).fkIndexDdl.size == 1 && (Entity.spec Person).fkIndexDdl.isEmpty)
    "Party.host gets one; Person has no references"
  checkIO (!(fingerprint (IsSchema.specs S)).isEmpty &&
    (IsSchema.specs S).all (fun t => !(t.fullDdl.contains "_leandb_fk_")))
    "engine indexes are not part of the declared schema or fingerprint"
  let path : System.FilePath := s!"/tmp/leandb-ddd-m2-fk-{nonce}.sqlite"
  let target := Gate.Target.ofSchema S
  let (conn, _) ← must "open" (Gate.openDb path target [addGuestList])
  match ← DbM.run conn (show DbM Unit from do
    let host ← LeanDb.insert Person ⟨"Asha", "asha@example.test", "100"⟩
    let ada ← LeanDb.insert Person ⟨"Ada", "ada@example.test", "101"⟩
    let grace ← LeanDb.insert Person ⟨"Grace", "grace@example.test", "102"⟩
    let p1 ← LeanDb.insert Party ⟨host.id, "Housewarming", "Bring a plant", 2000, .attendees⟩
    let p2 ← LeanDb.insert Party ⟨host.id, "Picnic", "Bring food", 3000, .everyone⟩
    for (p, g) in [(p1.id, ada.id), (p1.id, grace.id), (p2.id, ada.id)] do
      discard <| compareTxn (addRsvp p g) "seed RSVP"
    -- Deleting a person: every restrict count (and SQLite's own RESTRICT
    -- check, which looks up the same key) searches the key's index.
    for r in ReferencedBy.all S Person do
      let plan ← explain (ReferencedBy.countSql r) #[.int ada.id.toInt64]
      let index := TableSpec.fkIndexName (ReferencedBy.sourceName r) (ReferencedBy.columnName r)
      check (planUses plan index (ReferencedBy.columnName r))
        s!"restrict count on {ReferencedBy.sourceName r}.{ReferencedBy.columnName r}: {plan}"
    check ((← compareTxn (removePerson ada.id) "delete a guest") == .ok "restricted rsvp.foreignKey.guest 2")
      "the indexed count still restricts with the exact count"
    -- Cancelling a party: the cascade deletes RSVPs by `party`, which the
    -- composite unique index leads.
    for r in ReferencedBy.all S Party do
      check (ReferencedBy.cascade r) "Party's only inbound key cascades"
      let plan ← explain (ReferencedBy.cascadeSql r) #[.int p1.id.toInt64]
      check (planUses plan "uq_rsvp_onePerGuest" "party") s!"cascade delete plan: {plan}"
    discard <| compareTxn (cancel p1.id) "cancel cascades through the index"
    check (((← DbState.load (s := S)).get (α := Rsvp)).rows.length == 1) "only p1's RSVPs went"
    -- An existing database made before these indexes: no migration, no
    -- finding; the next open adds the index.
    let _ ← untrackedSqlite fun db => db.exec "DROP INDEX \"_leandb_fk_rsvp_guest\""
    let r := (ReferencedBy.all S Person).toList.find? (ReferencedBy.columnName · == "guest")
    let some guestKey := r | throw (.sqlite "rsvp.guest inbound key")
    let scan ← explain (ReferencedBy.countSql guestKey) #[.int ada.id.toInt64]
    check (scan.any (·.startsWith "SCAN")) s!"without the index the count scans: {scan}"
    let before ← DbState.load (s := S)
    match ← Gate.check conn target [addGuestList] with
    | .ok .upToDate => pure ()
    | .ok status => throw (.sqlite s!"a missing access path is not schema drift:\n{status.render}")
    | .error e => throw e
    -- Ask the reopened connection: an EXPLAIN program does not re-check the
    -- schema cookie, so this connection's cached schema would show a scan.
    let fresh ← match ← Gate.openDb path target [addGuestList] with
      | .ok (fresh, .upToDate) => pure fresh
      | _ => throw (.sqlite "reopen with a missing FK index")
    let restored ← match ← DbM.run fresh (explain (ReferencedBy.countSql guestKey) #[.int ada.id.toInt64]) with
      | .ok plan => pure plan
      | .error e => throw e
    check (planUses restored "_leandb_fk_rsvp_guest" "guest") s!"the open recreated the index: {restored}"
    check (stateEq before (← DbState.load (s := S))) "creating the index changed no row or counter"
  ) with
  | .error e => throw (IO.userError e.message)
  | .ok () => IO.println "DDD M2: foreign-key indexes, restrict and cascade plans, existing databases: passed"

def run : IO Unit := do
  let nonce ← IO.monoNanosNow
  entityChecks nonce
  fkIndexChecks nonce
  gateRefusalAndBackfill nonce
  duplicatePreflight nonce
  atomicity nonce

end TestsDddM2
