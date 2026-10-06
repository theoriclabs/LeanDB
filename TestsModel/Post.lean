/- The Part 1 post's data model: its entities, declarations, rules and the storage steps the
   rules allow, on `LeanDb.Model` alone (no operation layer: who is signed in and what time it
   is arrive as plain arguments here). Ported from LeanReact's `tests/domain/PostPart1.lean`.
   Top level on purpose: `#check Person.insert` must print as in the post. -/
import LeanDb.Model
open LeanDb.Model

-- Rule proofs are carried as arguments that the body never inspects.
set_option linter.unusedVariables false

/-! ## What exists -/

structure Person where
  name  : Name
  email : Email
  deriving Entity

inductive GuestListVisibility where
  | everyone    -- anyone with the link
  | attendees   -- the host and people who RSVP'd
  | hostOnly    -- just the host

structure Party where
  host        : Ref Person
  title       : Title
  description : Text
  date        : Time
  guestList   : GuestListVisibility
  deriving Entity

structure Rsvp where
  party : Ref Party
  guest : Ref Person
  deriving Entity

-- The raw RSVP table is read and written only in this module (`Party.guests`, `Rsvp.add`),
-- raw party writes too, and an edit cannot touch the host or the date.
internal Rsvp.select, Rsvp.insert, Party.update, Party.delete
-- The guest list joins RSVPs to the people who sent them.
link Rsvp.party Rsvp.guest
deriving instance Changes (except := [host, date]) for Party

constraint Person.uniqueEmail : unique email
private constraint Rsvp.onePerGuest : unique (party, guest)
-- Deleting a party deletes its RSVPs.
constraint Rsvp.cancelWithParty : cascade party
-- Generated on first use anyway; listed so importing modules can rely on them.
entity_operations Person, Party, Rsvp

/-- info: Person.insert : Person → DB (Except Person.Conflict (Ref Person)) -/
#guard_msgs in #check Person.insert

/--
info: inductive Person.Conflict where
  | uniqueEmail
-/
#guard_msgs in #print Person.Conflict

/-- info: Party.insert : Party → DB (Ref Party) -/
#guard_msgs in #check Party.insert

/-- info: Party.find : Ref Party → Query (Option (Row Party)) -/
#guard_msgs in #check Party.find

/-- info: Person.findBy : Email → Query (Option (Row Person)) -/
#guard_msgs in #check Person.findBy

/-- info: Rsvp.findBy : Ref Party → Ref Person → Query (Option (Row Rsvp)) -/
#guard_msgs in #check Rsvp.findBy

/-- info: Party.patch : Row Party → Party.Changes → DB Unit -/
#guard_msgs in #check Party.patch
#guard (HasRecord.fieldMetadata (T := Party.Changes)).map (·.name) == ["title", "description", "guestList"]
/-- info: Rsvp.link.party.guest : LinkKey Rsvp Party Person -/
#guard_msgs in #check Rsvp.link.party.guest
#guard Rsvp.link.party.guest.identity == "Rsvp.party.guest"
-- The cascade is recorded for the native schema, in declaration form.
run_cmd do
  unless (Deriving.cascadeDeclarations.getState (← Lean.getEnv)).any (fun entry =>
      entry.owner == `Rsvp && entry.field == `party && entry.target == `Party) do
    Lean.throwError "Rsvp.cancelWithParty is not recorded"

/-! ## Who can see who's coming -/

inductive Role where
  | host
  | attendee
  | visitor   -- signed in or not, hasn't RSVP'd
  deriving DecidableEq, Repr

structure Viewer (party : Ref Party) where
  private mk ::
  role : Role

/-- Your role relative to one party, from who you are and the RSVP table. -/
def Viewer.of (me : Option (Ref Person)) (p : Row Party) : Query (Viewer p.id) := do
  match me with
  | none => return ⟨.visitor⟩
  | some me =>
    if me == p.host then return ⟨.host⟩
    match ← Rsvp.findBy p.id me with
    | some _ => return ⟨.attendee⟩
    | none => return ⟨.visitor⟩

def CanSeeGuests : GuestListVisibility → Role → Bool
  | .everyone,  _         => true
  | .attendees, .host     => true
  | .attendees, .attendee => true
  | .attendees, .visitor  => false
  | .hostOnly,  .host     => true
  | .hostOnly,  .attendee => false
  | .hostOnly,  .visitor  => false

structure Guest where
  name : Name

inductive GuestList where
  | visible (guests : List Guest)
  | hidden

/-- Names of the people who RSVP'd, by guest id: one typed join (RSVP ⋈ Person) that selects
only `name`. It takes the proof that this viewer may see them. -/
def Party.guests (p : Row Party) (viewer : Viewer p.id)
    (h : CanSeeGuests p.guestList viewer.role) : Query (List Guest) :=
  (·.map Guest.mk) <$> Query.linkField Rsvp.link.party.guest Person.namePath p.id

/-! ## The rest of the rules -/

/-- Only the host can edit or cancel a party. -/
def MayEdit (p : Row Party) (viewer : Viewer p.id) : Prop :=
  viewer.role = .host

/-- Nobody can RSVP once the party has started. -/
def MayRsvp (now : Time) (p : Row Party) : Prop :=
  now < p.date

/-- A party can be moved until it starts, and only to a time in the future. -/
def MayReschedule (now : Time) (p : Row Party) (date : Time) : Prop :=
  now < p.date ∧ now < date

instance : Decidable (MayEdit p viewer) := inferInstanceAs (Decidable (viewer.role = .host))
instance : Decidable (MayRsvp now p) := inferInstanceAs (Decidable (now < p.date))

/-- The only way to change a date. (`internal` makes the raw `Party.update` private.) -/
def Party.reschedule (p : Row Party) (viewer : Viewer p.id) (now : Time) (date : Time)
    (h₁ : MayEdit p viewer) (h₂ : MayReschedule now p date) : DB Unit :=
  Party.update p { p.toParty with date }

/-- Only the host edits, and an edit cannot change the date or the host. -/
def Party.edit (p : Row Party) (viewer : Viewer p.id) (changes : Party.Changes)
    (h : MayEdit p viewer) : DB Unit :=
  Party.patch p changes

/-- `Rsvp.cancelWithParty` deletes the party's RSVPs with it. -/
def Party.cancel (p : Row Party) (viewer : Viewer p.id) (h : MayEdit p viewer) : DB Unit :=
  Party.delete p

/-- RSVP as yourself, before the party starts. -/
def Rsvp.add (p : Row Party) (me : Ref Person) (now : Time)
    (h : MayRsvp now p) : DB (Except Rsvp.Conflict Unit) := do
  match ← Rsvp.insert { party := p.id, guest := me } with
  | .ok _ => return .ok ()
  | .error conflict => return .error conflict

/-! ## Programs: the storage halves of the post's operations -/

inductive PostError where
  | emailTaken
  | notFound
  | notHost
  | alreadyStarted
  | dateInPast
  deriving Repr, BEq, DecidableEq

def createPerson (name : Name) (email : Email) : DB (Except PostError (Ref Person)) := do
  match ← Person.insert { name, email } with
  | .ok id              => return .ok id
  | .error .uniqueEmail => return .error .emailTaken

def hostParty (me : Ref Person) (now : Time) (title : Title) (description : Text) (date : Time)
    (guestList : GuestListVisibility) : DB (Except PostError (Ref Party)) := do
  if now < date then return .ok (← Party.insert { host := me, title, description, date, guestList })
  else return .error .dateInPast

def rsvp (me : Ref Person) (now : Time) (party : Ref Party) : DB (Except PostError Unit) := do
  let some p ← Party.find party | return .error .notFound
  if isOpen : MayRsvp now p then
    match ← Rsvp.add p me now isOpen with
    | .ok _               => return .ok ()
    | .error .onePerGuest => return .ok ()  -- already going
  else return .error .alreadyStarted

structure PartyPage where
  title       : Title
  description : Text
  date        : Time
  guests      : GuestList

def getParty (me : Option (Ref Person)) (party : Ref Party) : Query (Except PostError PartyPage) := do
  let some p ← Party.find party | return .error .notFound
  let viewer ← Viewer.of me p
  let guests ←
    if h : CanSeeGuests p.guestList viewer.role then
      GuestList.visible <$> Party.guests p viewer h
    else
      pure .hidden
  return .ok { title := p.title, description := p.description, date := p.date, guests }

def reschedule (me : Ref Person) (now : Time) (party : Ref Party) (date : Time) :
    DB (Except PostError Unit) := do
  let some p ← Party.find party | return .error .notFound
  let viewer ← Viewer.of (some me) p
  if isHost : MayEdit p viewer then
    if notStarted : now < p.date then
      if inFuture : now < date then
        Party.reschedule p viewer now date isHost ⟨notStarted, inFuture⟩
        return .ok ()
      else return .error .dateInPast
    else return .error .alreadyStarted
  else return .error .notHost

def edit (me : Ref Person) (party : Ref Party) (changes : Party.Changes) : DB (Except PostError Unit) := do
  let some p ← Party.find party | return .error .notFound
  let viewer ← Viewer.of (some me) p
  if isHost : MayEdit p viewer then
    Party.edit p viewer changes isHost
    return .ok ()
  else return .error .notHost

def cancel (me : Ref Person) (party : Ref Party) : DB (Except PostError Unit) := do
  let some p ← Party.find party | return .error .notFound
  let viewer ← Viewer.of (some me) p
  if isHost : MayEdit p viewer then
    Party.cancel p viewer isHost
    return .ok ()
  else return .error .notHost

def personByEmail (email : Email) : Query (Option (Ref Person)) := do
  return (← Person.findBy email).map (·.id)

def rsvpCount : Query Nat := do
  return (← Rsvp.select).length

derive_requirements createPerson, hostParty, rsvp, getParty, reschedule, edit, cancel, personByEmail,
  rsvpCount

/--
info: @getParty.Requirements.infer : {resources : StorageResources} →
  [capability0 : HasEntityResource resources Party] →
    [capability1 : HasEntityResource resources Rsvp] →
      [capability2 : HasEntityResource resources Person] →
        [capability3 :
            HasUniqueResource resources Rsvp (Ref Party × Ref Person) HasEntityResource.witness Rsvp.onePerGuest.key] →
          [capability4 : HasLinkResource resources Rsvp Party Person HasEntityResource.witness Rsvp.link.party.guest] →
            [capability5 : HasColumnResource resources Person Name HasEntityResource.witness Person.namePath] →
              getParty.Requirements resources
-/
#guard_msgs in #check @getParty.Requirements.infer

-- The storage requests of an unfolded body, read off its typed calls.
open Lean Meta Elab Command in
run_cmd liftTermElabM do
  let reschedule ← Requirements.inline Requirements.storageTargets (← getConstInfo ``reschedule).value!
  let nodes ← Requirements.storageNodes reschedule
  unless nodes.map (fun n => (n.kind, n.entity)) == #[("find", "Party"), ("findBy", "Rsvp"), ("update", "Party")] do
    throwError "reschedule: unexpected storage nodes {repr nodes}"
  let create ← Requirements.inline Requirements.storageTargets (← getConstInfo ``createPerson).value!
  let nodes ← Requirements.storageNodes create
  unless nodes.map (fun n => (n.kind, n.access, n.constraints)) == #[("insert", .command, ["Person.uniqueEmail"])] do
    throwError "createPerson: unexpected storage nodes {repr nodes}"
  let page ← Requirements.inline Requirements.storageTargets (← getConstInfo ``getParty).value!
  let kinds := (← Requirements.storageNodes page).map (·.kind)
  -- The guest list is one join request; no raw RSVP read is reachable from `getParty`.
  unless kinds.contains "linkField" && !kinds.contains "select" && (← Requirements.storageNodes page).all (·.access == .query) do
    throwError "getParty: unexpected storage nodes {kinds}"
