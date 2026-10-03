import LeanDbDomain
import LeanDb.Typed.Gate
import LeanDb.Typed.Link

/-! Milestone 2 on ORIGINAL portable records (native_schema%): the migration
gate and the typed semi-join over an ordinary `Rsvp` entity. Field symbols
here are the bridge's `T.DbField`; `migration%` resolves them through
`Entity.Field T`. Portable `Ref` columns encode exactly as native `Id`s, so
the link's coherence laws are `rfl`. -/

namespace GateEvolutionFixture
open LeanApp.Domain

inductive GuestListVisibility where
  | everyone | attendees | hostOnly
  deriving Domain

deriving instance BEq for GuestListVisibility

namespace V1
@[entity] structure Person where
  name : Name
  email : Email

@[entity] structure Party where
  host : Ref Person
  title : Title
  date : Instant

@[entity] structure Rsvp where
  party : Ref Party
  guest : Ref Person

-- Decision 8, on the portable record: deleting a party deletes its RSVPs.
cascade% Rsvp.party
native_schema% S := Person, Party, Rsvp
end V1

namespace V2
@[entity] structure Person where
  name : Name
  email : Email

@[entity] structure Party where
  host : Ref Person
  title : Title
  date : Instant
  guestList : GuestListVisibility

@[entity] structure Rsvp where
  party : Ref Party
  guest : Ref Person

cascade% Rsvp.party
native_schema% S := Person, Party, Rsvp

migration% addGuestList := Party.addField guestList (fill := .everyone)

def guestLinks : LeanDb.LinkRelation Party Person Rsvp where
  parentField := Rsvp.DbField.party
  targetField := Rsvp.DbField.guest
  getParent := fun r => LeanDb.ReferenceValue.id r.party
  getTarget := fun r => LeanDb.ReferenceValue.id r.guest
  parentColumn := fun _ => rfl
  targetColumn := fun _ => rfl
end V2

private def must {α} (label : String) (x : IO (Except LeanDb.DbError α)) : IO α := do
  match ← x with
  | .ok a => return a
  | .error e => throw (IO.userError s!"{label}: {e}")


def main : IO Unit := do
  let nonce ← IO.monoNanosNow
  let path : System.FilePath := s!"/tmp/leandb-gate-evolution-{nonce}.sqlite"
  let .ok ada := Name.parse "Ada" | throw (IO.userError "name")
  let .ok grace := Name.parse "Grace" | throw (IO.userError "name")
  let .ok asha := Name.parse "Asha" | throw (IO.userError "name")
  let .ok title := Title.parse "Housewarming" | throw (IO.userError "title")
  let .ok date := Instant.ofEpochSeconds 2000 | throw (IO.userError "date")
  match ← LeanDb.withDb path (LeanDb.IsSchema.specs V1.S) do
    let mk (n : Name) (e : String) : LeanDb.DbM (LeanDb.Stored V1.Person) := do
      let .ok email := Email.parse e | throw (.sqlite "email")
      LeanDb.insert V1.Person ⟨n, email⟩
    let host ← mk asha "asha@example.test"
    let g1 ← mk grace "grace@example.test"
    let g2 ← mk ada "ada@example.test"
    let .ok hostRef := LeanDb.Domain.idToRef host.id | throw (.sqlite "ref")
    let party ← LeanDb.insert V1.Party ⟨hostRef, title, date⟩
    let .ok partyRef := LeanDb.Domain.idToRef party.id | throw (.sqlite "ref")
    for g in [g1, g2] do
      let .ok guestRef := LeanDb.Domain.idToRef g.id | throw (.sqlite "ref")
      discard <| LeanDb.insert V1.Rsvp ⟨partyRef, guestRef⟩
  with
  | .error e => throw (IO.userError s!"seed: {e}")
  | .ok () => pure ()
  let target := LeanDb.Gate.Target.ofSchema V2.S
  let raw ← must "raw" (LeanDb.openDbRaw path)
  match ← must "check" (LeanDb.Gate.check raw target []) with
  | .refused [.missingFill "Party" "party" "guestList"] => pure ()
  | status => throw (IO.userError s!"portable refusal:\n{status.render}")
  let (conn, outcome) ← must "migrate" (LeanDb.Gate.openDb path target [V2.addGuestList])
  unless outcome matches .applied .. do throw (IO.userError "portable migration did not apply")
  match ← LeanDb.DbM.run conn (do
    let st ← LeanDb.DbState.load (s := V2.S)
    unless st.checkWF && (st.get (α := V2.Party)).rows.all (·.val.guestList == .everyone) do
      throw (.sqlite "portable backfill")
    -- The semi-join on original records: names only, by guest id.
    let program : LeanDb.Read V2.S (List Name) :=
      .linkField V2.guestLinks ⟨1⟩ V2.Person.DbField.name
    let expected := LeanDb.Read.denote program st
    let .ok names ← LeanDb.Read.run program | throw (.sqlite "linkField")
    unless names == expected && names == [grace, ada] do
      throw (.sqlite s!"portable linkField order/meaning")
    -- Cancelling the party cascades its RSVPs and keeps the people.
    match ← LeanDb.Txn.run (s := V2.S) (ε := String) (do
      match ← LeanDb.Txn.delete V2.Party ⟨1⟩ with
      | .ok _ => pure ()
      | .error _ => LeanDb.Txn.throw "delete") with
    | .ok (.ok ()) => pure ()
    | _ => throw (.sqlite "portable cancel")
    let after ← LeanDb.DbState.load (s := V2.S)
    unless (after.get (α := V2.Rsvp)).rows.isEmpty && (after.get (α := V2.Person)).rows.length == 3 &&
        after.checkWF do
      throw (.sqlite "portable cascade"))
  with
  | .error e => throw (IO.userError e.message)
  | .ok () => IO.println "portable records: gate refusal, typed backfill, semi-join and cascade PASS"

end GateEvolutionFixture

def main : IO Unit := GateEvolutionFixture.main
