import LeanDbDomain

namespace ProjectionEvolutionFixture
open LeanApp.Domain LeanDb.Domain

-- Added original-domain columns automatically obtain typed projection evidence;
-- no manual native field, relation or output record is added by the app author.
@[entity] structure Person where
  name : Name
  nickname : Name
  email : Email

@[entity] structure Party where
  title : Title
  guests : Members Person := {}

query% nicknames (id : Ref Party) : Disclosure (List Name) := do
  let party ← find Party id else partyMissing
  disclose (Policy.literal true) do
    party.guests.project fun person => person.nickname

native_schema% S := Person, Party

def generatedRequirements : nicknames.Requirements (storageResources S) :=
  nicknames.Requirements.infer (resources := storageResources S)

def evolved (row : Row Unit Party) : Projection Unit (List Name) (storageResources S) :=
  Projection.memberField (Row.membersField row "guests") "nickname"

def main : IO Unit := do
  let .ok name := Name.parse "Ada" | throw (IO.userError "name")
  let .ok nickname := Name.parse "Countess" | throw (IO.userError "nickname")
  let .ok email := Email.parse "ada@example.test" | throw (IO.userError "email")
  let .ok title := Title.parse "Evolved" | throw (IO.userError "title")
  let nonce ← IO.monoNanosNow
  match ← LeanDb.withDb s!"/tmp/leandb-projection-evolution-{nonce}.sqlite" (LeanDb.IsSchema.specs S) do
    let person ← LeanDb.insert Person ⟨name, nickname, email⟩
    let party ← LeanDb.insert Party ⟨title, {}⟩
    let .ok parent := idToRef party.id | throw (.sqlite "parent ref")
    let members := HasMemberStorage.storage (s := S) (Parent := Party) (field := "guests") (Target := Person)
    match ← LeanDb.Txn.run (s := S) (ε := String) (do
      let some live ← LeanDb.Txn.get Party party.id | LeanDb.Txn.throw "missing party"
      (LeanDb.Txn.includeMember (Party.guestsRelation.bind live) person.id).orAbort (fun _ => "FK")) with
    | .ok (.ok ()) => pure ()
    | _ => throw (.sqlite "evolved include")
    let selection := HasProjectionResource.witness (family := storageResources S)
      (P := Party) (T := Person) (member := "guests") (storage := members) (field := "nickname") (V := Name)
    let .ok plan := selection.project parent | throw (.sqlite "evolved plan")
    let before ← LeanDb.DbState.load (s := S)
    let .ok actual ← LeanDb.Read.run plan | throw (.sqlite "evolved execution")
    unless actual == [nickname] && actual == LeanDb.Read.denote plan before && before.checkWF do
      throw (.sqlite "added original field projection/denotation/WF")
  with
  | .error error => throw (IO.userError error.message)
  | .ok () => IO.println "generated original-domain projection evolution: populated nickname PASS"

end ProjectionEvolutionFixture

def main : IO Unit := ProjectionEvolutionFixture.main
