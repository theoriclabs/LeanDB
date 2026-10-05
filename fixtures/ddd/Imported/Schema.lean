import Imported.Declaration
import LeanDb.Typed.Harness

namespace ImportedMembers
open LeanDb

schema% S := Person, Party
#synth IsSchema.Has S Party.Guests

def main : IO Unit := do
  unless (IsSchema.specs S).length == 3 do
    throw (IO.userError "member schema closure lost imported declaration")
  unless !(HasReferencedBy.anyRestrict (s := S) (α := Party)) do
    throw (IO.userError "imported parent cascade became RESTRICT in denotation")
  let nonce ← IO.monoNanosNow
  let path : System.FilePath := s!"/tmp/leandb-imported-members-{nonce}.sqlite"
  match ← withDb path (IsSchema.specs S) do
    let person ← LeanDb.insert Person ⟨"Imported guest"⟩
    let party ← LeanDb.insert Party ⟨"Imported party"⟩
    match ← Txn.run (s := S) (ε := String) (do
      let some row ← Txn.get Party party.id | Txn.throw "missing parent"
      (Txn.includeMember (Party.guestsRelation.bind row) person.id).orAbort (fun _ => "missing FK")) with
    | .ok (.ok ()) => pure ()
    | _ => throw (.sqlite "imported relation include failed")
    let before ← DbState.load (s := S)
    let expected := Txn.denote (σ := Unit) (ε := String) (Txn.delete Party party.id) before
    match ← Txn.run (s := S) (ε := String) (Txn.delete Party party.id) with
    | .ok (.ok (.ok removed)) =>
        match expected.1 with
        | .ok (.ok pureRemoved) =>
            unless removed.id == pureRemoved.id && Entity.encode removed.val == Entity.encode pureRemoved.val do
              throw (.sqlite "imported delete payload differs from pure meaning")
        | _ => throw (.sqlite "pure imported delete unexpectedly failed")
    | _ => throw (.sqlite "imported cascade did not delete parent")
    let after ← DbState.load (s := S)
    unless Harness.getEq (α := Person) after expected.2 &&
      Harness.getEq (α := Party) after expected.2 &&
      Harness.getEq (α := Party.Guests) after expected.2 && after.checkWF &&
      (after.get (α := Party.Guests)).rows.isEmpty && (after.get (α := Person)).rows.length == 1 do
      throw (.sqlite "imported cascade differs from pure meaning or removed person")
  with
  | .error error => throw (IO.userError error.message)
  | .ok () => IO.println "imported member closure/cascade differential check passed"

end ImportedMembers

def main : IO Unit := ImportedMembers.main
