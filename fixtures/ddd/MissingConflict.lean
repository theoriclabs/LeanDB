import TestsDddM2
open LeanDb TestsDddM2

-- Expected rejection: the post's `rsvp` without deciding what a second yes
-- means. `Txn.insertUnique` returns the declared alternatives, so the match
-- is not exhaustive: `Missing cases: (Except.error Rsvp.Unique.onePerGuest)`.
def rsvpForgetful (guest : LeanDb.Id Person) (party : LeanDb.Id Party) :
    {σ : Type} → Txn σ S String Unit := do
  let .ok row := Entity.check Rsvp ⟨party, guest⟩ | Txn.throw "invalid"
  match ← Txn.insertUnique row (fun _ => "missingRef") with
  | .ok _ => pure ()
