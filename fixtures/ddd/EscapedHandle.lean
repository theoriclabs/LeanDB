import TestsDdd
open LeanDb TestsDdd

-- Expected rejection: a handle in σ cannot be returned with another scope.
def escape : {σ : Type} → Txn σ S String (MemberHandle Unit Party Person Party.Guests) := do
  let some row ← Txn.get Party ⟨1⟩ | Txn.throw "missing"
  pure (Party.guestsRelation.bind row)
