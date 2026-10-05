import TestsDdd
open LeanDb TestsDdd

-- Expected rejection: nominal target identity cannot stand in for the parent.
def wrongParent : Read S Bool :=
  Read.memberContains Party.guestsRelation (⟨1⟩ : LeanDb.Id Person) (⟨1⟩ : LeanDb.Id Person)
