import TestsDdd
open LeanDb TestsDdd

-- Expected rejection: binding must go through a transaction's Current parent.
def forged : MemberHandle Unit Party Person Party.Guests :=
  MemberHandle.mk Party.guestsRelation ⟨1⟩
