import LeanDb

-- Expected rejection: this formerly constructed the vacuous marker.
example (s : Type) [LeanDb.IsSchema s] : LeanDb.ExecutesAsMeaning s := ⟨⟩
