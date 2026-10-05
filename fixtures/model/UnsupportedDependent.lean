import LeanDb.Model
open LeanDb.Model
structure Dependent (n : Nat) where
  value : Fin n
  deriving Domain
