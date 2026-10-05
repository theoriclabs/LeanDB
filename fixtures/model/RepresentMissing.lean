/- A private-constructor type from another module without `represent` cannot be a field. -/
import TestsModel.RepresentTypes
import LeanDb.Model
open LeanDb.Model
structure Vault where
  label  : Name
  secret : Opaque
  deriving Entity
