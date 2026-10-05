import LeanDb.Model
open LeanDb.Model
structure Base where
  title : Title
  deriving Domain
structure Child extends Base where
  extra : Text
  deriving Domain
