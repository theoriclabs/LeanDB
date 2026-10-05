import LeanDb.Model
open LeanDb.Model
inductive Payload where
  | item (name : Name)
  deriving Domain
