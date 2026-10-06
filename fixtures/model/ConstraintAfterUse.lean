/- A constraint changes `T.insert`'s type, so it must come before `T.insert` is first used. -/
import LeanDb.Model
open LeanDb.Model
structure Person where
  name : Name
  email : Email
  deriving Entity
def make (name : Name) (email : Email) : DB (Ref Person) := Person.insert { name, email }
constraint Person.uniqueEmail : unique email
