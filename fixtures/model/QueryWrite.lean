/- A `Query` is read-only by type: it cannot contain an insert. -/
import TestsModel.Post
open LeanDb.Model
def sneaky (name : Name) (email : Email) : Query Unit := do
  let _ ← Person.insert { name, email }
