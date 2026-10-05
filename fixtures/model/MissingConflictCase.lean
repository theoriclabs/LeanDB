/- A conflict the program does not handle: `Rsvp.insert`'s result has a case per declared
   constraint, so a match that forgets `onePerGuest` is incomplete. -/
import LeanDb.Model
open LeanDb.Model
structure Person where
  name : Name
  deriving Entity
structure Party where
  title : Title
  deriving Entity
structure Rsvp where
  party : Ref Party
  guest : Ref Person
  deriving Entity
constraint Rsvp.onePerGuest : unique (party, guest)
def rsvp (guest : Ref Person) (party : Ref Party) : DB Bool := do
  let some _ ← Party.find party | return false
  match ← Rsvp.insert { party, guest } with
  | .ok _ => return true
