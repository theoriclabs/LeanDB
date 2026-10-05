/- An edit cannot move the party: `Party.Changes` has no `date`. -/
import TestsModel.Post
open LeanDb.Model
def sneaky (title : Title) (description : Text) (date : Time) : Party.Changes :=
  { title, description, guestList := .everyone, date }
