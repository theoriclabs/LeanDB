/- The raw RSVP table is internal to the module that declares the model. -/
import TestsModel.Post
open LeanDb.Model
def everyone : Query (List (Row Rsvp)) := Rsvp.select
