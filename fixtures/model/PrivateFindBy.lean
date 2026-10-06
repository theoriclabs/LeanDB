/- The composite RSVP lookup is private to the module that declares the model. -/
import TestsModel.Post
open LeanDb.Model
def probe (party : Ref Party) (person : Ref Person) := Rsvp.findBy party person
