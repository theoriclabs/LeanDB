/- References are typed: a person's id does not find a party. -/
import TestsModel.Post
open LeanDb.Model
def wrong (person : Ref Person) : Query (Option (Row Party)) := Party.find person
