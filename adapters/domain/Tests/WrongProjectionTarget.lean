import LeanDbDomain

namespace WrongProjectionTargetFixture
open LeanApp.Domain LeanDb.Domain

@[entity] structure Person where
  name : Name
  email : Email

@[entity] structure Party where
  guests : Members Person := {}

native_schema% S := Person, Party

-- Canonical field evidence cannot be inserted into an arbitrary carried target
-- dictionary. The actual relation, rather than a sibling class, owns that type.
def mismatched (relation : MemberStorage S Party Person) :
    ProjectionStorage relation Person.namePath where
  column := HasFieldStorage.storage (s := S) (T := Person) (field := "name") (Value := Name)
  source_agrees := rfl

-- Output-directed lookup must still reject an unknown ACTUAL target dictionary.
def mismatchedResource (relation : MemberStorage S Party Person) :
    HasProjectionResource (storageResources S) Party Person "guests" relation "name" Name :=
  inferInstance

end WrongProjectionTargetFixture
