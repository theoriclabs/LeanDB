import LeanDbDomain

namespace MissingProjectionFixture
open LeanApp.Domain LeanDb.Domain

@[entity] structure Person where
  name : Name
  email : Email

@[entity] structure Party where
  guests : Members Person := {}

native_schema% S := Person, Party

-- Even a lawful portable alias needs explicit native column/path evidence.
instance : EditableField Person "alias" Name :=
  inferInstanceAs (EditableField Person "name" Name)

def missing (row : Row Unit Party) : Projection Unit (List Name) (storageResources S) :=
  Projection.memberField (Row.membersField row "guests") "alias"

end MissingProjectionFixture
