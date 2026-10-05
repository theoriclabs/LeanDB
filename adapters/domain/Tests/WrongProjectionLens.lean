import LeanDbDomain

namespace WrongProjectionLensFixture
open LeanApp.Domain LeanDb.Domain

@[entity] structure Person where
  name : Name
  nickname : Name
  email : Email

@[entity] structure Party where
  guests : Members Person := {}

native_schema% S := Person, Party

-- A lawful lens with the original name/path identity and a DIFFERENT getter.
-- Native evidence must match the actual portable dictionary, not just labels.
local instance : EditableField Person "name" Name where
  lens := { (EditableField.lens (T := Person) (field := "nickname")) with
    identity := Person.namePath.identity }
  laws := by
    constructor
    · intro record value; rfl
    · intro record; cases record; rfl
    · intro record first second; rfl

def mismatched (row : Row Unit Party) : Projection Unit (List Name) (storageResources S) :=
  Projection.memberField (Row.membersField row "guests") "name"

end WrongProjectionLensFixture
