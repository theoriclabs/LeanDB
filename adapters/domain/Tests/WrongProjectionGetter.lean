import LeanDbDomain

namespace WrongProjectionGetterFixture
open LeanApp.Domain LeanDb.Domain

@[entity] structure Person where
  name : Name
  nickname : Name
  email : Email

@[entity] structure Party where
  guests : Members Person := {}

native_schema% S := Person, Party

def swapped : Ontology.FieldPath Person Name :=
  ⟨Person.namePath.identity, Person.nickname⟩

-- Same type and exact same label still do not establish getter agreement.
def forged : ProjectionStorage
    (HasMemberStorage.storage (s := S) (Parent := Party) (field := "guests") (Target := Person)) swapped where
  column := HasFieldStorage.storage (s := S) (T := Person) (field := "name") (Value := Name)
  source_agrees := rfl

end WrongProjectionGetterFixture
