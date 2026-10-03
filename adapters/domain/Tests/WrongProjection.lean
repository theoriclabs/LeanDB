import LeanDbDomain.Schema

namespace WrongProjectionFixture
open LeanApp.Domain

@[entity] structure Profile where
  name : Name
  email : Email

native_schema% S := Profile

-- A string label cannot turn an Email column into a Name projection. The
-- native dictionary must retain genuine value-type and getter equality.
example : LeanDb.Domain.FieldStorage Profile Name where
  field := Profile.DbField.email
  valueType := by
    change Email = Name
    rfl
  source := Profile.namePath
  getter_agrees := fun _ => rfl

end WrongProjectionFixture
