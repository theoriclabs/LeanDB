/- A string label cannot turn an Email column into a Name column: the native dictionary must
   retain genuine value-type and getter equality. -/
import LeanDb.Native

namespace WrongFieldStorageFixture
open LeanDb.Model

structure Profile where
  name : Name
  email : Email
  deriving Entity

native_schema% S := Profile

example : LeanDb.Native.FieldStorage Profile Name where
  field := Profile.DbField.email
  valueType := by
    change Email = Name
    rfl
  source := Profile.namePath
  getter_agrees := fun _ => rfl

end WrongFieldStorageFixture
