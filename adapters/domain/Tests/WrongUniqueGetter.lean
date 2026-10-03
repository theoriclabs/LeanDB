import LeanDbDomain.Schema

namespace WrongUniqueGetterFixture
open LeanApp.Domain

@[entity] structure Profile where
  email : Email
  backup : Email

-- A direct-looking path with a swapped getter cannot acquire native key
-- evidence just by naming the email column. Both values have the SAME type.
def Profile.byEmail : Unique Profile Email := {
  identity := "WrongUniqueGetterFixture.Profile.byEmail"
  field := Ontology.FieldPath.field (Ontology.HasTypeId.typeId (α := Profile))
    "email" Profile.backup }

-- A same-named marker cannot suppress the genuine getter proof check.
def Profile.byEmail.nativeFieldAgreement : True := trivial

native_schema% S := Profile

end WrongUniqueGetterFixture
