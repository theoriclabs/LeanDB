import LeanDbDomain.Schema

namespace PortableUniqueEvolution
open LeanApp.Domain

@[entity] structure Account where
  name : Name
  email : Email

unique% Account.byName := name
unique% Account.byEmail := email
native_schema% S := Account

-- An old exhaustive native caller becomes nonexhaustive when the PORTABLE
-- declaration adds email uniqueness. No repeated native unique declaration.
def oldHandler : LeanDb.InsertError Account → Nat
  | .duplicate .byName _ => 0
  | .missingRef fk => nomatch fk

end PortableUniqueEvolution
