/- An old exhaustive native caller becomes nonexhaustive when the MODEL declaration adds email
   uniqueness: no repeated native unique declaration. -/
import LeanDb.Native

namespace ModelUniqueEvolution
open LeanDb.Model

structure Account where
  name : Name
  email : Email
  deriving Entity

constraint Account.byName : unique name
constraint Account.byEmail : unique email
native_schema% S := Account

def oldHandler : LeanDb.InsertError Account → Nat
  | .duplicate .byName _ => 0
  | .missingRef fk => nomatch fk

end ModelUniqueEvolution
