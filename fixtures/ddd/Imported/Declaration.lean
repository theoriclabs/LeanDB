import LeanDb.Typed.Members

namespace ImportedMembers

structure Person where
  name : String
  deriving BEq, LeanDb.Entity

structure Party where
  title : String
  deriving BEq, LeanDb.Entity

members% Party.guests : Person

end ImportedMembers
