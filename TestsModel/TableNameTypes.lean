import LeanDb.Model

/- Explicit table names must survive importing a model before its native
   storage is derived (#140). -/

namespace ModelTableNames
open LeanDb.Model

structure A.Snapshot where
  title : String
  deriving Entity

structure B.Snapshot where
  workspace : Ref A.Snapshot
  deriving Entity

constraint B.Snapshot.onePerWorkspace : unique workspace

end ModelTableNames
