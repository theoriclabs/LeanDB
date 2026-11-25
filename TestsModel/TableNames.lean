import TestsModel.TableNameTypes
import LeanDb.Native

namespace ModelTableNames
open LeanDb.Model

-- Storage naming belongs to the native package; the imported model
-- needs no engine import or SQL annotations.
attribute [leandb_table "model_workspace_snapshot"] A.Snapshot
attribute [leandb_table "model_session_snapshot"] B.Snapshot

native_schema% Named := A.Snapshot, B.Snapshot

#guard LeanDb.Entity.tableName A.Snapshot == "model_workspace_snapshot"
#guard LeanDb.Entity.tableName B.Snapshot == "model_session_snapshot"
#guard ((LeanDb.Entity.columns B.Snapshot)[0]!).fkTable == some "model_workspace_snapshot"
#guard (LeanDb.Entity.spec B.Snapshot).indexes.any (fun i => i.unique)

def run : IO Unit := do
  let path : System.FilePath := ".lake" / "leandb_test_model_table_names.sqlite"
  if ← path.pathExists then IO.FS.removeFile path
  match ← LeanDb.withDb path [LeanDb.Entity.spec A.Snapshot, LeanDb.Entity.spec B.Snapshot] do
    let workspace ← LeanDb.insert A.Snapshot ⟨"workspace"⟩
    let workspaceRef ← LeanDb.DbM.ofExcept
      ((LeanDb.Native.idToRef workspace.ref).mapError LeanDb.DbError.sqlite)
    let session ← LeanDb.insert B.Snapshot ⟨workspaceRef⟩
    let some stored ← LeanDb.get session.ref | throw (.sqlite "missing session")
    unless stored.val.workspace == workspaceRef do throw (.sqlite "wrong reference")
  with
  | .ok () => pure ()
  | .error e => throw <| IO.userError s!"explicit model table names: {e}"

end ModelTableNames
