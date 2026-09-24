import LeanDb

/-! LDB-21: `patch` refuses a guard with an opaque leaf. Opaque used to
    render as `1`, so a residual false guard still updated the row. -/

namespace TestsLdb21

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

structure Tag where
  name : String
  deriving Repr, LeanDb.Entity

private def specs : List TableSpec := Entity.specs Tag

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb21.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def testRejectOpaque : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    let s ← insert Tag ⟨"keep"⟩
    let p : Patch Tag := { sets := #[Assignment.of Tag.Field.name "changed"] }
    let act : DbM PatchResult := patch s.id p (.opaque fun _ => false)
    match ← (fun conn => ExceptT.mk (.ok <$> (act conn).run)) with
    | .error e =>
        unless e.code == "sqlite" do
          throw (.sqlite s!"FAIL: expected sqlite refusal, got {e}")
    | .ok .updated =>
        throw (.sqlite "FAIL: opaque false guard was treated as true")
    | .ok other =>
        throw (.sqlite s!"FAIL: expected error, got {repr other}")
    let back ← get s.id
    unless back.map (·.val.name) == some "keep" do
      throw (.sqlite s!"FAIL: row changed, got {back.map (·.val.name)}")
    let ok ← patch s.id p .tt
    unless ok == .updated do throw (.sqlite s!"FAIL: exact guard, got {repr ok}")
  discard <| expectOk r "opaque patch guard"

def run : IO Unit := testRejectOpaque

end TestsLdb21
