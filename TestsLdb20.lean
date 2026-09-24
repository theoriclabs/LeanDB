import LeanDb

/-! LDB-20: a multi-statement verb that joins an outer transaction runs
    under a SAVEPOINT, so catching its error and committing the outer
    scope cannot keep partial effects. -/

namespace TestsLdb20

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

private def check' (condition : Bool) (message : String) : DbM Unit :=
  unless condition do throw (.sqlite s!"FAIL: {message}")

private def expectOk (r : Except DbError α) (context : String) : IO α :=
  match r with
  | .ok a => pure a
  | .error e => throw <| IO.userError s!"FAIL: {context}: {e}"

structure Posting where
  amount : Int64
  deriving Repr, BEq, LeanDb.Inline

structure Account where
  name : String
  balance : Int64
  postings : List Posting
  deriving Repr

@[leandb_invariant]
def Account.invariant (a : Account) : Bool :=
  a.balance ≥ 0 && a.balance == (a.postings.map (·.amount)).foldl (· + ·) 0

deriving instance LeanDb.Entity for Account

structure Keep where
  name : String
  deriving Repr, LeanDb.Entity

private def specs : List TableSpec := Entity.specs Account ++ Entity.specs Keep

private def dbPath : System.FilePath := ".lake" / "leandb_test_ldb20.sqlite"

private def fresh (p : System.FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p
  for suffix in ["-wal", "-shm"] do
    let side : System.FilePath := p.toString ++ suffix
    if ← side.pathExists then IO.FS.removeFile side

private def good : Account := ⟨"alice", 30, [⟨50⟩, ⟨-20⟩]⟩

/-- Swallow a failed `patch` (UPDATE then invariant `get`) inside an
    outer write transaction and still commit. The savepoint must undo
    the UPDATE so the stored account stays valid. -/
private def testNestedVerbAtomic : IO Unit := do
  fresh dbPath
  let r ← withDb dbPath specs do
    withTransaction do
      discard <| insert Keep ⟨"outer"⟩
      let s ← insert Account good
      let inner : DbM PatchResult :=
        patch s.id ⟨#[Assignment.of Account.Field.balance (-1 : Int64)]⟩
      let _ : Unit ← fun conn => ExceptT.mk do
        match ← (inner conn).run with
        | .ok _ => return .ok ()
        | .error _ => return .ok ()
    let names ← (·.map (·.val.name)) <$> fetchAll Keep
    check' (names == #["outer"]) s!"outer row survives, got {names}"
    let accs ← fetchAll Account
    check' (accs.map (·.val.balance) == #[30])
      s!"failed patch rolled back to savepoint, got {accs.map (·.val.balance)}"
  discard <| expectOk r "nested verb atomic"

def run : IO Unit := testNestedVerbAtomic

end TestsLdb20
