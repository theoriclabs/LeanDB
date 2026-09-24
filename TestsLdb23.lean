import LeanDb

/-! LDB-23: `Snapshot.rows` fails on an undecodable row instead of
    dropping it (which would make `forall` vacuously true). -/

namespace TestsLdb23

open LeanDb

private def check (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw <| IO.userError s!"FAIL: {message}"

structure Num where
  n : Nat
  deriving Repr, LeanDb.Entity

private def testUndecodableFails : IO Unit := do
  let s := Pred.Snapshot.empty.addRaw (Entity.tableName Num) #[(1, #[.text "not a nat"])]
  match Pred.Snapshot.rows? s Num with
  | .error e => check (e.code == "decode") s!"expected decode, got {e}"
  | .ok rs =>
      throw <| IO.userError s!"FAIL: dropped undecodable rows (got {rs.size}) instead of failing"
  let honest := Pred.Snapshot.empty.add Num #[⟨⟨1⟩, ⟨7⟩⟩]
  match Pred.Snapshot.rows? honest Num with
  | .ok rs => check (rs.map (·.val.n) == #[7]) s!"honest row: {rs.map (·.val.n)}"
  | .error e => throw <| IO.userError s!"FAIL: honest snapshot: {e}"

def run : IO Unit := testUndecodableFails

end TestsLdb23
