/-
  Fail if key M15-pre definitions/theorems depend on axioms beyond the
  standard trio `propext`, `Classical.choice`, `Quot.sound`.
  Compiled as part of `lake exe leandb_tests` (imported from Tests.lean).
-/
import Lean
import LeanDb
import TestsM14a

open Lean Elab Command

def allowedAxioms : NameSet :=
  ({} : NameSet)
    |>.insert ``propext
    |>.insert ``Classical.choice
    |>.insert ``Quot.sound

def assertAxioms (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains n do
    throwError "axiom check: unknown constant {n}"
  let axs ← collectAxioms n
  let extra := axs.toList.filter (fun a => !allowedAxioms.contains a)
  unless extra.isEmpty do
    throwError "axiom check: {n} depends on {extra} (allowed: propext, Classical.choice, Quot.sound)"
  logInfo m!"axiom check: {n} OK {axs.toList}"

elab "#check_m15_axioms" : command => do
  assertAxioms ``LeanDb.DbState.get_set_same
  assertAxioms ``LeanDb.DbState.get_set_other
  assertAxioms ``LeanDb.DbState.empty_rows
  assertAxioms ``LeanDb.Txn.denote
  assertAxioms ``LeanDb.Read.denote
  assertAxioms ``TestsM14a.insert_team_on_empty

#check_m15_axioms
