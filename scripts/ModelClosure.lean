import LeanDb.Model

/-! `LeanDb.Model` is portable: its import closure is itself, `LeanOntology` and Lean's own
libraries. No SQLite binding and no native LeanDB module may appear in it. -/

open Lean in
run_cmd do
  let modules := (← getEnv).header.moduleNames
  let allowed (m : Name) : Bool :=
    [`LeanDb.Model, `LeanOntology, `Lean, `Init, `Std].any fun root => root == m || root.isPrefixOf m
  let foreign := modules.filter (!allowed ·)
  unless foreign.isEmpty do throwError "LeanDb.Model is not portable; its closure imports {foreign}"
  logInfo m!"LeanDb.Model closure: {modules.size} modules, all portable"
