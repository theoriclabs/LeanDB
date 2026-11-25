import Lean
import LeanDb.Cli

/-! # `query%`: CLI queries derived from definition signatures

`query% slaBreached` turns `def slaBreached (now : Timestamp) : DbM ρ`
into a `QueryEntry`: the name, the parameters as `(binder, type)` pairs
(so `help`, an API, or an agent can see the signature), and a runner in
which each argument is parsed positionally through its type's `CliArg`
instance (types drive parsing — plan.md §4.2) and the result renders
through `QueryOut`. A base's query list becomes
`queries := [query% openTickets, query% slaBreached]` — no hand-written
flag parsing, and adding an argument to a query def changes its CLI
arity with no other edit.
-/

namespace LeanDb.Cli

open Lean Elab Term Meta

/-- The footprint of a query def: every plan reified while elaborating it,
    plus those of the definitions it uses (a `pred%` plan bound to a name,
    a helper query it calls), followed transitively through this package's
    own declarations. -/
private def queryFootprint (root : Name) : MetaM Footprint := do
  let env ← getEnv
  let mainRoot := (← getMainModule).getRoot
  let allowedRoots := (PlanElab.footprintModuleRoots env).insert mainRoot
  let ours := fun (n : Name) =>
    match env.getModuleIdxFor? n with
    | none => true
    | some idx => (env.header.moduleNames[idx.toNat]?.map (fun m => allowedRoots.contains m.getRoot)).getD false
  let mut visited : List Name := []
  let mut queue : List Name := [root]
  let mut acc : Footprint := {}
  let mut budget := 2000
  while !queue.isEmpty && budget > 0 do
    budget := budget - 1
    let n := queue.head!
    queue := queue.tail!
    if visited.contains n then continue
    visited := n :: visited
    for e in PlanElab.footprintsOf env n do
      acc := acc.union { tables := e.types, columns := e.columns, residual := e.residual }
    if let some info := env.find? n then
      if let some v := info.value? then
        for c in v.getUsedConstants do
          if ours c && !visited.contains c then queue := queue ++ [c]
  return acc

elab "query% " id:ident : term => do
  let name ← realizeGlobalConstNoOverloadWithInfo id
  let info ← getConstInfo name
  let fp ← queryFootprint name
  -- Plain forallTelescope: the reducing variant would unfold the `DbM`
  -- abbrev and hide the return-type check behind ReaderT plumbing.
  let (binderNames, binderTys, tyStrs) ← forallTelescope info.type fun xs body => do
    unless body.isAppOf ``LeanDb.DbM do
      throwError "query%: {name} must return in DbM, found {body}"
    let mut names : Array String := #[]
    let mut tys : Array Term := #[]
    let mut strs : Array String := #[]
    for x in xs do
      let decl ← x.fvarId!.getDecl
      unless decl.binderInfo == .default do
        throwError "query%: {name} has non-explicit binder '{decl.userName}'; only explicit arguments become CLI arguments"
      let ty ← instantiateMVars decl.type
      names := names.push decl.userName.toString
      tys := tys.push (← PrettyPrinter.delab ty)
      strs := strs.push (toString (← ppExpr ty))
    return (names, tys, strs)
  -- fun args => do
  --   let (a0, args) ← popArg τ0 "n0" args; …; doneArgs args
  --   let r ← f a0 …; pure (okResult (QueryOut.json r))
  -- Generated as nested `popArg … >>= fun pᵢ => …` so every splice sits in a
  -- term position. The argv list entering layer i is `args` (i = 0) or
  -- `Prod.snd p₍ᵢ₋₁₎`; the tail checks exhaustion against the last leftover.
  let n := binderNames.size
  let pIdent : Nat → Ident := fun i => mkIdent (Name.mkSimple s!"p{i}")
  -- One shared, unscoped `args` ident used at both the binder and its uses,
  -- so quotation hygiene cannot split them apart.
  let argsIdent : Ident := mkIdent (Name.mkSimple "args")
  let inputOf : Nat → TermElabM Term := fun i =>
    match i with
    | 0 => pure (argsIdent : Term)
    | i + 1 => `(Prod.snd $(pIdent i))
  let callArgs ← (Array.range n).mapM fun i => `(Prod.fst $(pIdent i))
  let call : Term := Syntax.mkApp (mkCIdent name) callArgs
  -- Nested `popArg … >>= fun pᵢ => …` — every splice sits in a term position.
  let mut body : Term ←
    `(LeanDb.Cli.doneArgs $(← inputOf n) >>= fun _ =>
        $call >>= fun r =>
          pure (LeanDb.Cli.okResult (LeanDb.Cli.QueryOut.json r)))
  for i in (Array.range n).reverse do
    body ← `(LeanDb.Cli.popArg $(binderTys[i]!) $(quote binderNames[i]!)
        $(← inputOf i) >>= fun $(pIdent i) => $body)
  let nameLit : Term := quote name.getString!
  let params : Term := quote ((binderNames.zip tyStrs).toList)
  let fpStx : Term ← `(LeanDb.Footprint.mk $(quote fp.tables) $(quote fp.columns) $(quote fp.residual))
  let stx ← `(LeanDb.QueryEntry.mk ($nameLit : String) ($params : List (String × String))
      $fpStx
      (fun ($argsIdent : List String) => ($body : LeanDb.DbM Lean.Json)))
  elabTerm stx none

end LeanDb.Cli
