import LeanDb.Model.DB
import Lean.Elab.Command

/-! # Requirements: running one model program on any backend

`DB`/`Query` code is written once, against the portable family (`portableStorage`, whose
evidence is `PUnit`). To run it where evidence is real (LeanDB's SQLite family), its body is
generalized over the family:

```
def Book.retire (b : Row Book) : DB Unit := Book.delete b
derive_requirements Book.retire
```

adds, next to `Book.retire` (ordinary declarations; `#check`/`#print` show them):

```
Book.retire.Requirements       : StorageResources → Type 1   -- the evidence its body demands
Book.retire.Requirements.infer : [capabilities…] → Book.retire.Requirements resources
Book.retire.portableRequirements : Book.retire.Requirements portableStorage
Book.retire.withResources      : {resources} → Book.retire.Requirements resources → {Scope} →
                                 Book.Row Scope → Program resources .command Scope Unit
```

`withResources` is `Book.retire`'s OWN elaborated body: the definitions that build it
(`Book.delete`, `DB.delete`, …) are unfolded, then `portableStorage`, its named instances
(`portableEntity`, `portableUnique`, `portableLink`, `portableColumn`) and `OpScope` are
abstracted, and the kernel re-checks the result. The requirements are exactly the typed
capabilities its storage calls demanded (`HasEntityResource resources Book`, …); nothing is
inferred from syntax. At the portable family it is the original program.

## For an operation layer

The machinery is parameterized by `Targets`, so an operation IR that embeds storage
requests reuses it with its own extended family: its portable family constant, its extra
named instances, and `portableStorage` mapped to the storage part of its family binder
(`derived := #[(``portableStorage, fun r => mkApp (mkConst ``MyResources.toStorageResources) r)]`).
`storageNode?` reads one storage request out of an unfolded body (for inspection metadata). -/

namespace LeanDb.Model.Requirements
open Lean Meta Elab Command

/-- What generalization abstracts, and into what. -/
structure Targets where
  /-- The type of the family binder (`StorageResources`, or an extension of it). -/
  familyType : Expr
  /-- The portable family the source is written against; it becomes the family binder. -/
  portable : Lean.Name
  /-- Further family constants, each replaced by an expression of the family binder (an
  extended family maps `portableStorage` to its storage part). -/
  derived : Array (Lean.Name × (Expr → Expr)) := #[]
  /-- The named portable instances; each distinct application becomes a requirement. -/
  instances : Array Lean.Name
  /-- The transaction index, abstracted to the `Scope` binder. -/
  scope : Lean.Name := ``OpScope
  /-- Only modules that import this one can mention the targets. -/
  root : Lean.Name := `LeanDb.Model.Resources

/-- LeanDB's named portable instances. -/
def portableInstances : Array Lean.Name :=
  #[``portableEntity, ``portableUnique, ``portableLink, ``portableColumn]

/-- Generalize storage programs (`DB`, `Query`) over `StorageResources`. -/
def storageTargets : Targets where
  familyType := mkConst ``StorageResources
  portable := ``portableStorage
  instances := portableInstances

def Targets.isTarget (targets : Targets) (c : Lean.Name) : Bool :=
  c == targets.portable || c == targets.scope || targets.derived.any (·.1 == c) || targets.instances.contains c

/-- Modules that (transitively) import `targets.root`; nothing else can mention the targets. -/
private def dependentModules (targets : Targets) (env : Environment) : Array Bool := Id.run do
  let names := env.header.moduleNames
  let some root := env.getModuleIdx? targets.root | return names.map fun _ => false
  let mut result : Array Bool := names.map fun _ => false
  let mut changed := true
  while changed do
    changed := false
    for i in [:names.size] do
      if result[i]! then continue
      let depends := i == root.toNat ||
        env.header.moduleData[i]!.imports.any fun imp =>
          match env.getModuleIdx? imp.module with
          | some j => result[j.toNat]!
          | none => false
      if depends then
        result := result.set! i true
        changed := true
  return result

/-- Optional-argument defaults do not make a declaration depend on the targets. -/
partial def stripDefaults (e : Expr) : Expr :=
  e.replace fun
    | .app (.app (.const ``optParam _) t) _ => some (stripDefaults t)
    | .app (.app (.const ``autoParam _) t) _ => some (stripDefaults t)
    | _ => none

/-- Does constant `c` (transitively) mention a target? -/
partial def mentionsTargets (targets : Targets) (dependent : Array Bool) (memo : IO.Ref (NameMap Bool))
    (c : Lean.Name) : MetaM Bool := do
  if targets.isTarget c then return true
  if let some known := (← memo.get).find? c then return known
  let env ← getEnv
  if let some idx := env.getModuleIdxFor? c then
    unless dependent[idx.toNat]?.getD false do
      memo.modify (·.insert c false)
      return false
  memo.modify (·.insert c false) -- cycle guard
  let some info := env.find? c | return false
  let mut used := (stripDefaults info.type).getUsedConstants
  if let some value := info.value? (allowOpaque := true) then used := used ++ value.getUsedConstants
  let mut result := false
  for d in used do
    if d != c && (← mentionsTargets targets dependent memo d) then
      result := true
      break
  memo.modify (·.insert c result)
  return result

/-- Unfold every definition that mentions a target until only constructors, generic library
code and the targets themselves remain. An opaque or partial definition on the way is an
error: its body cannot be generalized. -/
def inline (targets : Targets) (e : Expr) : MetaM Expr := do
  let dependent := dependentModules targets (← getEnv)
  let memo ← IO.mkRef ({} : NameMap Bool)
  Meta.transform e (pre := fun e => do
    match e.getAppFn with
    | .const c us =>
      if targets.isTarget c then return .continue
      unless ← mentionsTargets targets dependent memo c do return .continue
      match (← getEnv).find? c with
      | some (.defnInfo info) =>
        return .visit ((info.value.instantiateLevelParams info.levelParams us).betaRev e.getAppRevArgs)
      | some (.thmInfo info) =>
        return .visit ((info.value.instantiateLevelParams info.levelParams us).betaRev e.getAppRevArgs)
      | some info =>
        let kind := match info with
          | .opaqueInfo _ => "an opaque or partial definition"
          | .axiomInfo _ => "an axiom"
          | .thmInfo _ => "a theorem"
          | .inductInfo _ => "an inductive type"
          | .ctorInfo _ => "a constructor"
          | .recInfo _ => "a recursor"
          | .quotInfo _ => "a quotient primitive"
          | .defnInfo _ => "a definition"
        throwError "cannot generalize: `{c}` is {kind} that depends on the portable storage family; storage programs must be built from unfoldable definitions"
      | none => throwError "cannot generalize: unknown constant `{c}`"
    | _ => return .continue)

/-- Portable-instance applications occurring in `e` (closed, fully applied), each once. -/
def collectInstances (targets : Targets) (e : Expr) : MetaM (Array Expr) := do
  let mut arities : Array (Lean.Name × Nat) := #[]
  for c in targets.instances do
    let info ← getConstInfo c
    let arity ← forallTelescope info.type fun args _ => pure args.size
    arities := arities.push (c, arity)
  let found ← IO.mkRef (#[] : Array Expr)
  let rec visit (e : Expr) : StateRefT (Std.HashSet Expr) MetaM Unit := do
    if (← get).contains e then return
    modify (·.insert e)
    match e with
    | .app f a => visit f; visit a
    | .lam _ t b _ | .forallE _ t b _ => visit t; visit b
    | .letE _ t v b _ => visit t; visit v; visit b
    | .mdata _ b => visit b
    | .proj _ _ b => visit b
    | _ => pure ()
    if let .const c _ := e.getAppFn then
      if let some (_, arity) := arities.find? (·.1 == c) then
        if e.getAppNumArgs == arity then
          if e.hasLooseBVars then
            throwError "cannot generalize: storage capability `{c}` depends on a locally bound type; generalize a monomorphic definition"
          unless (← found.get).contains e do found.modify (·.push e)
  (visit e).run' {}
  found.get

/-- Replace each instance application by its binder, then the families and the scope. -/
def abstractTargets (targets : Targets) (e : Expr) (instances binders : Array Expr) (family scope : Expr) : Expr :=
  let e := e.replace fun sub => (instances.findIdx? (· == sub)).map (binders[·]!)
  e.replace fun
    | .const c _ =>
      if c == targets.portable then some family
      else if c == targets.scope then some scope
      else (targets.derived.find? (·.1 == c)).map fun (_, replacement) => replacement family
    | _ => none

/-- Order instance applications so that every one comes after those it contains. -/
partial def dependencyOrder (pending : Array Expr) (done : Array Expr := #[]) : Array Expr :=
  if pending.isEmpty then done else
  let ready := pending.filter fun a => !pending.any fun b => b != a && (a.find? (· == b)).isSome
  let ready := if ready.isEmpty then pending else ready
  dependencyOrder (pending.filter (!ready.contains ·)) (done ++ ready)

/-- Bind one instance-implicit capability per instance application, abstracting earlier ones. -/
partial def withCapabilityBinders {β : Type} (targets : Targets) (sorted : Array Expr) (family scope : Expr)
    (i : Nat) (binders : Array Expr) (k : Array Expr → MetaM β) : MetaM β := do
  if h : i < sorted.size then
    let type ← inferType sorted[i]
    let type := abstractTargets targets type (sorted.extract 0 i) binders family scope
    withLocalDecl (.mkSimple s!"capability{i}") .instImplicit type fun binder =>
      withCapabilityBinders targets sorted family scope (i + 1) (binders.push binder) k
  else k binders

/-- Run a generated declaration through the kernel and compiler. -/
def addDefinition (name : Lean.Name) (type value : Expr) : MetaM Unit := do
  let type ← instantiateMVars type
  let value ← instantiateMVars value
  if type.hasMVar || value.hasMVar then throwError "internal: unresolved metavariables in generated `{name}`"
  let hints := ReducibilityHints.regular (getMaxHeight (← getEnv) value + 1)
  addAndCompile <| .defnDecl { name, levelParams := [], type, value, hints, safety := .safe }

/-- The result of `generalize`. -/
structure Generalized where
  /-- The unfolded (still portable) body, for scanning its storage requests. -/
  inlined : Expr
  /-- How many capabilities `f.Requirements` holds. -/
  requirements : Nat

/-- Generalize definition `f` over the family of `targets`. Adds `f.Requirements`,
`f.Requirements.infer`, `f.portableRequirements` and `body` (default `f.withResources`):
`{resources} → f.Requirements resources → {Scope} → <f's type, generalized>`. -/
def generalize (targets : Targets) (f : Lean.Name) (body : Lean.Name := f ++ `withResources) :
    MetaM Generalized := do
  let info ← getConstInfo f
  unless info.levelParams.isEmpty do throwError "cannot generalize `{f}`: it is universe-polymorphic"
  let some value := info.value? | throwError "cannot generalize `{f}`: it has no definition body (opaque or partial)"
  let inlined ← inline targets value
  let inlinedType ← inline targets info.type
  let instances := (← collectInstances targets inlined) ++ (← collectInstances targets inlinedType)
  let instances := instances.foldl (fun acc i => if acc.contains i then acc else acc.push i) #[]
  -- Instances whose arguments contain other instances must come later.
  let sorted := dependencyOrder instances
  withLocalDecl `resources .implicit targets.familyType fun family => do
  withLocalDecl `Scope .implicit (mkSort Level.one) fun scope => do
  withCapabilityBinders targets sorted family scope 0 #[] fun binders => do
    let generalized := abstractTargets targets inlined sorted binders family scope
    let generalizedType := abstractTargets targets inlinedType sorted binders family scope
    let leftovers := [targets.portable, targets.scope] ++ (targets.derived.map (·.1)).toList ++ targets.instances.toList
    for leftover in leftovers do
      if generalized.getUsedConstants.contains leftover || generalizedType.getUsedConstants.contains leftover then
        throwError "cannot generalize `{f}`: its body still depends on `{leftover}` after generalization"
    -- Requirements r := (c0 : …) ×' (c1 : …) ×' … ×' PUnit
    let unitLevel := Level.one.succ
    let mut products : Array Expr := #[mkConst ``PUnit [unitLevel]]
    let mut tuples : Array Expr := #[mkConst ``PUnit.unit [unitLevel]]
    for j in [:binders.size] do
      let i := binders.size - 1 - j
      let binder := binders[i]!
      let α ← inferType binder
      let u ← getLevel α
      let rest := products.back!
      let β ← mkLambdaFVars #[binder] rest
      let v ← getLevel rest
      products := products.push (mkApp2 (mkConst ``PSigma [u, v]) α β)
      tuples := tuples.push (mkApp4 (mkConst ``PSigma.mk [u, v]) α β binder tuples.back!)
    let requirementsName := f ++ `Requirements
    addDefinition requirementsName (← mkArrow targets.familyType (mkSort Level.one.succ))
      (← mkLambdaFVars #[family] products.back!)
    addDefinition (requirementsName ++ `infer)
      (← mkForallFVars (#[family] ++ binders) (mkApp (mkConst requirementsName) family))
      (← mkLambdaFVars (#[family] ++ binders) tuples.back!)
    addDefinition (f ++ `portableRequirements) (mkApp (mkConst requirementsName) (mkConst targets.portable))
      (mkAppN (mkConst (requirementsName ++ `infer)) (#[mkConst targets.portable] ++ sorted))
    -- body {resources} (requirements) {Scope} args… := f's body[capability_i := requirements.i]
    withLocalDecl `requirements .default (mkApp (mkConst requirementsName) family) fun requirements => do
      let mut projections : Array Expr := #[]
      let mut cursor := requirements
      for _ in [:binders.size] do
        projections := projections.push (← mkAppM ``PSigma.fst #[cursor])
        cursor ← mkAppM ``PSigma.snd #[cursor]
      let value := (generalized.replaceFVars binders projections)
      let type := (generalizedType.replaceFVars binders projections)
      let value ← mkLambdaFVars #[family, requirements, scope] value
      let type ← mkForallFVars #[family, requirements, scope] type
      check value
      unless ← isDefEq (← inferType value) type do
        throwError "internal: generalized body of `{f}` does not have the generalized type"
      addDefinition body type value
    return { inlined, requirements := binders.size }

/-- One storage request in an unfolded body: its constructor (`insert`, `findBy`, …), its
access (`query` or `command`), the entity it touches, and, for writes, the identities of the
constraints it can report. -/
structure StorageNode where
  kind : String
  access : Access
  entity : String
  constraints : List String := []
  deriving Repr, BEq

private def stringLit? : Expr → Option String
  | .lit (.strVal s) => some s
  | .mdata _ e => stringLit? e
  | _ => none

/-- Identity literals of a literal `List (Constraint C)`. -/
private partial def constraintIdentities (e : Expr) : List String :=
  if e.isAppOfArity ``List.cons 3 then
    let head := e.appFn!.appArg!
    let rest := constraintIdentities e.appArg!
    if head.isAppOf ``Constraint.mk then
      match head.getAppArgs[1]? >>= stringLit? with
      | some identity => identity :: rest
      | none => rest
    else rest
  else []

/-- `e` as a storage request, if it is one (a `StorageRequest` constructor application). -/
def storageNode? (e : Expr) : MetaM (Option StorageNode) := do
  let .const c _ := e.getAppFn | return none
  unless c.getPrefix == ``StorageRequest && (← getEnv).isConstructor c do return none
  let kind := c.getString!
  let access := if ["insert", "update", "delete"].contains kind then Access.command else .query
  let args := e.getAppArgs
  let entity ← forallTelescope (← getConstInfo c).type fun binders _ => do
    let names ← binders.mapM fun b => return (← b.fvarId!.getDecl).userName
    let index := if kind == "linkField" then names.findIdx? (· == `E) else names.findIdx? (· == `T)
    match index >>= (args[·]?) with
    | some (.const t _) => return t.toString
    | _ => return ""
  let constraints := if access == .command && kind != "delete" then (args.back?.map constraintIdentities).getD [] else []
  return some { kind, access, entity, constraints }

/-- The storage requests of an unfolded body, in order of first occurrence. -/
partial def storageNodes (e : Expr) : MetaM (Array StorageNode) := do
  let out ← IO.mkRef (#[] : Array StorageNode)
  let seen ← IO.mkRef (Std.HashSet.emptyWithCapacity 64 : Std.HashSet Expr)
  let rec visit (e : Expr) : MetaM Unit := do
    if (← seen.get).contains e then return
    seen.modify (·.insert e)
    match e with
    | .app .. =>
      if let some node ← storageNode? e then out.modify (·.push node)
      visit e.getAppFn
      for arg in e.getAppArgs do visit arg
    | .lam _ _ b _ => visit b
    | .letE _ _ v b _ => visit v; visit b
    | .mdata _ b => visit b
    | .proj _ _ b => visit b
    | _ => pure ()
  visit e
  out.get

end LeanDb.Model.Requirements

namespace LeanDb.Model
open Lean Elab Command Meta

/-- `derive_requirements f, g, …`: generalize each `DB`/`Query` definition over the storage
family (see `LeanDb.Model.Requirements`). -/
syntax (name := deriveRequirementsCmd) "derive_requirements " ident,+ : command

elab_rules : command
  | `(derive_requirements $fs,*) => do
    for f in fs.getElems do
      let name ← liftCoreM <| realizeGlobalConstNoOverload f
      withRef f <| liftTermElabM do
        let info ← getConstInfo name
        let isProgram ← forallTelescope info.type fun _ result => do
          return result.isAppOf ``DB || result.isAppOf ``Query
        unless isProgram do
          throwError "derive_requirements: `{name}` must return `DB α` or `Query α`"
        discard <| Requirements.generalize Requirements.storageTargets name
end LeanDb.Model
