import LeanDb.Model.Deriving
import Lean.ReservedNameAction

/-! # Entity operations, constraints, links and `Changes`

```
constraint Customer.uniqueEmail : unique email
constraint Loan.oneActive        : unique (book, member)
```

Each entity `T` (from `deriving Entity`) has generated storage steps:

* `T.Conflict` — one constructor per unique constraint, named after it, in declaration order
  (only when `T` has unique constraints);
* `T.insert : T → DB (Except T.Conflict (Ref T))`, or `T → DB (Ref T)` without uniques;
* `T.update : Row T → T → DB (Except T.Conflict Unit)` (or `DB Unit`); only constraints over
  fields whose value changes are checked;
* `T.patch : Row T → T.Changes → DB …` with `deriving Changes`; only constraints over the
  editable fields can conflict;
* `T.find : Ref T → Query (Option (Row T))`, `T.select : Query (List (Row T))`,
  `T.delete : Row T → DB Unit` (first deleting, through their own `delete`, the rows that
  reference it through a field declared `constraint C.c : cascade field`);
* `T.findBy` — the lookup of the FIRST declared unique constraint (curried for composites);
  every constraint `c` also has `T.c.find` and `T.c.key`.

The constraint-dependent declarations are generated on first reference (Lean reserved
names), so constraints may follow the entity declaration. Declaring a
constraint after `T.insert`/`T.Conflict`/`T.findBy` were first used is an error. Generation
happens only in the module that declares `T`. Foreign-key failures never appear in
`T.Conflict`; they stay backend faults.

Other declarations: `internal T.op, …` (generated operations private to the module),
`link E.parent E.target` (a join key for `Query.linkField`), `deriving Changes` /
`deriving instance Changes (except := […]) for T`, `entity_operations T, …`. -/

namespace LeanDb.Model.Entities
open Lean Elab Command Deriving

/-- `deriving Changes (except := …)`: the entity and its editable fields, in declaration order. -/
initialize changesDeclarations : SimplePersistentEnvExtension (Lean.Name × Array Lean.Name) (Array (Lean.Name × Array Lean.Name)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl Array.append #[]
  }

/-- Generate `T.Changes` (the fields of `T` not in `except`), `T.Changes.toChange` (built only
from the generated lawful lenses) and `T.Changes.ofValue`. `T.patch` follows on first use. -/
def deriveChanges (owner : Lean.Name) (except : Array Lean.Name) : CommandElabM Unit := do
  let env ← getEnv
  unless (entityDeclarations.getState env).any (·.name == owner) do
    throwError "deriving Changes requires an entity; add `deriving Entity` first"
  if (entityRealization.getState env).1.contains owner then
    throwError "deriving Changes for {owner} must come before its generated operations are first used"
  let fields := getStructureFields env owner
  for field in except do
    unless fields.contains field do throwError "deriving Changes: {owner} has no field `{field}` (fields: {fields.toList})"
  let mut editable : Array (Lean.Name × String) := #[]
  for field in fields do
    if except.contains field then continue
    let type ← liftTermElabM <| Meta.forallTelescopeReducing (← getConstInfo (owner ++ field)).type fun _ body => do
      return some (← Deriving.sourceOf body)
    if let some type := type then editable := editable.push (field, type)
  if editable.isEmpty then throwError "deriving Changes: every field of {owner} is excluded"
  let ty := full owner
  let changes := full (owner ++ `Changes)
  runCommand ("structure " ++ changes ++ " where\n  " ++ String.intercalate "\n  " (editable.toList.map fun (f, t) => f.toString ++ " : " ++ t) ++
    "\n  deriving LeanDb.Model.Domain")
  let sets := editable.toList.map fun (f, _) =>
    "(LeanDb.Model.Change.set (T := " ++ ty ++ ") (field := " ++ quoted f.toString ++ ") changes." ++ f.toString ++ ")"
  let merged := sets.tail.foldl (fun acc next => "(LeanDb.Model.Change.andThen " ++ acc ++ " " ++ next ++ ")") sets.head!
  runCommand ("def " ++ changes ++ ".toChange (changes : " ++ changes ++ ") : LeanDb.Model.Change " ++ ty ++ " := " ++ merged)
  runCommand ("def " ++ changes ++ ".ofValue (value : " ++ ty ++ ") : " ++ changes ++ " := { " ++
    String.intercalate ", " (editable.toList.map fun (f, _) => f.toString ++ " := value." ++ f.toString) ++ " }")
  modifyEnv fun env => changesDeclarations.addEntry env (owner, editable.map (·.1))

/-- Generate every constraint-dependent operation of entity `T` at once. -/
def generateEntityOperations (owner : Lean.Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains (owner ++ `Row) do
    throwError "entity {owner} has no row view (an entity field named `id` is reserved for the row identity)"
  let uniques := (constraintDeclarations.getState env).filter (·.owner == owner)
  let ty := full owner
  let row := "(" ++ full (owner ++ `Row) ++ " LeanDb.Model.OpScope)"
  let id := "(Ontology.Ref " ++ ty ++ ")"
  let decl := fun (stem : String) => (if isPrivateOperation env owner stem then "private def " else "def ") ++ ty ++ "." ++ stem
  if uniques.isEmpty then
    runCommand (decl "insert" ++ " : " ++ ty ++ " → LeanDb.Model.DB " ++ id ++ " := fun value => LeanDb.Model.DB.insertTotal value")
    runCommand (decl "update" ++ " : " ++ row ++ " → " ++ ty ++ " → LeanDb.Model.DB Unit := fun row value => LeanDb.Model.DB.updateTotal (T := " ++ ty ++ ") row value")
  else
    let conflict := ty ++ ".Conflict"
    runCommand ("inductive " ++ conflict ++ " where " ++ String.intercalate " " (uniques.toList.map fun u => "| " ++ u.name.toString))
    enumInstances (owner ++ `Conflict) (uniques.toList.map (·.name.toString)) (decidable := true)
    let conflicts := "([" ++ String.intercalate ", " (uniques.toList.map fun u =>
      "{ identity := " ++ quoted (owner ++ u.name).toString ++ ", fields := [" ++
      String.intercalate ", " (u.fields.toList.map fun f => quoted f.toString) ++ "], publicFailure := " ++ conflict ++ "." ++ u.name.toString ++ " }") ++
      "] : List (LeanDb.Model.Constraint " ++ conflict ++ "))"
    runCommand (decl "insert" ++ " : " ++ ty ++ " → LeanDb.Model.DB (Except " ++ conflict ++ " " ++ id ++ ") := fun value => LeanDb.Model.DB.insert value " ++ conflicts)
    runCommand (decl "update" ++ " : " ++ row ++ " → " ++ ty ++ " → LeanDb.Model.DB (Except " ++ conflict ++ " Unit) := fun row value => LeanDb.Model.DB.update (T := " ++ ty ++ ") row value " ++ conflicts)
  -- `T.patch` (with `deriving Changes`): only constraints over the editable fields can conflict.
  if let some (editable : Array Lean.Name) := (changesDeclarations.getState env).find? (·.1 == owner) |>.map (·.2) then
    let touched := uniques.filter fun u => u.fields.any editable.contains
    let changes := full (owner ++ `Changes)
    if touched.isEmpty then
      runCommand (decl "patch" ++ " : " ++ row ++ " → " ++ changes ++ " → LeanDb.Model.DB Unit := fun row changes => LeanDb.Model.DB.patchTotal (T := " ++ ty ++ ") row changes.toChange")
    else
      let conflict := ty ++ ".Conflict"
      let conflicts := "([" ++ String.intercalate ", " (touched.toList.map fun u =>
        "{ identity := " ++ quoted (owner ++ u.name).toString ++ ", fields := [" ++
        String.intercalate ", " (u.fields.toList.map fun f => quoted f.toString) ++ "], publicFailure := " ++ conflict ++ "." ++ u.name.toString ++ " }") ++
        "] : List (LeanDb.Model.Constraint " ++ conflict ++ "))"
      runCommand (decl "patch" ++ " : " ++ row ++ " → " ++ changes ++ " → LeanDb.Model.DB (Except " ++ conflict ++ " Unit) := fun row changes => LeanDb.Model.DB.patch (T := " ++ ty ++ ") row changes.toChange " ++ conflicts)
  runCommand (decl "find" ++ " : " ++ id ++ " → LeanDb.Model.Query (Option " ++ row ++ ") := fun id => LeanDb.Model.Query.find (T := " ++ ty ++ ") id")
  runCommand (decl "select" ++ " : LeanDb.Model.Query (List " ++ row ++ ") := LeanDb.Model.Query.select (T := " ++ ty ++ ")")
  -- Cascades onto this entity: delete the referencing rows (through their own `delete`, so
  -- cascades chain) before the row itself.
  let cascades := (cascadeDeclarations.getState env).filter (·.target == owner)
  let children := cascades.toList.map fun c =>
    "  for child in (← LeanDb.Model.Query.select (T := " ++ full c.owner ++ ")) do\n    if child." ++ c.field.toString ++
      " == row.id then " ++ full (c.owner ++ `delete) ++ " child\n"
  runCommand (decl "delete" ++ " : " ++ row ++ " → LeanDb.Model.DB Unit := fun row => do\n" ++ String.join children ++
    "  LeanDb.Model.DB.delete (T := " ++ ty ++ ") row")

/-- Realize `T`'s generated operations (reserved-name action body). -/
def realizeEntity (owner : Lean.Name) : CoreM Unit := do
  modifyEnv (entityRealization.modifyState · fun (done, active) => (done, owner :: active))
  try
    liftCommandElabM (generateEntityOperations owner)
  finally
    modifyEnv (entityRealization.modifyState · fun (done, active) => (done.insert owner, active.erase owner))

initialize
  registerReservedNameAction fun name => do
    let some owner := entityOpOwner? (← getEnv) name | return false
    realizeEntity owner
    return true

/-- Generated conflict types, for `#print`. -/
def isConflictType (env : Environment) (name : Lean.Name) : Bool :=
  match name with
  | .str owner "Conflict" => (constraintDeclarations.getState env).any (·.owner == owner)
  | _ => false

end LeanDb.Model.Entities

namespace LeanDb.Model
open Lean Elab Command

/-- `constraint T.name : unique field` / `constraint T.name : unique (f₁, f₂)`, optionally
`private constraint …` (its lookups `T.name.find`/`T.findBy` are then private to the module).
Parsed with a leading identifier so `constraint` stays usable as an ordinary name. -/
syntax (name := constraintDecl) ("private ")? withPosition(ident colGt ident colGt " : " colGt &"unique" colGt (ident <|> ("(" ident,+ ")"))) : command

/-- `constraint C.name : cascade field`: deleting what `C.field` references deletes the
referencing `C` rows. Without it a referenced row cannot be deleted while referenced. -/
syntax (name := cascadeDecl) withPosition(ident colGt ident colGt " : " colGt &"cascade" colGt ident) : command

@[command_elab cascadeDecl] def elabCascade : CommandElab := fun stx => do
  unless stx[0].getId == `constraint do throwErrorAt stx[0] "unexpected identifier; expected command"
  let target := stx[1]
  let name := target.getId
  if name.getPrefix.isAnonymous then throwErrorAt target "constraint name must be Entity.name"
  let owner ← liftCoreM <| realizeGlobalConstNoOverload (mkIdentFrom target name.getPrefix)
  let env ← getEnv
  unless (Deriving.entityDeclarations.getState env).any (·.name == owner) do
    throwErrorAt target "{owner} is not an entity; add `deriving Entity`"
  let field := stx[4].getId
  unless (getStructureFields env owner).contains field do throwErrorAt stx[4] "{owner} has no field `{field}`"
  let type ← liftTermElabM <| Meta.forallTelescopeReducing (← getConstInfo (owner ++ field)).type fun _ body => Meta.whnfR body
  unless type.isAppOfArity ``Ontology.EntityId 1 do throwErrorAt stx[4] "`{field}` must have type `Ref T` to cascade"
  let .const parent _ := type.appArg! | throwErrorAt stx[4] "`{field}` must reference an entity"
  if (Deriving.entityRealization.getState env).1.contains parent then
    throwErrorAt target "cascade {name} must be declared before {parent}.delete is first used"
  if (env.getModuleIdxFor? parent).isSome then
    throwErrorAt target "cascade {name}: {parent} is declared in another module; declare the cascade there"
  modifyEnv fun env => Deriving.cascadeDeclarations.addEntry env
    { owner, name := Lean.Name.mkSimple name.getString!, field, target := parent }

@[command_elab constraintDecl] def elabConstraint : CommandElab := fun stx => do
  let isPrivate := stx[0].getNumArgs > 0
  let kw := stx[1]
  let target := stx[2]
  let fieldsStx := stx[5]
  unless kw.getId == `constraint do throwErrorAt kw "unexpected identifier; expected command"
  let fields := if fieldsStx.isIdent then #[fieldsStx.getId] else fieldsStx[1].getSepArgs.map (·.getId)
  let name := target.getId
  if name.getPrefix.isAnonymous then throwErrorAt target "constraint name must be Entity.name"
  let owner ← liftCoreM <| realizeGlobalConstNoOverload (mkIdentFrom target name.getPrefix)
  unless (Deriving.entityDeclarations.getState (← getEnv)).any (·.name == owner) do
    throwErrorAt target "{owner} is not an entity; add `deriving Entity`"
  let constraintName := Lean.Name.mkSimple name.getString!
  withRef target <| Deriving.declareUniqueConstraint owner constraintName fields isPrivate
  -- The constraint itself: a single-field `Unique T V` (what the native schema bridge reads,
  -- identity `T.name`), or the composite `UniqueKey`.
  let base := Deriving.full (owner ++ constraintName)
  if h : fields.size = 1 then
    let path := Deriving.full (owner ++ Lean.Name.mkSimple (fields[0].toString ++ "Path"))
    Deriving.runCommand ("def " ++ base ++ " := LeanDb.Model.Unique.mk (T := " ++ Deriving.full owner ++ ") " ++
      Deriving.quoted (owner ++ constraintName).toString ++ " " ++ path)
  else
    Deriving.runCommand ("def " ++ base ++ " := " ++ base ++ ".key")

/-- Generate the operations of the listed entities now (normally they are generated on first
use). Use it in the declaring module for an entity whose operations are first used only in
importing modules: generation is module-local, so importers never duplicate it. -/
syntax (name := entityOperationsCmd) "entity_operations " ident,+ : command

elab_rules : command
  | `(entity_operations $entities,*) => do
    for entity in entities.getElems do
      let owner ← liftCoreM <| realizeGlobalConstNoOverload entity
      let env ← getEnv
      unless (Deriving.entityDeclarations.getState env).any (·.name == owner) do
        throwErrorAt entity "{owner} is not an entity; add `deriving Entity`"
      if (env.getModuleIdxFor? owner).isSome then
        throwErrorAt entity "{owner} is declared in another module; generate its operations there"
      unless (Deriving.entityRealization.getState env).1.contains owner do
        liftCoreM <| Entities.realizeEntity owner

/-- `#print T.Conflict` shows the generated type in the source form it was declared from. -/
elab_rules : command
  | `(#print%$tk $id:ident) => do
    let some name ← (try some <$> liftCoreM (realizeGlobalConstNoOverload id) catch _ => pure none)
      | throwUnsupportedSyntax
    unless Entities.isConflictType (← getEnv) name do throwUnsupportedSyntax
    let info ← getConstInfoInduct name
    let ctors := info.ctors.map fun ctor => "\n  | " ++ ctor.getString!
    logInfoAt tk m!"inductive {.ofConstName name} where{String.join ctors}"

end LeanDb.Model

namespace LeanDb.Model.Deriving
open Lean Elab Command Meta

initialize registerDerivingHandler ``LeanDb.Model.Changes fun names => do
  for name in names do Entities.deriveChanges name #[]
  return true

end LeanDb.Model.Deriving

namespace LeanDb.Model.Entities
open Lean Elab Command

/-- `internal Loan.select, Loan.insert, Book.update`: these generated operations are private to
this (the domain) module: raw table access stays where the rules are. Lean's structure
`deriving` clause takes only class names, so the option is its own command; it must come before
the operations are first used (and before the first constraint, for `findBy`). Parsed with a
leading identifier so `internal` stays an ordinary name. -/
syntax (name := internalOperations) withPosition(ident colGt ident,+) : command

@[command_elab internalOperations] def elabInternalOperations : CommandElab := fun stx => do
  unless stx[0].getId == `internal do throwErrorAt stx[0] "unexpected identifier; expected command"
  for target in stx[1].getSepArgs do
    let name := target.getId
    if name.getPrefix.isAnonymous then throwErrorAt target "expected Entity.operation, e.g. `Loan.select`"
    let owner ← liftCoreM <| realizeGlobalConstNoOverload (mkIdentFrom target name.getPrefix)
    unless (Deriving.entityDeclarations.getState (← getEnv)).any (·.name == owner) do
      throwErrorAt target "{owner} is not an entity; add `deriving Entity`"
    withRef target <| Deriving.setPrivateOperations owner [name.getString!]

/-- Field `field` of entity `owner`, with its (reducible-unfolded) type. -/
private def entityField (target : Syntax) : CommandElabM (Lean.Name × Lean.Name × Expr) := do
  let name := target.getId
  if name.getPrefix.isAnonymous then throwErrorAt target "expected Entity.field, e.g. `Loan.member`"
  let owner ← liftCoreM <| realizeGlobalConstNoOverload (mkIdentFrom target name.getPrefix)
  unless (Deriving.entityDeclarations.getState (← getEnv)).any (·.name == owner) do
    throwErrorAt target "{owner} is not an entity; add `deriving Entity`"
  let field := Lean.Name.mkSimple name.getString!
  unless (getStructureFields (← getEnv) owner).contains field do
    throwErrorAt target "{owner} has no field `{field}`"
  let type ← liftTermElabM <| Meta.forallTelescopeReducing (← getConstInfo (owner ++ field)).type fun _ body => Meta.whnfR body
  return (owner, field, type)

/-- The entity a `Ref P` field points to. -/
private def referenceTarget (target : Syntax) (type : Expr) : CommandElabM Lean.Name := do
  unless type.isAppOfArity ``Ontology.EntityId 1 do throwErrorAt target "`{target.getId}` must have type `Ref T`"
  let .const profile _ := type.appArg! | throwErrorAt target "`{target.getId}` must reference an entity"
  return profile

/-- `link E.parent E.target`: a join through edge entity `E` from the entity its `parent` field
references to the one its `target` field references, as `E.link.parent.target : LinkKey E P T`
(for `Query.linkField`). -/
private def declareLink (parentField targetField : Syntax) : CommandElabM Unit := do
  let (owner, parent, parentType) ← entityField parentField
  let (owner', target, targetType) ← entityField targetField
  unless owner == owner' do throwErrorAt targetField "both fields must belong to the same edge entity"
  if parent == target then throwErrorAt targetField "a link joins two different reference fields"
  let parentEntity ← referenceTarget parentField parentType
  let targetEntity ← referenceTarget targetField targetType
  let key := owner ++ `link ++ parent ++ target
  Deriving.runCommand ("def " ++ Deriving.full key ++ " : LeanDb.Model.LinkKey " ++ Deriving.full owner ++ " " ++ Deriving.full parentEntity ++ " " ++ Deriving.full targetEntity ++
    " := { identity := " ++ Deriving.quoted (owner.toString ++ "." ++ parent.toString ++ "." ++ target.toString) ++
    ", parent := " ++ Deriving.full (owner ++ parent) ++ ", target := " ++ Deriving.full (owner ++ target) ++ " }")

/-- `link E.parent E.target`, identifier-led like `constraint`. Another layer can give the
same shape its own keyword (e.g. an operation layer's `credential C.profile C.hash`) with one
more `@[command_elab LeanDb.Model.Entities.entityFieldPair]` elaborator: this one claims only
`link`. -/
syntax (name := entityFieldPair) withPosition(ident colGt ident colGt ident) : command

@[command_elab entityFieldPair] def elabEntityFieldPair : CommandElab := fun stx => do
  match stx[0].getId with
  | `link => declareLink stx[1] stx[2]
  | _ => throwUnsupportedSyntax

private def exceptList (arg : Syntax) : Option (Array Lean.Name) := do
  guard (arg.isOfKind ``Lean.Parser.Term.namedArgument && arg[1].getId.toString == "except")
  let list := arg[3]
  guard (list.isOfKind ``«term[_]»)
  let items := list[1].getSepArgs
  guard (items.all (·.isIdent))
  pure (items.map (·.getId))

/-- `deriving instance Changes (except := [owner, createdAt]) for Order`: `Order.Changes` holds the
other fields; an edit through it cannot touch the excluded ones. (`deriving Changes` in the
structure itself takes every field.) -/
@[command_elab Lean.Parser.Command.deriving] def elabChangesExcept : CommandElab := fun stx => do
  match stx with
  | `(deriving instance $[$classes],* for $[$decls],*) =>
    let mut except? : Option (Array Lean.Name) := none
    for cls in classes do
      let term := cls.raw[1]
      unless term.isOfKind ``Lean.Parser.Term.app && term[0].isIdent && term[0].getId.getString! == "Changes" &&
          term[1].getNumArgs == 1 do throwUnsupportedSyntax
      let some fields := exceptList term[1][0] | throwUnsupportedSyntax
      except? := some fields
    let some except := except? | throwUnsupportedSyntax
    for decl in decls do
      let owner ← liftCoreM <| realizeGlobalConstNoOverload decl
      withRef decl <| deriveChanges owner except
  | _ => throwUnsupportedSyntax

end LeanDb.Model.Entities
