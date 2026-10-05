import LeanDb.Model.DB
import Lean.Elab.Deriving.Basic

/-! # `deriving Domain` and `deriving Entity`

For a record `T` (all generated declarations are ordinary; `#print` shows them):

* field paths `T.<field>Path` and lawful lenses (`EditableField T "<field>" V`);
* the `Domain`/`Entity` instance: wire name, field metadata, and for an entity the row
  representation (each field through its `StorageCodec`); a `Domain` record also gets `Wire`;
* for an entity: the row view `T.Row Scope` (extends `T` with `id : Ref T`, `HasRow`);
* `T.Field`, `HasRecord T`, `NamedField`, `T.wireDefaults`.

A payload-free inductive gets `Domain` and an enum `Wire` codec. Value types declared in the
same module and reached from a derived record get `Wire` the same way (closed variants with
named payload fields included). Anything else needs `represent`.

The entity's storage operations (`T.insert`, `T.find`, …) are generated on first use
(`LeanDb.Model.Entities`). -/

namespace LeanDb.Model.Deriving
open Lean Meta Elab Command

structure EntityDeclaration where
  name : Lean.Name
  /-- Field names and their printed types, in declaration order. -/
  fields : Array (String × String)
  deriving Inhabited

initialize entityDeclarations : SimplePersistentEnvExtension EntityDeclaration (Array EntityDeclaration) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl Array.append #[]
  }

initialize enumDeclarations : SimplePersistentEnvExtension Lean.Name (Array Lean.Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl Array.append #[]
  }

/-- A declared unique constraint (`constraint T.name : unique …`). -/
structure ConstraintEntry where
  owner : Lean.Name
  name : Lean.Name
  fields : Array Lean.Name
  /-- `private constraint …`: its lookups (`T.c.find`, `T.findBy`) are private to the module. -/
  isPrivate : Bool := false
  deriving Inhabited

/-- Generated entity operations (`insert`, `find`, `findBy`, `update`, `delete`, `select`)
declared private to the entity's module (`internal T.op`). -/
initialize privateOperations : SimplePersistentEnvExtension (Lean.Name × String) (Array (Lean.Name × String)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl Array.append #[]
  }

initialize constraintDeclarations : SimplePersistentEnvExtension ConstraintEntry (Array ConstraintEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl Array.append #[]
  }

/-- Entities whose generated operations (`insert`, `find`, `Conflict`, …) already exist,
and the entity currently being realized (its names are then not reserved). -/
initialize entityRealization : EnvExtension (NameSet × List Lean.Name) ←
  registerEnvExtension (pure ({}, []))

/-- `constraint C.name : cascade field`: deleting the row of entity `target` that `C.field`
references deletes the referencing `C` rows. Persistent, read by native schema derivation
(`native_schema%`); the generated `target.delete` honors it on every backend. -/
structure CascadeEntry where
  owner : Lean.Name
  name : Lean.Name
  field : Lean.Name
  target : Lean.Name
  deriving Inhabited

initialize cascadeDeclarations : SimplePersistentEnvExtension CascadeEntry (Array CascadeEntry) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := Array.push
    addImportedFn := fun entries => entries.foldl Array.append #[]
  }

private def entityOpStems : List String := ["insert", "find", "update", "delete", "select", "patch", "Conflict"]

private def isLocalEntity (env : Environment) (name : Lean.Name) : Bool :=
  (env.getModuleIdxFor? name).isNone && (entityDeclarations.getState env).any (·.name == name)

def isPrivateOperation (env : Environment) (owner : Lean.Name) (stem : String) : Bool :=
  (privateOperations.getState env).contains (owner, stem)

/-- `T` when `name` is one of local entity `T`'s generated, not yet realized operations, in
the visibility it will be declared with (a private operation is reserved only under its
private name: Lean resolves an exact public name before trying the private one). -/
def entityOpOwner? (env : Environment) (name : Lean.Name) : Option Lean.Name :=
  let (name, wasPrivate) := match privateToUserName? name with
    | some user => (user, true)
    | none => (name, false)
  let state := entityRealization.getState env
  let rec go : Lean.Name → Option Lean.Name
    | .str pre component =>
      if entityOpStems.contains component && isLocalEntity env pre &&
          !state.1.contains pre && !state.2.contains pre then
        if wasPrivate == isPrivateOperation env pre component then some pre else none
      else go pre
    | _ => none
  go name

initialize reservedPredicateInstalled : EnvExtension Bool ← registerEnvExtension (pure false)

/-- Reserved-name predicates are snapshotted when an environment is created, before
imported initializers run; install ours into this module's environment directly. -/
def installEntityReservedNames : CommandElabM Unit := do
  unless reservedPredicateInstalled.getState (← getEnv) do
    modifyEnv fun env =>
      let env := reservedNamePredicatesExt.modifyState env (·.push fun env name => (entityOpOwner? env name).isSome)
      reservedPredicateInstalled.setState env true

def runCommand (source : String) : CommandElabM Unit := do
  let env ← getEnv
  match Parser.runParserCategory env `command source with
  | .error message => throwError "Domain generation failed: {message}\n{source}"
  | .ok stx => elabCommand stx

def full (name : Lean.Name) : String := "_root_." ++ name.toString
def quoted (text : String) : String := (Lean.Json.str text).compress

/-- Authoring aliases (`Time`) are printed as their underlying nominal types so generated
source re-elaborates in any scope. -/
def printable (e : Expr) : Expr := e.replace fun
  | .const `LeanDb.Model.Time _ => some (mkConst `Ontology.Instant)
  | _ => none

/-- Re-elaborable source for a closed type: full names, no notation/unexpanders, so it
means the same thing in any scope (including inside `liftCommandElabM`). -/
def sourceOf (e : Expr) : MetaM String := do
  let fmt ← withOptions (fun o => (o.setBool `pp.fullNames true).setBool `pp.notation false) <| ppExpr e
  return fmt.pretty 100000

/-- `BEq` (or `DecidableEq`) and `Repr` for a generated payload-free inductive `name`, as
declarations named in its own namespace (`T.Field.instBEq`, `T.Field.instRepr`). A `deriving`
clause would name them after the type's last component in the CURRENT namespace
(`instReprField`), so two modules that each declare an entity at the same level could not be
imported together. -/
def enumInstances (name : Lean.Name) (ctors : List String) (decidable : Bool := false) : CommandElabM Unit := do
  let ty := full name
  if decidable then
    let arms := ctors.flatMap fun a => ctors.map fun b =>
      "| ." ++ a ++ ", ." ++ b ++ " => " ++ (if a == b then "isTrue rfl" else "isFalse (fun h => nomatch h)")
    runCommand ("instance " ++ ty ++ ".instDecidableEq : DecidableEq " ++ ty ++ " := fun a b => match a, b with " ++ String.intercalate " " arms)
  else
    let index := "(match value with " ++ String.intercalate " " ((List.range ctors.length).zip ctors |>.map fun (i, c) => "| ." ++ c ++ " => " ++ toString i) ++ ")"
    runCommand ("instance " ++ ty ++ ".instBEq : BEq " ++ ty ++ " := ⟨fun a b => (fun value => " ++ index ++ ") a == (fun value => " ++ index ++ ") b⟩")
  let reprs := ctors.map fun c => "| ." ++ c ++ " => " ++ quoted (name.toString ++ "." ++ c)
  runCommand ("instance " ++ ty ++ ".instRepr : Repr " ++ ty ++ " := ⟨fun value _ => match value with " ++ String.intercalate " " reprs ++ "⟩")

private def isEntityDeclaration (env : Environment) (name : Lean.Name) : Bool :=
  (entityDeclarations.getState env).any (·.name == name)

private def hasWire (ty : Expr) : CommandElabM Bool := liftTermElabM do
  return (← Meta.synthInstance? (mkApp (mkConst ``Ontology.Wire) ty)).isSome

mutual
/-- Value types reachable from a derived record/variant (and from published operations)
that are declared in this module without a wire codec get one derived here. Imported and
entity types are never touched. -/
partial def ensureWire (ty : Expr) (visiting : NameSet := {}) : CommandElabM Unit := do
  if ← hasWire ty then return
  let env ← getEnv
  for c in ty.getUsedConstants do
    if visiting.contains c || (env.getModuleIdxFor? c).isSome || isEntityDeclaration env c then continue
    let some (.inductInfo info) := env.find? c | continue
    unless info.numParams == 0 && info.numIndices == 0 && info.levelParams.isEmpty do continue
    unless ← hasWire (mkConst c) do
      deriveOne c false (allowPayload := true) (visiting := visiting.insert c)

partial def deriveOne (name : Lean.Name) (entity : Bool) (allowPayload : Bool := false)
    (visiting : NameSet := {}) : CommandElabM Unit := do
  let env ← getEnv
  let info ← getConstInfoInduct name
  unless info.numParams == 0 && info.numIndices == 0 && info.levelParams.isEmpty do
    throwError "deriving Domain supports only nondependent, monomorphic declarations; provide a checked representation adapter for {name} (declare `represent T as R by enc checked dec`)"
  let ty := full name
  let identity := "{ packageName := \"domain\", name := " ++ quoted name.toString ++ " }"
  if isStructure env name then
    unless (getStructureParentInfo env name).isEmpty do
      throwError "inherited Domain record {name} needs a checked representation adapter (declare `represent T as R by enc checked dec`)"
    let fields := getStructureFields env name
    if fields.isEmpty then throwError "Domain record {name} must have at least one field"
    let mut metadata : Array String := #[]
    let mut codec := "(Ontology.RecordFields.pure " ++ ty ++ ".mk)"
    let mut fieldTypes : Array String := #[]
    let mut defaults : Array String := #[]
    for field in fields do
      let proj := name ++ field
      let fieldExpr ← liftTermElabM <| forallTelescopeReducing (← getConstInfo proj).type fun args body => do
        unless args.size == 1 && !body.hasFVar do
          throwError "dependent or inherited field {proj} needs a checked representation adapter (declare `represent T as R by enc checked dec`)"
        return body
      unless fieldExpr.isConstOf ``Ontology.PasswordHash do
        ensureWire fieldExpr (visiting.insert name)
      let type ← liftTermElabM do return (← ppExpr (printable fieldExpr)).pretty
      fieldTypes := fieldTypes.push type
      let defaultFn := getDefaultFnForField? env name field
      let defaulted := defaultFn.isSome
      if let some fn := defaultFn then
        let constant ← liftTermElabM <| forallTelescopeReducing (← getConstInfo fn).type fun args _ => pure args.isEmpty
        unless constant do throwError "dependent default for {proj} needs a checked default adapter"
        let enumTag? ← liftTermElabM do
          let defaultType ← inferType (mkConst fn)
          if (enumDeclarations.getState (← getEnv)).contains defaultType.getAppFn.constName! then
            let value ← whnf (mkConst fn)
            if let .const ctor _ := value then return some ctor.getString!
            throwError "closed enum default for {proj} must reduce to a constructor"
          return none
        let encoded := if let some tag := enumTag? then "Lean.Json.str " ++ quoted tag
          else "LeanDb.Model.encodeDefault (Ontology.Wire.codec (α := " ++ type ++ ")) " ++ full fn
        -- The alternate constant representation must match the SAME codec definitionally.
        runCommand ("theorem " ++ ty ++ "." ++ field.toString ++ "DefaultEncoding : (" ++ encoded ++ ") = (Ontology.Wire.codec (α := " ++ type ++ ")).encode " ++ full fn ++ " := by rfl")
        defaults := defaults.push ("(" ++ quoted field.toString ++ ", " ++ encoded ++ ")")
      let defaultJson := defaultFn.map (fun fn => "some " ++ quoted fn.toString) |>.getD "none"
      metadata := metadata.push ("{ name := " ++ quoted field.toString ++
        ", kind := LeanDb.Model.FieldType.kind (T := " ++ type ++ "), editor := LeanDb.Model.FieldType.editor (T := " ++ type ++ "), hasDefault := " ++ toString defaulted ++ ", defaultDeclaration := " ++ defaultJson ++ " }")
      codec := "(" ++ codec ++ ").apply (Ontology.RecordFields.field " ++ quoted field.toString ++
        (if entity then " LeanDb.Model.StorageCodec.codec " else " Ontology.Wire.codec ") ++ full proj ++ ")"

    for i in [:fields.size] do
      let field := fields[i]!
      let fieldName := quoted field.toString
      let fieldType := fieldTypes[i]!
      let pathName := full (name ++ Lean.Name.mkSimple (field.toString ++ "Path"))
      runCommand ("def " ++ pathName ++ " : Ontology.FieldPath " ++ ty ++ " (" ++ fieldType ++ ") := Ontology.FieldPath.field " ++ identity ++ " " ++ fieldName ++ " " ++ full (name ++ field))
      runCommand ("instance : LeanDb.Model.EditableField " ++ ty ++ " " ++ fieldName ++ " (" ++ fieldType ++ ") := { lens := { toFieldPath := " ++ pathName ++ ", set := fun source value => { source with " ++ field.toString ++ " := value } }, laws := ⟨(by intros; rfl), (by intro source; cases source; rfl), (by intros; rfl)⟩ }")
    let domainBase := "{ typeId := " ++ identity ++ ", isEntity := " ++ toString entity ++
      ", fields := [" ++ String.intercalate ", " metadata.toList ++ "] }"
    if entity then
      runCommand ("instance : LeanDb.Model.Entity " ++ ty ++ " := { toDomain := " ++ domainBase ++ ", recordRepresentation := LeanDb.Model.recordCodec " ++ identity ++ " (" ++ codec ++ "), entityOnly := rfl }")
    else
      runCommand ("instance : LeanDb.Model.Domain " ++ ty ++ " := " ++ domainBase)
      runCommand ("instance : Ontology.Wire " ++ ty ++ " := ⟨LeanDb.Model.recordCodec " ++ identity ++ " (" ++ codec ++ ")⟩")
    if entity then
      installEntityReservedNames
      modifyEnv fun env => entityDeclarations.addEntry env
        ⟨name, ((List.range fields.size).map fun i => (fields[i]!.toString, fieldTypes[i]!)).toArray⟩
    -- Row view: `Row T` = `T.Row OpScope`, extending `T` with its `id`.
    if entity && !(fields.contains `id) then
      let short := name.getString!
      let rowTy := full (name ++ `Row)
      runCommand ("structure " ++ rowTy ++ " (Scope : Type) extends " ++ ty ++ " where\n  private mk ::\n  id : Ontology.Ref " ++ ty)
      runCommand ("instance : LeanDb.Model.HasRow " ++ ty ++ " " ++ rowTy ++ " := { ofRow := fun row => { to" ++ short ++ " := row.value, id := row.id }, toRow := fun row => LeanDb.Model.Trusted.row row.id row.to" ++ short ++ " }")
      runCommand ("@[app_unexpander " ++ rowTy ++ "] def " ++ rowTy ++ ".unexpandView : Lean.PrettyPrinter.Unexpander\n  | `($_ $scope:ident) => if scope.getId.getString! == \"OpScope\" then `(Row $(Lean.mkIdent " ++ "`" ++ short ++ ")) else throw ()\n  | _ => throw ()")
    -- A closed field type gives forms typed field names while reusing RecordDescriptor.
    runCommand ("inductive " ++ ty ++ ".Field where " ++ String.intercalate " " (fields.toList.map fun f => "| " ++ f.toString))
    enumInstances (name ++ `Field) (fields.toList.map (·.toString))
    let fieldNames := fields.toList.map fun f => quoted f.toString
    let mut values : Array String := #[]
    let mut getters : Array String := #[]
    let mut descriptors : Array String := #[]
    for i in [:fields.size] do
      let branch := "| " ++ ty ++ ".Field." ++ fields[i]!.toString ++ " => "
      values := values.push (branch ++ fieldTypes[i]!)
      getters := getters.push (branch ++ full (name ++ fields[i]!))
      descriptors := descriptors.push (branch ++ "{ identity := { packageName := \"domain\", name := " ++ quoted fieldTypes[i]! ++ " }, displayName := " ++ quoted fields[i]!.toString ++ " }")
    let cases := fields.toList.map fun f => ty ++ ".Field." ++ f.toString
    let branches := fun (xs : Array String) => String.intercalate " " xs.toList
    let fieldNamesFn := String.intercalate " " ((List.range fields.size).map fun i => "| " ++ cases[i]! ++ " => " ++ fieldNames[i]!)
    runCommand ("def " ++ ty ++ ".wireDefaults : List (String × Lean.Json) := [" ++ String.intercalate ", " defaults.toList ++ "]")
    runCommand ("instance : LeanDb.Model.HasRecord " ++ ty ++ " := { record := { identity := " ++ identity ++
      ", Field := " ++ ty ++ ".Field, Value := (fun i => match i with " ++ branches values ++
      "), fields := [" ++ String.intercalate ", " cases ++ "], fieldName := (fun i => match i with " ++ fieldNamesFn ++
      "), valueDescriptor := (fun i => match i with " ++ branches descriptors ++
      "), get := (fun i => match i with " ++ branches getters ++ ") }, fieldMetadata := [" ++ String.intercalate ", " metadata.toList ++ "] , defaultValues := " ++ ty ++ ".wireDefaults }")
    for field in fields do
      runCommand ("instance : LeanDb.Model.NamedField " ++ ty ++ " " ++ quoted field.toString ++ " := ⟨" ++ ty ++ ".Field." ++ field.toString ++ "⟩")

  else
    if entity then throwError "deriving Entity requires a structure"
    let payloads ← info.ctors.anyM fun ctorName => do return (← getConstInfoCtor ctorName).numFields != 0
    if payloads && allowPayload then
      deriveVariant name info.ctors identity visiting
      return
    modifyEnv fun env => enumDeclarations.addEntry env name
    let mut cases : Array String := #[]
    let mut entries : Array String := #[]
    let mut branches : Array String := #[]
    for ctorName in info.ctors do
      let ctor ← getConstInfoCtor ctorName
      unless ctor.numFields == 0 do
        throwError "deriving Domain currently supports payload-free closed enums; {ctorName} requires a checked representation adapter (declare `represent T as R by enc checked dec`)"
      let tag := ctorName.getString!
      cases := cases.push (quoted tag)
      entries := entries.push ("(" ++ quoted tag ++ ", " ++ full ctorName ++ ")")
      branches := branches.push ("| " ++ full ctorName ++ " => " ++ quoted tag)
    runCommand ("instance : LeanDb.Model.Domain " ++ ty ++ " := { typeId := " ++ identity ++ ", cases := [" ++ String.intercalate ", " cases.toList ++ "] }")
    runCommand ("instance : Ontology.Wire " ++ ty ++ " := ⟨LeanDb.Model.enumCodec " ++ identity ++ " [" ++ String.intercalate ", " entries.toList ++ "] (fun value => " ++ (if branches.isEmpty then "nomatch value" else "match value with " ++ String.intercalate " " branches.toList) ++ ")⟩")

/-- Closed variants whose constructors carry named, non-dependent payload fields
(e.g. `Availability.onLoan (until : Time)`). Derived only for authored value types reached
from a derived record (or, through `ensureWire`, from an operation layer). -/
partial def deriveVariant (name : Lean.Name) (ctors : List Lean.Name) (identity : String) (visiting : NameSet) :
    CommandElabM Unit := do
  let ty := full name
  let mut cases : Array String := #[]
  let mut tags : Array String := #[]
  let mut encoders : Array String := #[]
  for ctorName in ctors do
    let tag := ctorName.getString!
    let fields ← liftTermElabM <| forallTelescopeReducing (← getConstInfo ctorName).type fun args _ => do
      let mut result : Array (String × Expr) := #[]
      for i in [:args.size] do
        let decl ← args[i]!.fvarId!.getDecl
        let fieldTy ← instantiateMVars decl.type
        if fieldTy.hasAnyFVar (fun fvar => args.contains (.fvar fvar)) then
          throwError "variant field {ctorName} #{i} depends on an earlier field; provide a checked representation adapter (declare `represent T as R by enc checked dec`)"
        let label := if decl.userName.hasMacroScopes || decl.userName.isAnonymous then "_" ++ toString (i + 1)
          else decl.userName.eraseMacroScopes.toString
        result := result.push (label, fieldTy)
      return result
    for (_, fieldTy) in fields do ensureWire fieldTy (visiting.insert name)
    let printed ← liftTermElabM <| fields.mapM fun (label, fieldTy) => do
      return (label, ← sourceOf fieldTy)
    tags := tags.push (quoted tag)
    let codecOf := fun (type : String) => "(Ontology.Wire.codec (α := " ++ type ++ "))"
    let binders := (List.range printed.size).map fun i => "x" ++ toString i
    if printed.isEmpty then
      cases := cases.push ("{ tag := " ++ quoted tag ++ ", decode := fun _ => pure " ++ full ctorName ++ " }")
      encoders := encoders.push ("| " ++ full ctorName ++ " => (" ++ quoted tag ++ ", none)")
    else
      let schema := String.intercalate ", " (printed.toList.map fun (label, type) => "(" ++ quoted label ++ ", " ++ codecOf type ++ ".schema)")
      let reads := String.intercalate "; " ((List.range printed.size).map fun i =>
        "let x" ++ toString i ++ " ← Ontology.Codec.field " ++ quoted printed[i]!.1 ++ " " ++ codecOf printed[i]!.2 ++ " payload")
      cases := cases.push ("{ tag := " ++ quoted tag ++ ", fields := [" ++ schema ++ "], decode := fun payload => do " ++ reads ++ "; pure (" ++ full ctorName ++ " " ++ String.intercalate " " binders ++ ") }")
      let writes := String.intercalate ", " ((List.range printed.size).map fun i =>
        "(" ++ quoted printed[i]!.1 ++ ", " ++ codecOf printed[i]!.2 ++ ".encode x" ++ toString i ++ ")")
      encoders := encoders.push ("| " ++ full ctorName ++ " " ++ String.intercalate " " binders ++ " => (" ++ quoted tag ++ ", some (Lean.Json.mkObj [" ++ writes ++ "]))")
  runCommand ("instance : LeanDb.Model.Domain " ++ ty ++ " := { typeId := " ++ identity ++ ", cases := [" ++ String.intercalate ", " tags.toList ++ "] }")
  runCommand ("instance : Ontology.Wire " ++ ty ++ " := ⟨LeanDb.Model.variantCodec " ++ identity ++ " [" ++ String.intercalate ", " cases.toList ++ "] (fun value => " ++ (if encoders.isEmpty then "nomatch value" else "match value with " ++ String.intercalate " " encoders.toList) ++ ")⟩")
end

/-- Declare which generated operations of `owner` are private to its module. Must run
before they are first used (generation is on first reference). -/
def setPrivateOperations (owner : Lean.Name) (stems : List String) : CommandElabM Unit := do
  if (entityRealization.getState (← getEnv)).1.contains owner then
    throwError "the generated operations of {owner} were already used; declare their visibility before first use"
  for stem in stems do
    unless ["insert", "find", "findBy", "update", "delete", "select", "patch"].contains stem do
      throwError "unknown generated operation `{stem}` (expected insert, find, findBy, update, delete, select or patch)"
    modifyEnv fun env => privateOperations.addEntry env (owner, stem)

/-- Register a unique constraint on entity `owner` and generate its constraint-local
declarations: `owner.name.key : UniqueKey owner K`, the lookup `owner.name.find`, and — for
the first constraint of `owner` — `owner.findBy`. (`T.Conflict`, `T.insert`, `T.update`
depend on ALL constraints of `T` and are generated on first use.) -/
def declareUniqueConstraint (owner name : Lean.Name) (fields : Array Lean.Name) (isPrivate : Bool := false) : CommandElabM Unit := do
  let env ← getEnv
  if (entityRealization.getState env).1.contains owner then
    throwError "constraint {owner}.{name} must be declared before {owner}.insert, {owner}.update or {owner}.Conflict are first used; they were already generated from the earlier constraints"
  if (constraintDeclarations.getState env).any (fun entry => entry.owner == owner && entry.name == name) then
    throwError "constraint {owner}.{name} is already declared"
  let structFields := getStructureFields env owner
  let ty := full owner
  let mut types : Array String := #[]
  for field in fields do
    unless structFields.contains field do
      throwError "constraint {owner}.{name}: {owner} has no field `{field}` (fields: {structFields.toList})"
    let fieldType ← liftTermElabM <| forallTelescopeReducing (← getConstInfo (owner ++ field)).type fun _ body => do
      sourceOf body
    types := types.push fieldType
  modifyEnv fun env => constraintDeclarations.addEntry env ⟨owner, name, fields, isPrivate⟩
  let base := full (owner ++ name)
  let identity := quoted (owner ++ name).toString
  let keyType := String.intercalate " × " (types.toList.map fun t => "(" ++ t ++ ")")
  let binders := (List.range fields.size).map fun i => "k" ++ toString i
  let tuple := if fields.size == 1 then "k0" else "(" ++ String.intercalate ", " binders ++ ")"
  let project := if fields.size == 1 then "value." ++ fields[0]!.toString
    else "(" ++ String.intercalate ", " (fields.toList.map fun f => "value." ++ f.toString) ++ ")"
  runCommand ("def " ++ base ++ ".key : LeanDb.Model.UniqueKey " ++ ty ++ " (" ++ keyType ++ ") := { identity := " ++ identity ++
    ", fields := [" ++ String.intercalate ", " (fields.toList.map fun f => quoted f.toString) ++ "], key := fun value => " ++ project ++
    ", equal := fun a b => a == b }")
  let first := !(constraintDeclarations.getState env).any (·.owner == owner)
  if (← getEnv).contains (owner ++ `Row) then
    let arrows := String.intercalate " → " (types.toList.map fun t => "(" ++ t ++ ")")
    runCommand ((if isPrivate then "private " else "") ++ "def " ++ base ++ ".find : " ++ arrows ++ " → LeanDb.Model.Query (Option (" ++ full (owner ++ `Row) ++ " LeanDb.Model.OpScope)) := fun " ++
      String.intercalate " " binders ++ " => LeanDb.Model.Query.findBy " ++ base ++ ".key " ++ tuple)
    -- `T.findBy` names the FIRST declared unique constraint, so it is fixed now.
    if first then
      let hidden := isPrivate || isPrivateOperation env owner "findBy"
      runCommand ((if hidden then "private def " else "def ") ++ full (owner ++ `findBy) ++ " := " ++ base ++ ".find")

initialize registerDerivingHandler ``LeanDb.Model.Domain fun names => do
  for name in names do deriveOne name false
  return true
initialize registerDerivingHandler ``LeanDb.Model.Entity fun names => do
  for name in names do deriveOne name true
  return true
end LeanDb.Model.Deriving
