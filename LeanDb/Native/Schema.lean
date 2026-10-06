import LeanDb.Native.Witness
import LeanDb.Native.Resources
import LeanDb.Model.Deriving
import LeanDb.Derive

/-! # `native_schema%`: the native schema of model entities

`native_schema% S := T₁, T₂, …` reads the `LeanDb.Model` declarations of each entity and
derives, with no second declaration of anything:

* a native `LeanDb.Entity` for the ORIGINAL type (field symbols `T.DbField`), closed enums as
  native enums, and every other structured field type with a `StorageCodec` as one canonical
  JSON TEXT column (`storageColCodec`);
* `constraint C.c : cascade f` as a native cascade, and every `constraint T.c : unique …`
  (single-field and composite, in declaration order) as a native unique index whose key is
  proven (by `rfl`) to agree with the declared key;
* schema `S` (`schema%`) and the evidence `storageResources S` carries: `HasEntityStorage`,
  `HasUniqueStorage` per constraint, `HasFieldStorage`/`HasColumnEvidence` per `Wire` field,
  and `HasLinkStorage`/`HasLinkEvidence` per declared `link E.a E.b`. -/

namespace LeanDb.Native
open Lean Elab Command Meta

private def nativeName (name : Name) : Ident := mkIdent (`_root_ ++ name)

/-- The entity a name refers to, resolved as Lean resolves any name (current namespace, `open`s). -/
private def resolveType (type : Ident) : CommandElabM Name := do
  try liftCoreM <| realizeGlobalConstNoOverload type
  catch _ => throwErrorAt type "native_schema: unknown type {type.getId}"

private def fieldType (owner field : Name) : CommandElabM Expr := liftTermElabM do
  let info ← getConstInfo (owner ++ field)
  forallTelescopeReducing info.type fun _ body => pure body

/-- Consume the model declarations once. Original entity types receive native
    Entity instances; unique declarations become the corresponding native typed
    constraint. Unsupported fields are rejected by derivation, not silently ignored. -/
syntax (name := nativeSchema) "native_schema% " ident " := " ident,+ : command

@[command_elab nativeSchema]
def elabNativeSchema : CommandElab := fun stx => do
  let `(native_schema% $schema:ident := $types:ident,*) := stx | throwUnsupportedSyntax
  let resolved ← types.getElems.mapM resolveType
  for type in resolved do
    let model ← liftTermElabM do
      synthInstance? (mkApp (mkConst ``LeanDb.Model.Entity) (mkConst type))
    unless model.isSome do throwError "native_schema: {type} has no model entity declaration (`deriving Entity`)"
    let hasNative ← liftTermElabM do
      synthInstance? (mkApp (mkConst ``LeanDb.Entity) (mkConst type))
    unless hasNative.isSome do
      -- Model `constraint E.name : cascade field`: the reference cascades on
      -- delete. Recorded before the native entity is derived, like `cascade%`
      -- (which keeps working; the declaration is idempotent).
      for entry in LeanDb.Model.Deriving.cascadeDeclarations.getState (← getEnv) do
        if entry.owner == type then
          LeanDb.Derive.declareCascade entry.owner entry.field
      -- Closed enum storage is derived from the same enum, never a duplicate.
      -- Any other field type with a model `StorageCodec` and no native codec
      -- (a list, a record, a variant with payloads, a represented type) is one
      -- TEXT column of its canonical JSON (`storageColCodec`).
      for field in getStructureFields (← getEnv) type do
        let ty ← fieldType type field
        let storage? ← liftTermElabM do
          let ty ← whnf ty
          if (← synthInstance? (mkApp (mkConst ``LeanDb.ColCodec) ty)).isSome then return none
          if let .const name _ := ty then
            if let .inductInfo info ← getConstInfo name then
              if !(isStructure (← getEnv) name) then
                let payloadFree ← info.ctors.allM fun ctor => do
                  return (← getConstInfoCtor ctor).numFields == 0
                if payloadFree then return some (Sum.inl name)
          if (← synthInstance? (mkApp (mkConst ``LeanDb.Model.StorageCodec) ty)).isSome then
            return some (Sum.inr ty)
          return none
        match storage? with
        | some (.inl enum) => discard <| LeanDb.Derive.deriveClosedEnum enum
        | some (.inr valueType) =>
            let valueStx ← liftTermElabM do
              withOptions (fun options => options.setBool `pp.fullNames true) (PrettyPrinter.delab valueType)
            elabCommand (← `(instance : LeanDb.ColCodec $valueStx := LeanDb.Native.storageColCodec $valueStx))
        | none => pure ()
      -- Model derivation owns T.Field. Native symbols are separate storage
      -- evidence derived from the same fields, with no duplicate record type.
      discard <| LeanDb.Derive.deriveEntityCore type (fieldTyName := type ++ `DbField)
  -- Model `Unique T Value` declarations carry typed paths. Recover the
  -- direct field identity by normalization; no unsafe type/string casts.
  let env ← getEnv
  let declarations := env.constants.toList
  let mut uniqueSources : Array (Name × Name × Name) := #[]
  for (name, info) in declarations do
    let ty := info.type
    if ty.isAppOfArity ``LeanDb.Model.Unique 2 then
      let owner := ty.getArg! 0
      if let .const owner _ := owner then
        if resolved.contains owner then
          let fieldName ← liftTermElabM do
            let field ← mkAppM ``LeanDb.Model.Unique.field #[mkConst name]
            let identity ← whnf (← mkAppM ``Ontology.FieldPath.identity #[field])
            unless identity.isAppOfArity ``List.cons 3 do
              throwError "native_schema: unique {name} needs one direct field path"
            let segment ← whnf (identity.getArg! 1)
            let tail ← whnf (identity.getArg! 2)
            unless tail.isAppOfArity ``List.nil 1 && segment.isAppOfArity ``Ontology.PathSegment.field 2 do
              throwError "native_schema: unique {name} needs one direct field path"
            let .lit (.strVal field) ← whnf (segment.getArg! 1)
              | throwError "native_schema: unique path field is not a literal"
            return Name.mkSimple field
          unless (getStructureFields env owner).contains fieldName do
            throwError "native_schema: {name} names unknown field {fieldName}"
          -- A label alone does not prove this is the declared getter. Keep
          -- an actual kernel-checked agreement theorem before using the
          -- original field as the native unique key; opaque/custom getters
          -- with the same identity must not silently change the constraint.
          let agreement := name ++ `nativeFieldAgreement
          let ownerId := nativeName owner
          let uniqueId := nativeName name
          let getterId := nativeName (owner ++ fieldName)
          if (← getEnv).contains agreement then
            -- Repeated assembly still checks the getter. An existing symbol
            -- with this name is not evidence of any agreement proposition.
            elabCommand (← `(
              example : ∀ record : $ownerId,
                  (LeanDb.Model.Unique.field $uniqueId).get record = $getterId record := by
                intro record
                rfl
            ))
          else
            elabCommand (← `(
              theorem $(nativeName agreement):ident : ∀ record : $ownerId,
                  (LeanDb.Model.Unique.field $uniqueId).get record = $getterId record := by
                intro record
                rfl
            ))
          let entry : UniqueEntry := { typeName := owner, ctor := .mkSimple name.getString!, fields := #[fieldName] }
          if uniqueSources.any (fun (type, ctor, _) => type == owner && ctor == entry.ctor) then
            throwError "native_schema: ambiguous unique alternative {owner}.{entry.ctor}"
          uniqueSources := uniqueSources.push (owner, entry.ctor, name)
          unless (uniqueExt.getState (← getEnv)).any (fun u => u.typeName == entry.typeName && u.ctor == entry.ctor) do
            modifyEnv (uniqueExt.modifyState · (·.push entry))
  -- Declared constraints with no single-field `Unique T V` descriptor, i.e. the
  -- composite `constraint T.c : unique (f₁, f₂)`, come from the model
  -- declaration registry. The native index is derived from the declared fields
  -- (in order); its identity is the declaration's `UniqueKey`.
  let declarations := (LeanDb.Model.Deriving.constraintDeclarations.getState (← getEnv)).filter
    (fun entry => resolved.contains entry.owner)
  let mut keyedSources : Array (Name × Name × Array Name) := #[]
  for entry in declarations do
    if uniqueSources.any (fun (type, ctor, _) => type == entry.owner && ctor == entry.name) then continue
    unless (← getEnv).contains (entry.owner ++ entry.name ++ `key) do
      throwError "native_schema: constraint {entry.owner}.{entry.name} has no key descriptor"
    for field in entry.fields do
      unless (getStructureFields (← getEnv) entry.owner).contains field do
        throwError "native_schema: constraint {entry.owner}.{entry.name} names unknown field {field}"
    keyedSources := keyedSources.push (entry.owner, entry.name, entry.fields)
    unless (uniqueExt.getState (← getEnv)).any (fun u => u.typeName == entry.owner && u.ctor == entry.name) do
      modifyEnv (uniqueExt.modifyState · (·.push { typeName := entry.owner, ctor := entry.name, fields := entry.fields }))
  -- Native alternatives follow declaration order, as the model's `T.Conflict`
  -- constructors do (the first clashing constraint is the one reported).
  let order := declarations.toList.map fun entry => (entry.owner, entry.name)
  let rank := fun (u : UniqueEntry) => (order.findIdx? (· == (u.typeName, u.ctor))).getD order.length
  modifyEnv (uniqueExt.modifyState · fun entries =>
    entries.filter (!resolved.contains ·.typeName) ++
      (entries.filter (resolved.contains ·.typeName)).insertionSort (fun a b => rank a < rank b))
  let nativeTypes := resolved.map nativeName
  elabCommand (← `(schema% $schema := $nativeTypes,*))
  -- Actual dictionaries, indexed by the concrete source type and schema.
  -- These are generated assembly evidence for a typed resource-family IR;
  -- they do not invent an untyped runtime dispatch or another Flow meaning.
  let schemaName := (← getCurrNamespace) ++ schema.getId
  let schemaId := nativeName schemaName
  -- The native alternative retains its original semantic descriptor identity.
  -- A kernel equality checks actual encoded keys as well as the earlier getter.
  for (owner, ctor, source) in uniqueSources do
    let ownerId := nativeName owner
    let sourceId := nativeName source
    let indexId := nativeName (owner ++ `Unique ++ ctor)
    let proposition ← `(term| ∀ record : $ownerId,
      LeanDb.Unique.encodeKey (α := $ownerId) $indexId
        (LeanDb.Unique.keyOf (α := $ownerId) $indexId record) =
      #[LeanDb.toCol ((LeanDb.Model.Unique.field $sourceId).get record)])
    let agreement := source ++ `nativeKeyAgreement
    if (← getEnv).contains agreement then
      elabCommand (← `(example : $proposition := by intro record; rfl))
    else
      elabCommand (← `(theorem $(nativeName agreement):ident : $proposition := by intro record; rfl))
  -- Composite (keyed) constraints: the native key IS the declaration's key, and
  -- the encoded index key is each declared field's column value, in order.
  for (owner, ctor, fields) in keyedSources do
    let ownerId := nativeName owner
    let keyId := nativeName (owner ++ ctor ++ `key)
    let indexId := nativeName (owner ++ `Unique ++ ctor)
    let cols : Array Term ← fields.mapM fun field =>
      `(LeanDb.toCol ($(nativeName (owner ++ field)) record))
    let proposition ← `(term| ∀ record : $ownerId,
      LeanDb.Unique.keyOf (α := $ownerId) $indexId record = (LeanDb.Model.UniqueKey.key $keyId) record ∧
      LeanDb.Unique.encodeKey (α := $ownerId) $indexId
        (LeanDb.Unique.keyOf (α := $ownerId) $indexId record) = #[$cols,*])
    let agreement := owner ++ ctor ++ `nativeKeyAgreement
    if (← getEnv).contains agreement then
      elabCommand (← `(example : $proposition := fun _ => ⟨rfl, rfl⟩))
    else
      elabCommand (← `(theorem $(nativeName agreement):ident : $proposition := fun _ => ⟨rfl, rfl⟩))
  for type in resolved do
    let typeId := nativeName type
    let sources := uniqueSources.filter (fun (owner, _, _) => owner == type)
    let keyed := keyedSources.filter (fun (owner, _, _) => owner == type)
    let sourceIdentity : TSyntax `term ← if sources.isEmpty && keyed.isEmpty then `(LeanDb.Unique.identity) else do
      let alternatives ← sources.mapM fun (_, ctor, source) =>
        `(Lean.Parser.Term.matchAltExpr| | .$(mkIdent ctor):ident =>
            LeanDb.Model.Unique.identity $(nativeName source))
      let keyedAlternatives ← keyed.mapM fun (owner, ctor, _) =>
        `(Lean.Parser.Term.matchAltExpr| | .$(mkIdent ctor):ident =>
            LeanDb.Model.UniqueKey.identity $(nativeName (owner ++ ctor ++ `key)))
      let alternatives := alternatives ++ keyedAlternatives
      `(fun $alternatives:matchAlt*)
    elabCommand (← `(
      @[reducible] instance : LeanDb.Native.HasEntityStorage $schemaId $typeId where
        storage := {
          entity := inferInstance
          indexes := inferInstance
          unique := inferInstance
          foreignKey := inferInstance
          schema := inferInstance
          pack := inferInstance
          referencedBy := inferInstance
          sourceUnique := $sourceIdentity }
    ))
  -- Typed lookup evidence (`StorageResources.unique`) for EVERY declared constraint,
  -- single-field and composite: the native alternative, the key conversion
  -- (identity: the native key type is the declared key type), and both laws by `rfl`.
  for entry in declarations do
    let keyName := entry.owner ++ entry.name ++ `key
    unless (← getEnv).contains keyName do continue
    let keyType ← liftTermElabM do
      let type ← whnfR (← inferType (mkConst keyName))
      unless type.isAppOfArity ``LeanDb.Model.UniqueKey 2 do
        throwError "native_schema: {keyName} is not a UniqueKey"
      withOptions (fun options => options.setBool `pp.fullNames true) (PrettyPrinter.delab (type.getArg! 1))
    elabCommand (← `(
      @[reducible] instance : LeanDb.Native.HasUniqueStorage $schemaId $(nativeName entry.owner) $keyType
          $(nativeName keyName) where
        lookup := {
          index := $(nativeName (entry.owner ++ `Unique ++ entry.name))
          encode := fun key => key
          identity_agrees := rfl
          key_agrees := fun _ => rfl }
    ))
  -- Direct-column witnesses retain the original typed getter/path, not merely
  -- its string label; flattened/noncolumn paths cannot acquire one.
  for type in resolved do
    let typeId := nativeName type
    let symbols ← liftTermElabM do
      let typeExpr := mkConst type
      let entity ← synthInstance (mkApp (mkConst ``LeanDb.Entity) typeExpr)
      let .const name _ ← whnf (mkApp2 (mkConst ``LeanDb.Entity.Field) typeExpr entity)
        | throwError "native_schema: expected declared native field symbols"
      pure name
    for field in getStructureFields (← getEnv) type do
      let symbol := symbols ++ field
      unless (← getEnv).contains symbol do continue
      let valueTy ← fieldType type field
      -- A server-only value (no `Wire`, e.g. `PasswordHash`) is a column but never
      -- an output: it gets no column evidence, so no model read
      -- (`Query.linkField`) can select it.
      let wire ← liftTermElabM do
        return (← synthInstance? (mkApp (mkConst ``Ontology.Wire) valueTy)).isSome
      unless wire do continue
      let valueStx ← liftTermElabM do
        withOptions (fun options => options.setBool `pp.fullNames true) (PrettyPrinter.delab valueTy)
      let source := nativeName (type ++ field.appendAfter "Path")
      elabCommand (← `(
        @[reducible] instance : LeanDb.Native.HasFieldStorage $schemaId $typeId
            $(quote field.toString) $valueStx where
          storage := {
            field := $(nativeName symbol)
            valueType := rfl
            source := $source
            getter_agrees := fun _ => rfl }
      ))
      elabCommand (← `(
        @[reducible] instance : LeanDb.Native.HasColumnEvidence $schemaId $typeId $valueStx $source where
          evidence := {
            column := LeanDb.Native.HasFieldStorage.storage (s := $schemaId) (T := $typeId)
              (field := $(quote field.toString)) (Value := $valueStx)
            source_agrees := rfl }
      ))
  -- Typed links for joins, for each declared link `link E.parent E.target`
  -- (e.g. `link Loan.book Loan.member` gives `Loan.link.book.member`, `Book → Member`).
  -- Nothing is inferred from an entity's shape. The column laws are `rfl` because
  -- the SQL column and the getter are the same field.
  for type in resolved do
    let symbols ← liftTermElabM do
      let typeExpr := mkConst type
      let entity ← synthInstance (mkApp (mkConst ``LeanDb.Entity) typeExpr)
      let .const name _ ← whnf (mkApp2 (mkConst ``LeanDb.Entity.Field) typeExpr entity)
        | throwError "native_schema: expected declared native field symbols"
      pure name
    let mut references : Array (Name × Name) := #[]
    for field in getStructureFields (← getEnv) type do
      unless (← getEnv).contains (symbols ++ field) do continue
      let declared ← fieldType type field
      let target? ← liftTermElabM do
        let ty ← whnfR declared
        if ty.isAppOfArity ``Ontology.EntityId 1 then
          match ty.appArg! with
          | .const target _ => return some target
          | _ => return none
        else return none
      if let some target := target? then
        if resolved.contains target then references := references.push (field, target)
    for (parentField, parentType) in references do
      for (targetField, targetType) in references do
        if parentField == targetField then continue
        let keyName := type ++ `link ++ parentField ++ targetField
        unless (← getEnv).contains keyName do continue
        let edgeId := nativeName type
        elabCommand (← `(
          @[reducible] instance : LeanDb.Native.HasLinkStorage $schemaId $edgeId
              $(quote parentField.toString) $(quote targetField.toString)
              $(nativeName parentType) $(nativeName targetType) where
            storage := {
              parent := LeanDb.Native.HasEntityStorage.storage
              target := LeanDb.Native.HasEntityStorage.storage
              edge := LeanDb.Native.HasEntityStorage.storage
              relation := {
                parentField := $(nativeName (symbols ++ parentField))
                targetField := $(nativeName (symbols ++ targetField))
                getParent := fun edge => LeanDb.ReferenceValue.id ($(nativeName (type ++ parentField)) edge)
                getTarget := fun edge => LeanDb.ReferenceValue.id ($(nativeName (type ++ targetField)) edge)
                parentColumn := fun _ => rfl
                targetColumn := fun _ => rfl } }
        ))
        -- Evidence for the model join key `E.link.<parent>.<target>`.
        do
          elabCommand (← `(
            @[reducible] instance : LeanDb.Native.HasLinkEvidence $schemaId $edgeId
                $(nativeName parentType) $(nativeName targetType) $(nativeName keyName) where
              evidence := {
                parentIdentity := inferInstance
                targetIdentity := inferInstance
                link := LeanDb.Native.HasLinkStorage.storage (s := $schemaId) (Edge := $edgeId)
                  (parentField := $(quote parentField.toString)) (targetField := $(quote targetField.toString))
                parent_agrees := fun _ => rfl
                target_agrees := fun _ => rfl }
          ))

end LeanDb.Native
