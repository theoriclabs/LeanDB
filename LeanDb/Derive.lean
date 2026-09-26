import Lean
import LeanDb.Json

/-! # `deriving LeanDb.Entity`

Generates, for a flat structure `Ticket`:

- `inductive Ticket.Field` — one constructor per declared field, in order,
  spelled as the structure spells it (`«at»`), `deriving DecidableEq, Repr`;
- the `Entity Ticket` instance: `fieldTy`/`get`/`codec`/`fieldSpec` as a
  `match` over the symbols, `fields`, table name, row encode/decode;
- the `FieldOf Ticket.Field Ticket` instance (symbol type → entity).

The generated code references only `columnSpec`/`ColCodec` through the
field *types*, so the schema cannot drift from the structure — there is
nothing else it could be derived from. A structure that already declares
`Field` in its namespace is refused.

A field whose default is `derived e`, with `e` over earlier fields, is a
**derived column** (LEP-0003 B3): `encode` recomputes it from its sources
(the supplied value is ignored), `decode` checks the stored value against
the recomputation and fails with `decode` naming the column if they
differ, and the JSON boundary may omit it. Lean forbids attributes on
structure fields, so the mark is the `derived` wrapper in the default.

A field whose type has an `Inline` instance (LEP-0003 C) is **flattened**:
`launch : LaunchConfig` contributes one column per inline sub-field,
`launch_block`, `launch_smemBytes`, …, each a symbol of the parent's
`Field` inductive (`Kernel.Field.launch_smemBytes`) with the sub-field's
type and codec, its column spec under the prefixed name and
`group := some "launch"`. `encode` splices the inline `encode`; `decode`
slices the row and calls the inline `decode`, naming `launch_<sub>` on
failure. A sub-field's own default is that column's default; a
parent-level default for the whole value is evaluated at derive time and
split. `Option` of an inline type is refused by name.

A field `ins : List R` whose element type `R` has an `Inline` instance
(LEP-0003 D) is a **child table**: the derive declares a structure
`Parent.Ins` — `parent : Ref Parent`, `position : Nat`, then `R`'s fields
copied verbatim (names, types, defaults) — and derives `LeanDb.Entity` for
it under the table name `<parent_table>_<field>`, with `parent` a
cascading foreign key; plus `Parent.Ins.record : Parent.Ins → R` and
`Parent.Ins.ofRecord`. (The field's own name is its projection function,
so the entity is spelled with the field capitalized.) The parent's `Field`
has no symbol for the list — it is not a column — and its `decode` leaves
the list empty; `Entity.children` carries a `ChildLink` per list that
reads the list off a value and attaches it back, which is what the
executor and the JSON boundary use. A derived column may be computed from
a child list; `decode` cannot check it without the list, so the link's
`attach` does. Refused by name: `List` of a non-`Inline` type without a
codec of its own, `Option (List R)`, a list inside an `Inline` record
(one level), a `derived` child list (LEP-0005), and a record field named
`parent` or `position`.

Not supported (typed error, not a runtime surprise): parameterized
structures, and fields whose types depend on earlier fields (proof fields).
A proof-carrying *nested* type is stored through its data representation
with `LeanDb.DbJson.via` instead.

# `deriving LeanDb.Inline`

For a small flat structure stored inside an entity's row: the same
`Field`/`fieldTy`/`get`/`codec`/`fieldSpec`/`fields`/`encode`/`decode`
surface as `Entity`, minus the table, plus `Inline.FieldOf`. One level
only — a field of an `Inline` type inside an `Inline` structure is refused
by name, as are a `List` field (a nested child table), `Option` of one and
`derived` defaults.

# `deriving LeanDb.DbJson`

For a nested value type (a structure or an inductive, recursive or not,
without parameters): `Lean.ToJson` and `Lean.FromJson` in exactly the
encoding Lean's own derive produces — objects for structures,
constructor-tagged objects for inductives — except that an omitted
structure field with a default takes the default; plus `JsonShape`, the
canonical description of the type that the fingerprint and `migrate` see.
A type the derive cannot walk (proof fields) gets `DbJson.via` over its
data representation instead; the parent derive then sees the data shape.
-/

namespace LeanDb.Derive

open Lean Elab Command Term Meta PrettyPrinter

private unsafe def evalColUnsafe (e : Expr) : MetaM LeanDb.Col :=
  evalExpr LeanDb.Col (mkConst ``LeanDb.Col) e

/-- Evaluate a `Col`-valued closed expression at elaboration time. Used to
    turn structure field defaults into literals with their definition-site
    instances baked in (a delab/re-elaborate round trip can resolve scoped
    instances differently, and referencing the `_default` constant from
    compiled code trips an LCNF panic on this toolchain). -/
@[implemented_by evalColUnsafe]
private opaque evalCol (e : Expr) : MetaM LeanDb.Col

/-- Quote an evaluated `Col` back into surface syntax. -/
private def colLitStx (v : LeanDb.Col) : Elab.TermElabM Term :=
  match v with
  | .text s => `(LeanDb.Col.text $(quote s))
  | .int i =>
      let n : Nat := i.toInt.natAbs
      if i.toInt < 0 then `(LeanDb.Col.int (-(Int64.ofNat $(quote n))))
      else `(LeanDb.Col.int (Int64.ofNat $(quote n)))
  | .real f => `(LeanDb.Col.real (Float.ofBits (UInt64.ofNat $(quote f.toBits.toNat))))
  | .null => `(LeanDb.Col.null)

/-- `"UserProfile"` → `"user_profile"`. -/
def tableNameOf (declName : Name) : String :=
  let last := declName.getString!
  last.foldl (init := "") fun acc c =>
    if c.isUpper then
      (if acc.isEmpty then acc else acc ++ "_") ++ c.toLower.toString
    else
      acc ++ c.toString

/-- Field/column names LeanDB cannot generate as a field symbol: `rec`
    collides with the recursor every inductive gets (`Field.rec`), and the
    modifier keywords cannot start a constructor declaration (an
    `inductive T.Field where | unsafe` fails to parse). A structure can
    carry such a field under guillemets, but `deriving LeanDb.Entity`
    would then fail with an unattributed kernel or parser error, so the
    derive refuses them by name (and the importer skips such columns). -/
def unusableSymNames : List String :=
  ["rec", "unsafe", "noncomputable", "partial", "private", "protected"]

private def fieldBinder (i : Nat) : Ident := mkIdent (Name.mkSimple s!"f{i}")

/-- An identifier for a declaration generated next to `declName`, anchored
    at `_root_` so the current namespace is not prepended (a private
    declaration re-mangles to the same private name — same module). -/
private def rootIdent (n : Name) : Ident :=
  mkIdent (`_root_ ++ (privateToUserName? n).getD n)

/-- Delaborate for re-elaboration in generated code: full names, so the
    term means the same thing wherever the instance is elaborated. -/
private def delabFull (e : Expr) : TermElabM Term :=
  withOptions (fun o => o.setBool `pp.fullNames true) (delab e)

/-- A structure field's default, analysed. Structure default functions
    (`S.f._default`) are never compiled — Lean adds them for elaboration
    only, and referencing one from compiled code panics LCNF — so the
    value is *reified*: delaborated and re-elaborated inside the generated
    code. `params` are the fields the default depends on, in order (the
    lambda binders Lean abstracts, named after the fields), so the reified
    term applied to those fields' values is the default. -/
private structure DefaultInfo where
  /-- The whole `_default` value (a lambda over `params` if nonempty). -/
  value : Expr
  params : Array Name
  /-- Marked `LeanDb.derived`. -/
  isDerived : Bool

private partial def stripIdMData : Expr → Expr
  | .mdata _ e => stripIdMData e
  | e => if e.isAppOfArity ``id 2 then stripIdMData e.appArg! else e

private def defaultInfo? (declName fname : Name) (fields : Array Name) :
    MetaM (Option DefaultInfo) := do
  let env ← getEnv
  let some dn := getDefaultFnForField? env declName fname | return none
  let info ← getConstInfo dn
  let value := info.value!
  -- leading lambdas named after fields are the dependencies; anything
  -- else is the value itself (a function-typed field)
  let rec deps (e : Expr) (acc : Array Name) : Array Name :=
    match e with
    | .lam n _ b _ => if fields.contains n then deps b (acc.push n) else acc
    | _ => acc
  let params := deps value #[]
  let body ← lambdaBoundedTelescope value params.size fun _ body => pure body
  return some { value, params, isDerived := (stripIdMData body).isAppOf ``LeanDb.derived }

/-! ## The field walk shared by `Entity` and `Inline`

Both derives walk a structure's fields the same way — one column per
scalar field, its symbol, type, getter, codec, spec, encoding and
decoding — and differ only in what surrounds the walk: an entity has a
table, derived columns and typed errors; an inline structure has none
of those. An entity field whose type is `Inline` is *flattened* here:
it contributes one column per inline sub-field, each a symbol of its
own in the parent's `Field` inductive. -/

/-- One generated column. -/
private structure ColGen where
  /-- The symbol constructor: `age`, or `launch_smemBytes` for a
      flattened one. -/
  symName : Name
  colName : String
  /-- The column's Lean type. -/
  tyStx : Term
  /-- `get`: the value read off `r`. -/
  getStx : Term
  codecStx : Term
  specStx : Term
  /-- `encode`: the column value off `r` (a derived column recomputes). -/
  encStx : Term
  /-- Derived (entity only): the reified recompute function and the
      declared-field indices it is applied to. -/
  recompute : Option (Term × Array Nat) := none
  /-- `true` when `toSql?` of this column can return `none` (`Nat`, or
      `Option` of such). Other columns always encode, so `rangeOk` is
      definitionally `true` and `decide` works on free rows. -/
  canRefuse : Bool := false
  deriving Inhabited

/-- How a declared field is encoded and decoded. -/
private inductive FieldEnc where
  /-- One column, decoded through its codec. -/
  | plain (colName : String) (tyStx : Term) (col : Nat)
  /-- An inline value: `len` columns from `start`, spliced by the inline
      instance's `encode`/`decode`. -/
  | inline (tyStx : Term) (start len : Nat)
  /-- A child list (LEP-0003 D): no columns of its own; `decode` leaves it
      empty and the parent's `ChildLink` attaches it. -/
  | child (elemTy : Expr) (elemTyStx : Term)
  deriving Inhabited

private def FieldEnc.isChild : FieldEnc → Bool
  | .child .. => true
  | _ => false

/-- `toSql?` can return `none` for `Nat` (and `Option` wrapping it). -/
private partial def tyCanRefuse (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  if ty.isConstOf ``Nat then true
  else if ty.isAppOfArity ``Option 1 then tyCanRefuse (ty.getArg! 0)
  else false

/-- A declared field with the columns it contributes. -/
private structure FieldGen where
  fname : Name
  cols : Array ColGen
  enc : FieldEnc
  deriving Inhabited

/-- A sub-field of an inline structure, as the parent needs it. -/
private structure SubField where
  name : Name
  ty : Expr
  tyStx : Term
  /-- The inline type's own symbol for it (`Dims.Field.w`). -/
  sym : Name
  deriving Inhabited

/-- Does `ty` have an `Inline` instance? -/
private def isInlineTy (ty : Expr) : MetaM Bool := do
  try
    return (← synthInstance? (mkApp (mkConst ``LeanDb.Inline) ty)).isSome
  catch _ => return false

/-- Does `ty` have a `ColCodec` instance? (A `List` with a codec of its own
    is a scalar column, not a child table.) -/
private def hasCodec (ty : Expr) : MetaM Bool := do
  try
    return (← synthInstance? (mkApp (mkConst ``LeanDb.ColCodec) ty)).isSome
  catch _ => return false

/-- The sub-fields of the inline structure `τ`, in order, with the
    symbols its `Inline` instance declares for them. -/
private def inlineSubFields (who : String) (owner fname : Name) (τ : Expr) :
    TermElabM (Array SubField) := do
  let env ← getEnv
  let .const iname _ := τ.getAppFn |
    throwError "{who}: field '{fname}' of {owner} has the Inline type {τ}, which is not a plain structure"
  unless isStructure env iname && τ.getAppNumArgs == 0 do
    throwError "{who}: field '{fname}' of {owner} has the Inline type {τ}, which is not a plain structure"
  let inst ← synthInstance (mkApp (mkConst ``LeanDb.Inline) τ)
  let symTy ← whnf (mkApp2 (mkConst ``LeanDb.Inline.Field) τ inst)
  let .const symTyName _ := symTy |
    throwError "{who}: the Inline instance of {τ} has a symbol type that is not an inductive ({symTy})"
  let ctorInfo ← getConstInfoCtor (← getConstInfoInduct iname).ctors.head!
  let subs := getStructureFields env iname
  forallTelescopeReducing ctorInfo.type fun ys _ => do
    unless ys.size == subs.size do
      throwError "{who}: unexpected constructor arity for {iname}"
    let mut out := #[]
    for j in [0:subs.size] do
      let g := subs[j]!
      let ty ← inferType ys[j]!
      if (Array.ofSubarray ys[0:j]).any (fun y => ty.containsFVar y.fvarId!) then
        throwError "{who}: field '{g}' of the inline type {iname} depends on an earlier field; not supported"
      let sym := symTyName ++ g
      unless env.contains sym do
        throwError "{who}: the Inline instance of {iname} declares no symbol '{sym}' for field '{g}'"
      out := out.push { name := g, ty, tyStx := ← delab ty, sym }
    return out

/-- Walk the fields of `declName` (inside its constructor's telescope) into
    the columns they generate. `entity` says whether derived columns,
    inline flattening and child lists are allowed (they are entity
    notions); `cascade` names the `Ref` fields whose foreign key cascades
    on delete, with the table they reference (a generated child's
    `parent` — the parent's `Entity` instance does not exist yet when the
    child is derived, so `RefTarget` cannot name the table). -/
private def walkFields (who : String) (declName : Name) (entity : Bool)
    (cascade : Array (Name × String) := #[]) (declaredCascade : Array Name := #[]) : TermElabM (Array FieldGen) := do
  let env ← getEnv
  let ctorInfo ← getConstInfoCtor (← getConstInfoInduct declName).ctors.head!
  let fields := getStructureFields env declName
  forallTelescopeReducing ctorInfo.type fun xs _ => do
    unless xs.size == fields.size do
      throwError "{who}: unexpected constructor arity for {declName}"
    let mut gens : Array FieldGen := #[]
    let mut nextCol := 0
    for i in [0:fields.size] do
      let fname := fields[i]!
      let ftype := (← instantiateMVars (← inferType xs[i]!)).consumeMData
      if (Array.ofSubarray xs[0:i]).any (fun x => ftype.containsFVar x.fvarId!) then
        throwError "{who}: field '{fname}' of {declName} depends on an earlier field; proof/dependent fields are not stored — persist the data representation instead and re-decide the proofs on decode with `LeanDb.DbJson.via`"
      let tyStx ← delab ftype
      -- `Option` of an inline value is refused: "every sub-column NULL" is
      -- ambiguous once a sub-field is itself nullable
      if ftype.isAppOfArity ``Option 1 then
        if ← isInlineTy (ftype.getArg! 0) then
          throwError "{who}: field '{fname}' of {declName} is `Option {ftype.getArg! 0}` where {ftype.getArg! 0} is an Inline structure; an optional inline value is not supported (all sub-columns NULL is ambiguous once a sub-field is itself nullable) — store it as a JSON column (ColCodec.json) if it must be optional"
        -- …and so is an optional child list: absent and empty would be indistinguishable
        let inner := ftype.getArg! 0
        if inner.isAppOfArity ``List 1 then
          if ← isInlineTy (inner.getArg! 0) then
            throwError "{who}: field '{fname}' of {declName} is `Option (List {inner.getArg! 0})` where {inner.getArg! 0} is an Inline record; an optional child list is not supported (an absent list and an empty one would be the same rows) — use `List {inner.getArg! 0}` and let empty mean none"
      let dflt? ← defaultInfo? declName fname fields
      -- a child list (LEP-0003 D): `List R` with `R` an Inline record
      if ftype.isAppOfArity ``List 1 then
        let elem := (ftype.getArg! 0).consumeMData
        if ← isInlineTy elem then
          unless entity do
            throwError "{who}: field '{fname}' of {declName} is `List {elem}` where {elem} is an Inline record; an Inline record cannot itself contain a child list (nested child tables are not supported)"
          if dflt?.any (·.isDerived) then
            throwError "{who}: field '{fname}' of {declName} is a child list marked `derived`; derived child lists (a tabulated relation, LEP-0005) are not supported yet"
          gens := gens.push { fname, cols := #[], enc := .child elem (← delabFull elem) }
          continue
        else if !(← hasCodec ftype) then
          if entity then
            throwError "{who}: field '{fname}' of {declName} is `List {elem}` but {elem} is not an Inline record; a child table needs `deriving LeanDb.Inline` on the element type (or give `List {elem}` a ColCodec of its own to store it as one column)"
          else
            throwError "{who}: field '{fname}' of {declName} is `List {elem}`; an Inline record cannot contain a list (nested child tables are not supported), and `List {elem}` has no ColCodec of its own"
      if ← isInlineTy ftype then
        -- an inline field: flattened into one column per sub-field
        unless entity do
          throwError "{who}: field '{fname}' of {declName} has type {ftype}, which is itself an Inline structure; nesting inline structures is not supported yet (one level only)"
        if dflt?.any (·.isDerived) then
          throwError "{who}: field '{fname}' of {declName} is marked `derived` but has an Inline type; a derived column must be a scalar"
        let subs ← inlineSubFields who declName fname ftype
        -- a parent-level default for the whole value is evaluated here and
        -- split into per-column defaults; a sub-field's own default comes
        -- with its `fieldSpec`
        let mut splitDflt : Array (Option Term) := subs.map fun _ => none
        match dflt? with
        | some d =>
            if d.params.isEmpty then
              try
                let mut acc := #[]
                for sub in subs do
                  let v ← evalCol (← mkAppM ``LeanDb.ColCodec.toCol #[← mkProjection d.value sub.name])
                  acc := acc.push (some (← colLitStx v))
                splitDflt := acc
              catch ex =>
                logWarning m!"{who}: default of '{declName}.{fname}' could not be evaluated ({ex.toMessageData}) — JSON inserts must supply it"
            else
              logWarning m!"{who}: default of '{declName}.{fname}' depends on other fields and is not reified — JSON inserts must supply it"
        | none => pure ()
        let mut cols : Array ColGen := #[]
        for j in [0:subs.size] do
          let sub := subs[j]!
          let colName := s!"{fname}_{sub.name}"
          let getStx ← `($(mkCIdent (ftype.getAppFn.constName! ++ sub.name)) ($(mkCIdent (declName ++ fname)) r))
          let base ← `(LeanDb.Inline.fieldSpec (α := $tyStx) $(mkCIdent sub.sym))
          let specStx ← match splitDflt[j]! with
            | some lit => `({ $base with name := $(quote colName), group := some $(quote fname.toString), dflt := some $lit })
            | none => `({ $base with name := $(quote colName), group := some $(quote fname.toString) })
          cols := cols.push {
            symName := Name.mkSimple colName, colName, tyStx := sub.tyStx, getStx
            codecStx := ← `((inferInstance : LeanDb.ColCodec $(sub.tyStx)))
            specStx
            encStx := ← `(LeanDb.ColCodec.toCol $getStx)
            canRefuse := tyCanRefuse sub.ty }
        gens := gens.push { fname, cols, enc := .inline tyStx nextCol subs.size }
        nextCol := nextCol + subs.size
        continue
      -- a scalar field: one column. Its `:= default` is reified by
      -- EVALUATING it here, at elaboration time, with its definition-site
      -- instances — then the literal is embedded in the column spec (DDL
      -- DEFAULT, JSON omission, migration backfill all read it from there).
      -- A `derived` default is reified as a *function* of its sources.
      let mut recompute : Option (Term × Array Nat) := none
      let dfltStx : Term ← do
        match dflt? with
        | some d =>
            if d.params.isEmpty then
              if d.isDerived then
                throwError "{who}: field '{fname}' of {declName} is marked `derived` but its default does not depend on other fields"
              try
                let v ← evalCol (← mkAppM ``LeanDb.ColCodec.toCol #[d.value])
                `(some $(← colLitStx v))
              catch ex =>
                logWarning m!"{who}: default of '{declName}.{fname}' could not be evaluated ({ex.toMessageData}) — JSON inserts must supply it"
                `((none : Option LeanDb.Col))
            else if d.isDerived then
              unless entity do
                throwError "{who}: field '{fname}' of {declName} is marked `derived`; derived columns belong to entities, not inline structures"
              let idxs ← d.params.mapM fun p => do
                match fields.findIdx? (· == p) with
                | some j => if j < i then pure j else
                    throwError "{who}: derived field '{fname}' of {declName} depends on '{p}', which is not an earlier field"
                | none => throwError "{who}: derived field '{fname}' of {declName} depends on '{p}', which is not a field"
              recompute := some (← delabFull d.value, idxs)
              `((none : Option LeanDb.Col))
            else
              logWarning m!"{who}: default of '{declName}.{fname}' depends on other fields and is not reified — JSON inserts must supply it{if entity then " (mark it `derived` to have LeanDB compute it)" else ""}"
              `((none : Option LeanDb.Col))
        | none => `((none : Option LeanDb.Col))
      let getStx ← `($(mkCIdent (declName ++ fname)) r)
      let encStx ← match recompute with
        | some (fn, idxs) =>
            let args ← idxs.mapM fun j => `($(mkCIdent (declName ++ fields[j]!)) r)
            `(LeanDb.ColCodec.toCol (($fn) $args*))
        | none => `(LeanDb.ColCodec.toCol $getStx)
      let specStx ← match cascade.find? (·.1 == fname) with
        | some (_, target) =>
            `({ LeanDb.columnSpec $(quote fname.toString) $tyStx $dfltStx with
                fkTable := some $(quote target), cascade := true })
        | none =>
            if declaredCascade.contains fname then
              `({ LeanDb.columnSpec $(quote fname.toString) $tyStx $dfltStx with
                  cascade := true })
            else
              `(LeanDb.columnSpec $(quote fname.toString) $tyStx $dfltStx)
      let col : ColGen := {
        symName := fname, colName := fname.toString, tyStx, getStx
        codecStx := ← `((inferInstance : LeanDb.ColCodec $tyStx))
        specStx, encStx, recompute, canRefuse := tyCanRefuse ftype }
      gens := gens.push { fname, cols := #[col], enc := .plain fname.toString tyStx nextCol }
      nextCol := nextCol + 1
    -- flattened names must not collide with anything else
    let names := gens.foldl (fun acc g => acc ++ g.cols.map (·.colName)) #[]
    for n in names, k in [0:names.size] do
      if (names.extract 0 k).contains n then
        throwError "{who}: {declName} generates column '{n}' twice (a flattened inline column collides with another field)"
    return gens

/-- Everything the two instance bodies share, built from the walk. -/
private structure Built where
  fieldTyFn : Term
  getFn : Term
  codecFn : Term
  specFn : Term
  derivedFn : Term
  syms : Array Term
  encode : Term
  /-- Conjunction of `toSql?.isSome` for each column (`true` if none). -/
  rangeOk : Term
  /-- Number of columns. -/
  n : Nat

private def buildShared (declName : Name) (gens : Array FieldGen) : TermElabM Built := do
  let fieldTyName := declName ++ `Field
  let cols := gens.foldl (fun acc g => acc ++ g.cols) #[]
  let mut tyAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut getAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut codecAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut specAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut derivedAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
  let mut syms : Array Term := #[]
  for c in cols do
    let sym : Ident := mkCIdent (fieldTyName ++ c.symName)
    syms := syms.push sym
    tyAlts := tyAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $sym:ident => $(c.tyStx)))
    getAlts := getAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $sym:ident => $(c.getStx)))
    codecAlts := codecAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $sym:ident => $(c.codecStx)))
    specAlts := specAlts.push (← `(Lean.Parser.Term.matchAltExpr| | $sym:ident => $(c.specStx)))
    derivedAlts := derivedAlts.push
      (← `(Lean.Parser.Term.matchAltExpr| | $sym:ident => $(quote c.recompute.isSome)))
  -- A zero-field structure has an empty symbol type: every function over
  -- it is `nomatch`.
  let bySym (alts : Array (TSyntax ``Lean.Parser.Term.matchAlt)) : TermElabM Term :=
    if cols.isEmpty then `(fun f => nomatch f)
    else `(fun f => match f with $alts:matchAlt*)
  let getFn ←
    if cols.isEmpty then `(fun f _ => nomatch f)
    else `(fun f r => match f with $getAlts:matchAlt*)
  -- encode: literal runs of scalar columns, inline values spliced in
  let mut pieces : Array Term := #[]
  let mut run : Array Term := #[]
  for g in gens do
    match g.enc with
    | .plain .. => run := run.push g.cols[0]!.encStx
    | .inline tyStx _ _ =>
        unless run.isEmpty do pieces := pieces.push (← `(#[$run,*])); run := #[]
        pieces := pieces.push (← `(LeanDb.Inline.encode (α := $tyStx) ($(mkCIdent (declName ++ g.fname)) r)))
    | .child .. => pure ()   -- a child list is not a column
  if pieces.isEmpty || !run.isEmpty then pieces := pieces.push (← `(#[$run,*]))
  let mut encode := pieces[0]!
  for p in pieces[1:] do encode ← `($encode ++ $p)
  -- `rangeOk`: `true` when no column can refuse encoding; otherwise a
  -- conjunction of `toSql?.isSome` so `Nat` above `Int64.maxValue` is
  -- excluded from `Checked`. Always-encodable columns (String, Ref, …)
  -- are omitted so `rangeOk` is definitionally `true` and `decide` works
  -- on free rows.
  let mut checks : Array Term := #[]
  for c in cols do
    if c.canRefuse then
      checks := checks.push (← `((LeanDb.ColCodec.toSql? (α := $(c.tyStx)) $(c.getStx)).isSome))
  let rangeOk ←
    if checks.isEmpty then `(fun _ => true)
    else
      let mut body := checks[0]!
      for c in checks[1:] do
        body ← `($body && $c)
      `(fun r => $body)
  return { fieldTyFn := ← bySym tyAlts, getFn, codecFn := ← bySym codecAlts
           specFn := ← bySym specAlts, derivedFn := ← bySym derivedAlts, syms
           encode := ← `(fun r => $encode), rangeOk, n := cols.size }

/-- The decode body: a right fold of per-field binds ending in the
    constructor. `table = some t` is an entity (typed `DbError`s; with
    `checking`, a derived column is decoded and compared with its
    recomputation, otherwise recomputed and the stored value ignored);
    `none` is an inline structure (`String` errors of the form
    `"<field>: <message>"`). -/
private def mkDecodeBody (declName : Name) (gens : Array FieldGen) (table : Option String)
    (checking : Bool) : TermElabM Term := do
  let ctorName := (← getConstInfoInduct declName).ctors.head!
  let ctorArgs := (Array.range gens.size).map fun i => (fieldBinder i : Term)
  let recomputed (fn : Term) (idxs : Array Nat) : TermElabM Term :=
    let args : Array Term := idxs.map fun j => (fieldBinder j : Term)
    `(($fn) $args*)
  let mut body : Term ← `(Except.ok ($(mkCIdent ctorName) $ctorArgs*))
  if checking then
    if let some tbl := table then
      for i in (List.range gens.size).reverse do
        if let some (fn, idxs) := gens[i]!.cols.getD 0 default |>.recompute then
          -- a column computed from a child list cannot be checked here (the
          -- list is attached later): its `ChildLink.attach` checks it
          if idxs.any (fun j => gens[j]!.enc.isChild) then continue
          body ← `(if $(fieldBinder i) == $(← recomputed fn idxs) then $body
                   else Except.error (LeanDb.DbError.decode $(quote tbl)
                     $(quote gens[i]!.fname.toString) "derived column disagrees with its source"))
  for i in (List.range gens.size).reverse do
    let g := gens[i]!
    match g.enc, table with
    | .child .., _ =>
        body ← `(let $(fieldBinder i) := []; $body)
    | .inline tyStx start len, some tbl =>
        body ← `(Except.mapError (LeanDb.inlineDecodeError $(quote tbl) $(quote g.fname.toString))
                   (LeanDb.Inline.decode (α := $tyStx) (row.extract $(quote start) $(quote (start + len))))
                 >>= fun $(fieldBinder i) => $body)
    | .inline .., none => throwError "deriving LeanDb.Inline: internal error — inline field inside an inline structure"
    | .plain colName tyStx col, some tbl =>
        match g.cols[0]!.recompute with
        | some (fn, idxs) =>
            if checking then
              body ← `(LeanDb.decodeField $(quote tbl) $(quote colName) $tyStx (row.getD $(quote col) .null)
                         >>= fun $(fieldBinder i) => $body)
            else
              body ← `(let $(fieldBinder i) : $tyStx := $(← recomputed fn idxs); $body)
        | none =>
            body ← `(LeanDb.decodeField $(quote tbl) $(quote colName) $tyStx (row.getD $(quote col) .null)
                       >>= fun $(fieldBinder i) => $body)
    | .plain colName tyStx col, none =>
        body ← `(LeanDb.decodeFieldStr $(quote colName) $tyStx (row.getD $(quote col) .null)
                   >>= fun $(fieldBinder i) => $body)
  return body

/-- Declare the symbol inductive `declName.Field` with one constructor per
    generated column. Under `_root_` so the current namespace is not
    prepended; a private structure gets a private symbol type (re-mangled
    to exactly `declName ++ Field` — same module). -/
private def declareSymbols (who : String) (declName : Name) (gens : Array FieldGen) :
    CommandElabM Unit := do
  let fieldTyName := declName ++ `Field
  let symId := rootIdent fieldTyName
  let cols := gens.foldl (fun acc g => acc ++ g.cols) #[]
  let ctors ← cols.mapM fun c => `(Lean.Parser.Command.ctor| | $(mkIdent c.symName):ident)
  let symCmd ←
    if isPrivateName declName then
      `(private inductive $symId:ident where $ctors* deriving DecidableEq, Repr)
    else
      `(inductive $symId:ident where $ctors* deriving DecidableEq, Repr)
  elabCommand symCmd
  unless (← getEnv).contains fieldTyName do
    throwError "{who}: failed to declare '{fieldTyName}'"

/-- The checks both derives make before anything is declared. -/
private def checkStructure (who : String) (declName : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless isStructure env declName do
    throwError "{who}: {declName} is not a structure"
  let indVal ← getConstInfoInduct declName
  unless indVal.numParams == 0 && indVal.numIndices == 0 do
    throwError "{who}: {declName} must not have type parameters"
  let fieldTyName := declName ++ `Field
  if env.contains fieldTyName then
    throwError "{who}: {declName} already declares '{fieldTyName}'; LeanDB generates the field symbols under that name"

/-! ## Child tables (LEP-0003 D)

For a field `ins : List R` of `Parent` with `R` an `Inline` record, the
derive declares the child entity and describes it to the parent. -/

/-- The structure literal `{ r with f := v }` as syntax. -/
private def withField (r : Term) (f : Name) (v : Term) : TermElabM Term :=
  `({ $r with $(mkIdent f):ident := $v })

/-- Declare `Parent.Ins` (`parent`, `position`, then `R`'s fields verbatim),
    derive its entity under the table `<parentTable>_<field>` with a
    cascading `parent`, and declare `record`/`ofRecord`. Returns the child
    entity's name. `deriveChild` is what makes `deriveEntityCore` recursive:
    a child has no children of its own (an `Inline` record refuses lists),
    so the recursion is one level deep. -/
private partial def deriveChild (who : String) (declName : Name) (tblName : String)
    (fname : Name) (elemTy : Expr)
    (deriveEntityCore : Name → Option String → Array (Name × String) → CommandElabM Bool) :
    CommandElabM Name := do
  let childName := childTypeName declName fname
  let env ← getEnv
  if env.contains childName then
    throwError "{who}: field '{fname}' of {declName} is a child list, but '{childName}' already exists; LeanDB generates the child entity under that name"
  let .const rname _ := elemTy.getAppFn |
    throwError "{who}: field '{fname}' of {declName}: the record type {elemTy} is not a plain structure"
  let subs ← liftTermElabM (inlineSubFields who declName fname elemTy)
  for sub in subs do
    if sub.name == `parent || sub.name == `position then
      throwError "{who}: field '{fname}' of {declName}: the record {rname} has a field '{sub.name}', which is the name of the child table's key column; rename it"
  let rFields := getStructureFields env rname
  -- 1. the structure
  let structCmd ← liftTermElabM do
    let mut binders : Array (TSyntax ``Lean.Parser.Command.structSimpleBinder) := #[]
    binders := binders.push (← `(Lean.Parser.Command.structSimpleBinder|
      parent : LeanDb.Ref $(mkCIdent declName)))
    binders := binders.push (← `(Lean.Parser.Command.structSimpleBinder| position : Nat))
    for sub in subs do
      let tyStx ← delabFull sub.ty
      let fid := mkIdent sub.name
      match ← defaultInfo? rname sub.name rFields with
      | some d =>
          let args : Array Term := d.params.map fun p => (mkIdent p : Term)
          let dfltTerm : Term ← if args.isEmpty then delabFull (stripIdMData d.value)
            else `(($(← delabFull d.value)) $args*)
          binders := binders.push (← `(Lean.Parser.Command.structSimpleBinder| $fid:ident : $tyStx := $dfltTerm))
      | none =>
          binders := binders.push (← `(Lean.Parser.Command.structSimpleBinder| $fid:ident : $tyStx))
    let childId := rootIdent childName
    if isPrivateName declName then
      `(private structure $childId:ident where $[$binders]*)
    else
      `(structure $childId:ident where $[$binders]*)
  elabCommand structCmd
  unless (← getEnv).contains childName do
    throwError "{who}: failed to declare the child entity '{childName}'"
  -- 2. its entity: the child's table, `parent` cascading
  discard <| deriveEntityCore childName (some s!"{tblName}_{fname}") #[(`parent, tblName)]
  -- 3. record ↔ child
  let defs ← liftTermElabM do
    let rCtor := (← getConstInfoInduct rname).ctors.head!
    let cCtor := (← getConstInfoInduct childName).ctors.head!
    let recordArgs ← subs.mapM fun sub => `($(mkCIdent (childName ++ sub.name)) c)
    let ofRecordArgs ← subs.mapM fun sub => `($(mkCIdent (rname ++ sub.name)) r)
    let rStx ← delabFull elemTy
    let recordCmd ← `(def $(rootIdent (childName ++ `record)):ident (c : $(mkCIdent childName)) : $rStx :=
      $(mkCIdent rCtor) $recordArgs*)
    let ofRecordCmd ← `(def $(rootIdent (childName ++ `ofRecord)):ident
        (parent : LeanDb.Ref $(mkCIdent declName)) (position : Nat) (r : $rStx) : $(mkCIdent childName) :=
      $(mkCIdent cCtor) parent position $ofRecordArgs*)
    pure (recordCmd, ofRecordCmd)
  elabCommand defs.1
  elabCommand defs.2
  return childName

/-- The `ChildLink` literal for the child list at field index `ci`. Derived
    columns computed from child lists are checked (`attach`) or recomputed
    (`attachRecomputing`) by the link of the *last* list they read, so
    every list they need is attached by then. -/
private def mkChildLink (declName : Name) (tblName : String) (gens : Array FieldGen)
    (ci : Nat) (childName : Name) : TermElabM Term := do
  let g := gens[ci]!
  let .child _ elemStx := g.enc | throwError "deriving LeanDb.Entity: internal error — not a child field"
  let fname := g.fname
  let childTbl := s!"{tblName}_{fname}"
  let proj := mkCIdent (declName ++ fname)
  let rows ← `(fun r => (($proj r).map fun x => LeanDb.Inline.encode (α := $elemStx) x).toArray)
  let decodeList ← `(rows.mapM fun p =>
    Except.mapError (LeanDb.childDecodeError $(quote childTbl)) (LeanDb.Inline.decode (α := $elemStx) p.2))
  -- the derived columns this link owns
  let mut owned : Array (Nat × Term × Array Nat) := #[]
  for j in [0:gens.size] do
    if let some (fn, idxs) := (gens[j]!.cols.getD 0 default).recompute then
      let childIdxs := idxs.filter fun k => gens[k]!.enc.isChild
      if childIdxs.back? == some ci then owned := owned.push (j, fn, idxs)
  let recomputeOf (fn : Term) (idxs : Array Nat) : TermElabM Term := do
    let args ← idxs.mapM fun j => `($(mkCIdent (declName ++ gens[j]!.fname)) r)
    `(($fn) $args*)
  -- attach: set the list, check the owned derived columns
  let attachBody ← do
    let mut body : Term ← `(Except.ok r)
    for (j, fn, idxs) in owned.reverse do
      body ← `(if $(mkCIdent (declName ++ gens[j]!.fname)) r == $(← recomputeOf fn idxs) then $body
               else Except.error (LeanDb.DbError.decode $(quote tblName)
                 $(quote gens[j]!.fname.toString) "derived column disagrees with its source"))
    let set ← withField (← `(r)) fname (← `(xs.toList))
    `(fun rows r => $decodeList >>= fun xs =>
        let r : $(mkCIdent declName) := $set
        $body)
  -- attachRecomputing: set the list, recompute the owned derived columns
  let attachRecBody ← do
    let mut body : Term ← `(Except.ok r)
    for (j, fn, idxs) in owned.reverse do
      let set ← withField (← `(r)) gens[j]!.fname (← recomputeOf fn idxs)
      body ← `(let r : $(mkCIdent declName) := $set
               $body)
    let set ← withField (← `(r)) fname (← `(xs.toList))
    `(fun rows r => $decodeList >>= fun xs =>
        let r : $(mkCIdent declName) := $set
        $body)
  `({ field := $(quote fname.toString)
      table := $(quote childTbl)
      spec := LeanDb.Entity.spec $(mkCIdent childName)
      rows := $rows
      attach := $attachBody
      attachRecomputing := $attachRecBody : LeanDb.ChildLink $(mkCIdent declName) })

/-- Refuse the field/column names `unusableSymNames` covers: the generated
    symbol inductive cannot declare them, and the failure would otherwise
    be an unattributed kernel or parser error. -/
private def checkSymNames (who : String) (declName : Name) (gens : Array FieldGen) :
    TermElabM Unit := do
  for g in gens do
    for c in g.cols do
      if unusableSymNames.contains c.colName then
        throwError "{who}: {declName} declares field '{c.colName}', whose name cannot be \
generated as a LeanDB field symbol (an inductive constructor with that name is refused by Lean); \
rename the field"

/-- `@[leandb_invariant]` marks `T.invariant : T → Bool` as the condition
    every stored `T` satisfies (LDB-16). `deriving LeanDb.Entity` for `T`
    reads it, so it is declared first, and the instance derived after it
    (`deriving instance LeanDb.Entity for T`). Tagging it once `Entity T`
    exists is refused: that instance would never check it. -/
initialize invariantAttr : TagAttribute ←
  registerTagAttribute `leandb_invariant
    "the condition LeanDB checks on every stored value of its type (LDB-16)"
    fun declName => do
      let .str typeName "invariant" := declName
        | throwError "@[leandb_invariant]: name the check `<Type>.invariant`, got {declName}"
      let info ← getConstInfo declName
      match info.type with
      | .forallE _ (.const t []) (.const b []) _ =>
          unless t == typeName && b == ``Bool do
            throwError "@[leandb_invariant]: {declName} must have type {typeName} → Bool"
      | _ => throwError "@[leandb_invariant]: {declName} must have type {typeName} → Bool"
      let derived ← Meta.MetaM.run' do
        return (← Meta.synthInstance? (mkApp (mkConst ``LeanDb.Entity) (mkConst typeName))).isSome
      if derived then
        throwError "@[leandb_invariant]: LeanDb.Entity {typeName} already exists and would \
not check {declName}. Declare the invariant first, then \
`deriving instance LeanDb.Entity for {typeName}`."

/-- `cascade% User.team` — this `Ref` is `ON DELETE CASCADE`. Must be
    declared before `deriving LeanDb.Entity`. Default is RESTRICT. -/
structure CascadeDecl where
  typeName : Name
  field : Name
  deriving Repr, BEq

initialize cascadeExt : EnvExtension (Array CascadeDecl) ←
  registerEnvExtension (pure #[])

syntax (name := cascadeCmd) "cascade% " ident : command

@[command_elab cascadeCmd]
def elabCascade : CommandElab := fun stx => do
  let `(cascade% $id:ident) := stx | throwUnsupportedSyntax
  let n := id.getId
  let field := Name.mkSimple n.getString!
  let rawType := n.getPrefix
  if rawType.isAnonymous then
    throwError "cascade%: expected `Type.field`, got {n}"
  let env ← getEnv
  let ns := (← getCurrNamespace)
  let typeName :=
    if isStructure env rawType then rawType
    else if isStructure env (ns ++ rawType) then ns ++ rawType
    else rawType
  unless isStructure env typeName do
    throwError "cascade%: {rawType} is not a structure"
  unless (getStructureFields env typeName).any (· == field) do
    throwError "cascade%: {typeName} has no field '{field}'"
  let has ← liftTermElabM do
    return (← Meta.synthInstance?
      (mkApp (mkConst ``LeanDb.Entity) (mkConst typeName))).isSome
  if has then
    throwError "cascade%: LeanDb.Entity {typeName} already exists; declare `cascade%` first, then derive"
  if (cascadeExt.getState env).any fun e => e.typeName == typeName && e.field == field then
    throwError "cascade%: {n} is already declared"
  modifyEnv (cascadeExt.modifyState · (·.push { typeName, field }))

/-- `deriving LeanDb.Entity` for `declName`. `tableName?` overrides the
    table name (a generated child's `<parent>_<field>`); `cascade` names
    the `Ref` fields whose FK cascades and the table each references (a
    child's `parent`). -/
partial def deriveEntityCore (declName : Name) (tableName? : Option String := none)
    (cascade : Array (Name × String) := #[]) : CommandElabM Bool := do
  let who := "deriving LeanDb.Entity"
  checkStructure who declName
  let env ← getEnv
  let fields := getStructureFields env declName
  let tblName := tableName?.getD (tableNameOf declName)
  if tblName.startsWith "_leandb_" then
    throwError "{who}: table name '{tblName}' uses the reserved _leandb_ prefix"
  if fields.any (·.getString! == "id") then
    throwError "{who}: field 'id' is reserved for LeanDB row identity"
  let fieldTyName := declName ++ `Field
  -- 1. The walk, then the field symbols (one per column: an inline field
  --    contributes `field_sub` for each of its sub-fields; a child list none).
  let gens ← liftTermElabM (walkFields who declName (entity := true) cascade
    ((cascadeExt.getState env).filterMap fun e =>
      if e.typeName == declName then some e.field else none))
  liftTermElabM (checkSymNames who declName gens)
  declareSymbols who declName gens
  -- 2. The child entities, one per child list, each with its own symbols
  --    and instance — declared before the parent's instance names them.
  let mut childNames : Array (Nat × Name) := #[]
  for i in [0:gens.size] do
    if let .child elemTy _ := gens[i]!.enc then
      let childName ← deriveChild who declName tblName gens[i]!.fname elemTy
        (fun n t c => deriveEntityCore n t c)
      childNames := childNames.push (i, childName)
  -- 3. The instances.
  let invName := declName ++ `invariant
  let hasInvariant := invariantAttr.hasTag (← getEnv) invName
  let cmds ← liftTermElabM do
    let b ← buildShared declName gens
    let invariant : Term ←
      if hasInvariant then `(some ($(quote (toString invName)), $(mkCIdent invName)))
      else `(none)
    let bodyCheck ← mkDecodeBody declName gens (some tblName) (checking := true)
    let bodyRecompute ← mkDecodeBody declName gens (some tblName) (checking := false)
    let links ← childNames.mapM fun (i, childName) => mkChildLink declName tblName gens i childName
    let n := quote b.n
    -- `@[reducible]`: instance lookup only sees through `Entity.fieldTy f`
    -- to the field's type if the instance unfolds at reducible transparency
    -- (see `LeanDb.Entity`).
    let entityCmd : TSyntax `command ← `(@[reducible] instance : LeanDb.Entity $(mkCIdent declName) where
        Field := $(mkCIdent fieldTyName)
        fieldTy := $(b.fieldTyFn)
        get := $(b.getFn)
        codec := $(b.codecFn)
        fieldSpec := $(b.specFn)
        fields := #[$(b.syms),*]
        tableName := $(quote tblName)
        typeName := $(quote (toString declName))
        encode := $(b.encode)
        decode := fun row =>
          if row.size == $n then $bodyCheck
          else Except.error (LeanDb.DbError.decode $(quote tblName) "*"
                 s!"expected {$n} columns, found {row.size}")
        isDerived := $(b.derivedFn)
        decodeRecomputing := fun row =>
          if row.size == $n then $bodyRecompute
          else Except.error (LeanDb.DbError.decode $(quote tblName) "*"
                 s!"expected {$n} columns, found {row.size}")
        children := [$links,*]
        invariant := $invariant
        rangeOk := $(b.rangeOk))
    let fieldOfCmd : TSyntax `command ← `(@[reducible] instance :
        LeanDb.FieldOf $(mkCIdent fieldTyName) $(mkCIdent declName) := ⟨fun f => f⟩)
    return (entityCmd, fieldOfCmd)
  elabCommand cmds.1
  elabCommand cmds.2
  return true

def deriveEntity (declName : Name) : CommandElabM Bool := deriveEntityCore declName

def entityHandler : DerivingHandler := fun declNames => do
  for declName in declNames do
    discard <| deriveEntity declName
  return true

initialize registerDerivingHandler ``LeanDb.Entity entityHandler

/-! ## `deriving LeanDb.Inline` -/

def deriveInline (declName : Name) : CommandElabM Bool := do
  let who := "deriving LeanDb.Inline"
  checkStructure who declName
  let fieldTyName := declName ++ `Field
  let gens ← liftTermElabM (walkFields who declName (entity := false))
  liftTermElabM (checkSymNames who declName gens)
  declareSymbols who declName gens
  let cmds ← liftTermElabM do
    let b ← buildShared declName gens
    let body ← mkDecodeBody declName gens none (checking := false)
    let n := quote b.n
    let inlineCmd : TSyntax `command ← `(@[reducible] instance : LeanDb.Inline $(mkCIdent declName) where
        Field := $(mkCIdent fieldTyName)
        fieldTy := $(b.fieldTyFn)
        get := $(b.getFn)
        codec := $(b.codecFn)
        fieldSpec := $(b.specFn)
        fields := #[$(b.syms),*]
        encode := $(b.encode)
        decode := fun row =>
          if row.size == $n then $body
          else Except.error s!"*: expected {$n} columns, found {row.size}")
    let fieldOfCmd : TSyntax `command ← `(@[reducible] instance :
        LeanDb.Inline.FieldOf $(mkCIdent fieldTyName) $(mkCIdent declName) := ⟨fun f => f⟩)
    return (inlineCmd, fieldOfCmd)
  elabCommand cmds.1
  elabCommand cmds.2
  return true

def inlineHandler : DerivingHandler := fun declNames => do
  for declName in declNames do
    discard <| deriveInline declName
  return true

initialize registerDerivingHandler ``LeanDb.Inline inlineHandler

/-! ## `deriving LeanDb.ClosedEnum` -/

def deriveClosedEnum (declName : Name) : CommandElabM Bool := do
  let indVal ← getConstInfoInduct declName
  unless indVal.numParams == 0 && indVal.numIndices == 0 do
    throwError "deriving LeanDb.ClosedEnum: {declName} must not have type parameters"
  for c in indVal.ctors do
    let ci ← getConstInfoCtor c
    unless ci.numFields == 0 do
      throwError "deriving LeanDb.ClosedEnum: constructor '{c}' carries data; only payload-free inductives are closed worlds (stored sums are planned separately)"
  let names := indVal.ctors.map (·.getString!)
  let cmd ← liftTermElabM do
    let variantTerms : Array Term := (names.map fun n => (quote n : Term)).toArray
    -- The scalar `Nat` motive matters: a `String`-motive casesOn inside a
    -- closed term (e.g. a reified field default) panics the compiler's
    -- boxing pass on this toolchain; an index into the variants array
    -- compiles everywhere.
    let idxArms : Array Term := (List.range names.length).toArray.map fun i => quote i
    let enc ← `(
      let vs : Array String := #[$variantTerms,*]
      fun x => vs[$(mkCIdent (declName ++ `casesOn)) (motive := fun _ => Nat) x $idxArms*]!)
    let mut dec : Term ← `((none : Option $(mkCIdent declName)))
    for (ctor, n) in (indVal.ctors.zip names).reverse do
      dec ← `(if s == $(quote n) then some $(mkCIdent ctor) else $dec)
    let ctorTerms : Array Term := (indVal.ctors.map fun c => (mkCIdent c : Term)).toArray
    `(instance : LeanDb.ClosedEnum $(mkCIdent declName) where
        variants := #[$variantTerms,*]
        all := #[$ctorTerms,*]
        encodeName := $enc
        decodeName := fun s => $dec)
  elabCommand cmd
  return true

def closedEnumHandler : DerivingHandler := fun declNames => do
  for declName in declNames do
    discard <| deriveClosedEnum declName
  return true

initialize registerDerivingHandler ``LeanDb.ClosedEnum closedEnumHandler

/-! ## `deriving LeanDb.DbJson` -/

/-- The name a shape uses for a nested type: the last component. -/
private def shapeName (n : Name) : String :=
  ((privateToUserName? n).getD n).getString!

private def shapeDelims : List Char :=
  ['{', '}', '(', ')', '<', '>', '[', ']', ',', '|', ':', '?', '=']

private def checkShapeName (what : String) (n : Name) : TermElabM Unit := do
  let s := n.getString!
  if s.any (shapeDelims.contains ·) then
    throwError "deriving LeanDb.DbJson: {what} '{n}' contains a character reserved by the shape grammar ({shapeDelims})"

/-- The shape of a type expression, as a `String`-valued term: containers
    are walked here (so a recursive reference renders as the type's bare
    name instead of looping), nested types go through their `JsonShape`
    instance at run time, closed enums through their variant list. -/
private partial def shapeTerm (declName : Name) (owner : String) (ty : Expr) : TermElabM Term := do
  let ty ← instantiateMVars ty
  let ty := ty.consumeMData
  if ty.isConstOf declName then return quote (shapeName declName)
  let args := ty.getAppArgs
  match ty.getAppFn.constName?, args.size with
  | some ``List, 1 | some ``Array, 1 => `(LeanDb.JsonShape.list $(← shapeTerm declName owner args[0]!))
  | some ``Option, 1 => `(LeanDb.JsonShape.option $(← shapeTerm declName owner args[0]!))
  | some ``Prod, 2 =>
      `(LeanDb.JsonShape.pair $(← shapeTerm declName owner args[0]!) $(← shapeTerm declName owner args[1]!))
  | _, _ =>
      if (ty.find? (·.isConstOf declName)).isSome then
        throwError "deriving LeanDb.DbJson: {owner}: a recursive occurrence of {declName} inside {ty} is only supported under List, Array, Option and pairs"
      let tyStx ← delabFull ty
      if (← synthInstance? (← mkAppM ``LeanDb.JsonShape #[ty])).isSome then
        `(LeanDb.JsonShape.shape $tyStx)
      else if (← synthInstance? (← mkAppM ``LeanDb.ClosedEnum #[ty])).isSome then
        `(LeanDb.JsonShape.closed (LeanDb.ClosedEnum.variants $tyStx))
      else
        throwError "deriving LeanDb.DbJson: {owner} has type {ty}, which has no JsonShape — derive LeanDb.DbJson for it, or declare `instance : LeanDb.JsonShape {ty}`"

/-- Does any constructor field of `declName` mention `declName`? -/
private def isSelfReferential (declName : Name) : MetaM Bool := do
  let indVal ← getConstInfoInduct declName
  indVal.ctors.anyM fun c => do
    let ci ← getConstInfoCtor c
    forallTelescopeReducing ci.type fun xs _ =>
      xs.anyM fun x => do return ((← inferType x).find? (·.isConstOf declName)).isSome

def deriveDbJson (declName : Name) : CommandElabM Bool := do
  let env ← getEnv
  let indVal ← getConstInfoInduct declName
  unless indVal.numParams == 0 && indVal.numIndices == 0 do
    throwError "deriving LeanDb.DbJson: {declName} must not have type parameters"
  let selfId := mkCIdent declName
  let toFn := declName ++ `leandbToJson
  let fromFn := declName ++ `leandbFromJson
  let toId := rootIdent toFn
  let fromId := rootIdent fromFn
  -- inside their own bodies the functions are named without `_root_`
  let toRef := mkIdent ((privateToUserName? toFn).getD toFn)
  let fromRef := mkIdent ((privateToUserName? fromFn).getD fromFn)
  let errPrefix (field : Name) : String := s!"{(privateToUserName? declName).getD declName}.{field}: "
  let cmds ← liftTermElabM do
    let selfRef ← isSelfReferential declName
    let (toBody, fromBody, shape) ← if isStructure env declName then do
      -- structure: an object, one key per (flattened) field
      let fields := getStructureFieldsFlattened env declName (includeSubobjectFields := false)
      for f in fields do checkShapeName "field" f
      let allFields := getStructureFields env declName
      withLocalDeclD `x (mkConst declName) fun x => do
        let mut pairs : Array Term := #[]
        let mut getters : Array (TSyntax ``Lean.Parser.Term.doSeqItem) := #[]
        let mut shapeFields : Array Term := #[]
        for f in fields do
          let proj ← mkProjection x f
          let fty ← inferType proj
          if fty.containsFVar x.fvarId! then
            throwError "deriving LeanDb.DbJson: field '{f}' of {declName} depends on another field; dependent fields are not stored — declare `instance : LeanDb.DbJson … := LeanDb.DbJson.via encode parse` for the field's type over its data representation"
          let key := quote f.toString
          let fId := mkIdent f
          let ftyStx ← delabFull fty
          pairs := pairs.push (← `(($key, Lean.toJson ($(mkIdent `x)).$fId:ident)))
          let dflt? ← defaultInfo? declName f allFields
          let required ← `(Except.mapError (fun s => $(quote (errPrefix f)) ++ s)
            (Lean.Json.getObjValAs? json $ftyStx $key))
          match dflt? with
          | some d =>
              let fnStx ← delabFull d.value
              let args : Array Term := d.params.map fun p => (mkIdent p : Term)
              let dfltTerm : Term ← if args.isEmpty then pure fnStx else `(($fnStx) $args*)
              let rhs ← `(Except.mapError (fun s => $(quote (errPrefix f)) ++ s)
                (LeanDb.jsonFieldOr json $key (fun _ => $dfltTerm)))
              getters := getters.push (← `(Lean.Parser.Term.doSeqItem| let $fId:ident : $ftyStx ← $rhs:term))
          | none =>
              getters := getters.push (← `(Lean.Parser.Term.doSeqItem| let $fId:ident : $ftyStx ← $required:term))
          shapeFields := shapeFields.push
            (← `(($key, $(← shapeTerm declName s!"field '{f}' of {declName}" fty), $(quote dflt?.isSome))))
        let fieldIds := fields.map mkIdent
        let toBody ← `(fun ($(mkIdent `x) : $selfId) => Lean.Json.mkObj [$pairs,*])
        let fromBody ← `(fun (json : Lean.Json) => do
          $getters*
          return { $[$fieldIds:ident := $(id fieldIds)],* })
        let shape ← `(LeanDb.JsonShape.struct $(quote (shapeName declName)) [$shapeFields,*])
        pure (toBody, fromBody, shape)
    else do
      -- inductive: Lean's constructor-tagged encoding
      let mut toAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
      let mut fromAlts : Array (TSyntax ``Lean.Parser.Term.matchAlt) := #[]
      let mut shapeCtors : Array Term := #[]
      for ctorName in indVal.ctors do
        let ci ← getConstInfoCtor ctorName
        let ctorStr := ctorName.eraseMacroScopes.getString!
        checkShapeName "constructor" (Name.mkSimple ctorStr)
        let (toAlt, fromAlt, shapeCtor) ← forallTelescopeReducing ci.type fun xs _ => do
          let mut binders : Array Ident := #[]
          let mut tys : Array Expr := #[]
          let mut userNames : Array Name := #[]
          for i in [0:ci.numFields] do
            let x := xs[i]!
            let decl ← x.fvarId!.getDecl
            if (Array.ofSubarray xs[0:i]).any (fun y => decl.type.containsFVar y.fvarId!) then
              throwError "deriving LeanDb.DbJson: constructor '{ctorName}' has a dependent field; dependent fields are not stored — declare `instance : LeanDb.DbJson … := LeanDb.DbJson.via encode parse` for the field's type over its data representation"
            unless decl.userName.hasMacroScopes do
              userNames := userNames.push decl.userName
            binders := binders.push (mkIdent (← mkFreshUserName `a))
            tys := tys.push decl.type
          let named := userNames.size == binders.size
          if named then for u in userNames do checkShapeName "constructor field" u
          let ctorId := mkCIdent ctorName
          -- encode
          let payload : Term ← match binders.size, named with
            | 0, _ => `(Lean.toJson $(quote ctorStr))
            | 1, false => `(Lean.Json.mkObj [($(quote ctorStr), Lean.toJson $(binders[0]!))])
            | _, false =>
                let xs ← binders.mapM fun b => `(Lean.toJson $b)
                `(Lean.Json.mkObj [($(quote ctorStr), Lean.Json.arr #[$xs,*])])
            | _, true =>
                let kvs ← (binders.zip userNames).mapM fun (b, u) =>
                  `(($(quote u.getString!), Lean.toJson $b))
                `(Lean.Json.mkObj [($(quote ctorStr), Lean.Json.mkObj [$kvs,*])])
          let toAlt ← `(Lean.Parser.Term.matchAltExpr| | @$ctorId:ident $binders* => $payload)
          -- decode
          let fromRhs : Term ←
            if binders.size == 0 then `(pure $ctorId)
            else do
              let namesOpt : Term ← if named then
                  let ns := userNames.map fun u => (quote u : Term)
                  `(some #[$ns,*])
                else `(none)
              let mut body : Term ← `(pure ($ctorId $binders*))
              for i in (List.range binders.size).reverse do
                let tyStx ← delabFull tys[i]!
                body ← `((Lean.fromJson? (jsons[$(quote i)]!) : Except String $tyStx) >>= fun $(binders[i]!) => $body)
              `((Lean.Json.parseCtorFields json $(quote ctorStr) $(quote binders.size) $namesOpt).bind
                  fun jsons => $body)
          let fromAlt ← `(Lean.Parser.Term.matchAltExpr| | $(quote ctorStr):str => $fromRhs)
          -- shape
          let shapePayload : Term ← match binders.size, named with
            | 0, _ => `(LeanDb.JsonShape.Payload.none)
            | _, true =>
                let kvs ← (tys.zip userNames).mapM fun (t, u) => do
                  `(($(quote u.getString!), $(← shapeTerm declName s!"constructor '{ctorName}'" t)))
                `(LeanDb.JsonShape.Payload.named [$kvs,*])
            | _, false =>
                let ts ← tys.mapM fun t => shapeTerm declName s!"constructor '{ctorName}'" t
                `(LeanDb.JsonShape.Payload.positional [$ts,*])
          let shapeCtor ← `(($(quote ctorStr), $shapePayload))
          pure (toAlt, fromAlt, shapeCtor)
        toAlts := toAlts.push toAlt
        fromAlts := fromAlts.push fromAlt
        shapeCtors := shapeCtors.push shapeCtor
      let toBody ← `(fun (x : $selfId) => match x with $toAlts:matchAlt*)
      let fromBody ← `(fun (json : Lean.Json) =>
        match Lean.Json.getTag? json with
        | some tag =>
            match tag with
            $fromAlts:matchAlt*
            | _ => Except.error "no inductive constructor matched"
        | none => Except.error "no inductive tag found")
      let shape ← `(LeanDb.JsonShape.inductive' $(quote (shapeName declName)) [$shapeCtors,*])
      pure (toBody, fromBody, shape)
    -- the aux functions: `partial` with local instances when recursive,
    -- exactly as Lean's own derive does
    let priv := isPrivateName declName
    let mkDef (id : Ident) (binder : TSyntax ``Lean.Parser.Term.bracketedBinder) (ty body : Term) :
        TermElabM (TSyntax `command) :=
      match priv, selfRef with
      | true, true => `(private partial def $id:ident $binder : $ty := $body)
      | true, false => `(private def $id:ident $binder : $ty := $body)
      | false, true => `(partial def $id:ident $binder : $ty := $body)
      | false, false => `(def $id:ident $binder : $ty := $body)
    let toBody' ← if selfRef then `(let _inst : Lean.ToJson $selfId := ⟨$toRef⟩; ($toBody) x)
      else `(($toBody) x)
    let fromBody' ← if selfRef then `(let _inst : Lean.FromJson $selfId := ⟨$fromRef⟩; ($fromBody) json)
      else `(($fromBody) json)
    let toDef ← mkDef toId (← `(Lean.Parser.Term.bracketedBinderF| (x : $selfId))) (← `(Lean.Json)) toBody'
    let fromDef ← mkDef fromId (← `(Lean.Parser.Term.bracketedBinderF| (json : Lean.Json)))
      (← `(Except String $selfId)) fromBody'
    let instCmds : Array (TSyntax `command) := #[
      ← `(instance : Lean.ToJson $selfId := ⟨$toId⟩),
      ← `(instance : Lean.FromJson $selfId := ⟨$fromId⟩),
      ← `(instance : LeanDb.JsonShape $selfId := ⟨$shape⟩),
      ← `(instance : LeanDb.DbJson $selfId := {})]
    pure (#[toDef, fromDef] ++ instCmds)
  for c in cmds do elabCommand c
  return true

def dbJsonHandler : DerivingHandler := fun declNames => do
  for declName in declNames do
    discard <| deriveDbJson declName
  return true

initialize registerDerivingHandler ``LeanDb.DbJson dbJsonHandler

end LeanDb.Derive
