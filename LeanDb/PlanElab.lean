import Lean
import LeanDb.Pred

/-! # `leandb_plan`: reifying the select predicate

`select`'s trailing argument `plan : PlanFor where' := by leandb_plan` makes
this tactic run at every call site with the *elaborated* predicate visible
in its goal type. It reifies what it recognizes into a `Pred ts` term over
the same table list that types the lambda — every column reference is a
`Pred.Col` built from a generated field symbol, so a plan over a column
that does not exist, a table not in the `select`, or a value of the wrong
type cannot be emitted at all:

- `row.val.field OP value` (both orders) via `==`/`!=`/`BEq` and
  `decide`-coerced `<`/`≤`/`>`/`≥`; captured variables and literals become
  the `v : τ` of `Pred.eq`/`Pred.ord`, bound as SQL parameters at run
  time. `ord` needs `SqlOrd τ` at the constructor, which is the gate that
  keeps nullable and closed-enum columns out of SQL ordering;
- the same through a validated newtype's projection — `row.val.field.rep`
  — as `Col.via c (·.rep) (fun _ => rfl)`: the proof elaborates exactly
  when `toCol a` and `toCol a.rep` are definitionally equal, which is what
  `ColCodec.via (·.rep) _` gives. The comparison then happens on the
  representation type, so ordering is pushed whenever *it* is `SqlOrd`;
- column-vs-column comparisons (`eq2`/`ord2`) — across tables these are
  join conditions (`t.val.ref == u.ref`, also through `some`, via
  `Col.via c some (fun _ => rfl)`), routed to the joined executor;
- `&&`, `||`, `!` (negation is exact — see `Pred.neg`), and
  `if c then t else e` on `Bool` as `(c ∧ t) ∨ (¬c ∧ e)`;
- `Option` tests (`== none`, `.isNone`, `.isSome`) as null-safe SQL;
- `EnumSet` membership (LEP-0003 A): `col.contains a` and `a ∈ col` with
  `a` a closed value (a literal or a captured parameter) as `Pred.bit`,
  a bit test `(col & ?) != 0`; negation flips it. With `a` a closed-enum
  *column* the case split below applies;
- bare `Bool` columns; `@[db]`-tagged defs unfolded;
- `row.val.ins.any (fun i => …)` / `.all` over a child-list field
  (LEP-0003 D) as LEP-0004's `Pred.exists`/`Pred.forall` over the generated
  child entity: the parent reference is the component's `Col.id`, the key
  the child's `parent` symbol, and the body is reified over `child :: ts`
  with `i` replaced by the record rebuilt from the child row's fields, so
  `i.rank ≥ n` is the child's `rank` column. A body the tactic cannot
  translate makes the whole quantifier one opaque leaf; `ins.length`,
  `ins.head?` and other non-quantifier reads of the list stay residual;
- `match` on a closed-enum column (directly or via an unfolded `@[db]`
  function like an SLA table) by *case-splitting on the closed world*:
  `⋁_c (col IS 'c' ∧ reify (conjunct[col := c]))` — total because the
  world is closed; branches that reduce to `false` drop out;
- the same split on a *captured parameter* of closed-enum type when the
  conjunct is stuck on it and no column is left to split (a `@[db]`
  function that matches on its parameter before its column argument, or
  a derived form like `!(d.forbids.contains k)`):
  `⋁_c (param IS 'c' ∧ reify (conjunct[param := c]))` — the guard is a
  value/value test (`Pred.vvEq`), which folds when the plan value is built;
- the same split on a captured parameter of type `Option α`, `α` a closed
  enum — the optional filter, `param.isNone || some col == param` or
  `match param with | none => true | some c => col == c` — over the world
  `none :: (ClosedEnum.all α).map some`: `(param IS NULL ∧ …) ∨ ⋁_c (param
  IS 'c' ∧ …)`, guarded by value/value tests again, so a `none` argument
  leaves `tt` for the conjunct and a `some c` argument the column test.

A top-level conjunct the tactic cannot translate becomes
`Pred.opaque (fun row => conjunct)` — the residual, as a leaf that still
carries its own meaning (`denote`), so `approx` drops it soundly and the
lambda decides it. The tactic never fails: on any surprise the whole
predicate becomes one opaque leaf (no narrowing, `residuals = 1`) —
correct, just unoptimized.

The same reflection is exposed as a term elaborator, `pred%`, for plans
written as data (`selectP`, quantifier bodies — LEP-0004).
-/

namespace LeanDb.PlanElab

open Lean Meta Elab Tactic

/-- Marks a definition as unfoldable during select-plan reification: a
    `@[db]` helper whose body is in the pushable fragment compiles to SQL
    at its call sites instead of going residual. -/
initialize dbAttr : TagAttribute ←
  registerTagAttribute `db
    "LeanDB: allow unfolding this def while reifying select plans"

register_option leandb.explain : Bool := {
  defValue := false
  descr := "log the reified Pred (pushed vs residual conjuncts) at each select call site"
}

/-! ## Footprints, recorded per declaration

Every plan the tactic reifies is walked for the columns it mentions —
`Pred.Col.here` carries the entity type and the field symbol, `Pred.Col.id`
the type — and whether an `opaque` leaf remains, and the result is stored
in an environment extension under the declaration being elaborated. That
is what `query%` reads to give a `QueryEntry` its footprint, statically,
with no plan re-executed. -/

structure PlanFootprint where
  decl : Name
  types : List String
  columns : List (String × String)
  residual : Bool
  deriving Inhabited

initialize planFootprintExt :
    SimplePersistentEnvExtension PlanFootprint (NameMap (List PlanFootprint)) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m e => m.insert e.decl (e :: (m.find? e.decl).getD [])
    addImportedFn := fun arrs => arrs.foldl (init := {}) fun m arr =>
      arr.foldl (init := m) fun m e => m.insert e.decl (e :: (m.find? e.decl).getD [])
  }

/-- The recorded footprints of a declaration (this file and imports). -/
def footprintsOf (env : Environment) (decl : Name) : List PlanFootprint :=
  ((planFootprintExt.getState env).find? decl).getD []

/-- Walk a reified plan for the columns it mentions. -/
partial def footprintOfPlan (plan : Expr) : Footprint := Id.run do
  let mut types : List String := []
  let mut cols : List (String × String) := []
  let mut residual := false
  let mut stack := [plan]
  let push := fun (xs : List String) (x : String) => if xs.contains x then xs else xs ++ [x]
  let pushC := fun (xs : List (String × String)) (x : String × String) => if xs.contains x then xs else xs ++ [x]
  while !stack.isEmpty do
    let e := stack.head!
    stack := stack.tail!
    let fn := e.getAppFn
    let args := e.getAppArgs
    match fn.constName? with
    | some ``Pred.Col.here =>
        -- #[F, α, ts, ent, fo, f]
        if let some ty := args[1]?.bind (·.constName?) then
          let tyS := toString ty
          types := push types tyS
          if let some sym := args[5]?.bind (·.constName?) then
            cols := pushC cols (tyS, sym.getString!)
    | some ``Pred.Col.id =>
        if let some ty := args[0]?.bind (·.constName?) then
          let tyS := toString ty
          types := push types tyS
          cols := pushC cols (tyS, "id")
    | some ``Pred.opaque => residual := true
    | _ => pure ()
    match e with
    | .app f a => stack := f :: a :: stack
    | .lam _ t b _ | .forallE _ t b _ => stack := t :: b :: stack
    | .letE _ t v b _ => stack := t :: v :: b :: stack
    | .mdata _ b | .proj _ _ b => stack := b :: stack
    | _ => pure ()
  return { tables := types, columns := cols, residual }

/-- Record a plan's footprint under the enclosing declaration, if any. -/
def recordFootprint (plan : Expr) : TermElabM Unit := do
  let some decl ← Term.getDeclName? | return
  let plan ← instantiateMVars plan
  let f := footprintOfPlan plan
  modifyEnv fun env => planFootprintExt.addEntry env
    { decl, types := f.tables, columns := f.columns, residual := f.residual }

/-- What the tactic knows about the `select` it is planning. -/
private structure Ctx where
  /-- The table list, as the goal states it. -/
  ts : Expr
  /-- `suffixes[k]` is `ts.drop k`, a sub-expression of `ts` itself — so
      the column terms built here are syntactically over the goal's own
      list and carry no metavariables. `suffixes.size = tys.size + 1`. -/
  suffixes : Array Expr
  /-- The entity types, in list order. -/
  tys : Array Expr
  /-- One local per table: the row components. -/
  comps : Array Expr

/-- Walk a `List Type` literal: its elements and its suffixes. -/
private partial def listSpine (ts : Expr) : MetaM (Array Expr × Array Expr) := do
  let mut tys := #[]
  let mut sufs := #[ts]
  let mut cur := ts
  repeat
    let w ← whnfR cur
    if w.isAppOfArity ``List.cons 3 then
      tys := tys.push (w.getArg! 1)
      cur := w.getArg! 2
      sufs := sufs.push cur
    else if w.isAppOfArity ``List.nil 1 then
      break
    else
      throwError "leandb_plan: the table list is not a literal: {ts}"
  return (tys, sufs)

/-- Walk a `Rows ts` product type, introducing one local per component, and
    hand the continuation the components plus the nested-pair value. -/
private partial def withComps (ρ : Expr) (k : Array Expr → Expr → MetaM α) : MetaM α := do
  let ρ ← whnfR ρ
  if ρ.isAppOfArity ``Prod 2 then
    withLocalDeclD `row (ρ.getArg! 0) fun a =>
      withComps (ρ.getArg! 1) fun comps rest => do
        k (#[a] ++ comps) (← mkAppM ``Prod.mk #[a, rest])
  else
    withLocalDeclD `row ρ fun a => k #[a] a

/-- The inverse of `withComps`: the projections of one `row : Rows ts`
    that stand for each component — `row` itself for one table; `row.1`,
    `row.2` for two; `row.1`, `row.2.1`, `row.2.2` for three; and so on. -/
private def rowProjs (row : Expr) (n : Nat) : Array Expr := Id.run do
  if n ≤ 1 then return #[row]
  let mut out := #[]
  let mut cur := row
  for i in [0:n] do
    if i + 1 == n then
      out := out.push cur
    else
      out := out.push (mkProj ``Prod 0 cur)
      cur := mkProj ``Prod 1 cur
  return out

/-- Does `e` mention any row component (i.e. is it *not* a closed value)? -/
private def usesComps (ctx : Ctx) (e : Expr) : Bool :=
  ctx.comps.any fun c => e.containsFVar c.fvarId!

private def isValue (ctx : Ctx) (e : Expr) : Bool :=
  !usesComps ctx e && !e.hasExprMVar

/-- Run a term builder; a failure to elaborate means "not translatable". -/
private def attempt (m : MetaM Expr) : MetaM (Option Expr) :=
  try some <$> m catch _ => pure none

/-! ## Term builders

The plan is a *term* — embedded values reference call-site variables.
`andS`/`orS`/`neg` are emitted as calls so tt/ff simplification happens
when the plan value is built. -/

private def ttE (ctx : Ctx) : Expr := mkApp (mkConst ``Pred.tt) ctx.ts
private def ffE (ctx : Ctx) : Expr := mkApp (mkConst ``Pred.ff) ctx.ts
private def mkAndS (ctx : Ctx) (a b : Expr) : Expr := mkApp3 (mkConst ``Pred.andS) ctx.ts a b
private def mkOrS (ctx : Ctx) (a b : Expr) : Expr := mkApp3 (mkConst ``Pred.orS) ctx.ts a b
private def mkNeg (ctx : Ctx) (a : Expr) : Expr := mkApp2 (mkConst ``Pred.neg) ctx.ts a

/-- The residual, as a leaf: `Pred.opaque (fun row => e)`, where each row
    component in `e` is replaced by its projection of `row`. -/
private def mkOpaque (ctx : Ctx) (e : Expr) : MetaM Expr := do
  let ρ := mkApp (mkConst ``LeanDb.Rows) ctx.ts
  withLocalDeclD `row ρ fun row => do
    let body := e.replaceFVars ctx.comps (rowProjs row ctx.comps.size)
    return mkApp2 (mkConst ``Pred.opaque) ctx.ts (← mkLambdaFVars #[row] body)

/-- The comparison operators the tactic recognizes; `eq`/`ne` become
    `EqOp`, the rest `OrdOp`. -/
private inductive CmpOp where
  | eq | ne | lt | le | gt | ge
  deriving BEq

private def CmpOp.isEq : CmpOp → Bool
  | .eq | .ne => true
  | _ => false

private def CmpOp.flip : CmpOp → CmpOp
  | .eq => .eq | .ne => .ne | .lt => .gt | .le => .ge | .gt => .lt | .ge => .le

private def CmpOp.expr : CmpOp → Expr
  | .eq => mkConst ``EqOp.eq | .ne => mkConst ``EqOp.ne
  | .lt => mkConst ``OrdOp.lt | .le => mkConst ``OrdOp.le
  | .gt => mkConst ``OrdOp.gt | .ge => mkConst ``OrdOp.ge

/-! ### Column terms -/

/-- `there^k c`: lift a column of table `k` to the whole list. -/
private def liftCol (ctx : Ctx) (k : Nat) (c : Expr) : MetaM Expr := do
  let mut c := c
  for j in (List.range k).reverse do
    c ← mkAppOptM ``Pred.Col.there #[ctx.tys[j]!, ctx.suffixes[j+1]!, none, none, c]
  return c

/-- `there^k (here α.Field.field)`: the declared field of table `k`, from
    its generated symbol. `none` when the entity has no such symbol. -/
private def fieldCol (ctx : Ctx) (k : Nat) (structName : Name) (field : String) :
    MetaM (Option (Expr × Nat)) := do
  let sym := (structName ++ `Field).str field
  unless (← getEnv).contains sym do return none
  (·.map (·, k)) <$> attempt do
    let here ← mkAppOptM ``Pred.Col.here
      #[none, ctx.tys[k]!, ctx.suffixes[k+1]!, none, none, mkConst sym]
    liftCol ctx k here

/-- `there^k Col.id`: the row identity of table `k`. -/
private def idCol (ctx : Ctx) (k : Nat) : MetaM (Option (Expr × Nat)) :=
  (·.map (·, k)) <$> attempt do
    liftCol ctx k (← mkAppOptM ``Pred.Col.id #[ctx.tys[k]!, ctx.suffixes[k+1]!, none])

/-- `Col.via c (fun a => f a) (fun a => rfl) : Col ts σ`. The proof is
    `Eq.refl (toCol a)`, checked by `mkAppOptM` against
    `∀ a, i.toCol a = j.toCol (f a)` — it elaborates exactly when the two
    encodings are definitionally equal, i.e. when `f` *is* the column's
    encoding (`ColCodec.via f _`) or `some` over it. `j` is the codec of
    `σ`, synthesized here: it is an implicit of the constructor, and
    unification alone cannot recover it from the proof. -/
private def viaCol (ctx : Ctx) (c : Expr) (σ : Expr) (f : Expr → Expr) : MetaM Expr := do
  let cTy ← instantiateMVars (← inferType c)
  unless cTy.isAppOfArity ``Pred.Col 3 do throwError "leandb_plan: not a column reference"
  let τ := cTy.getArg! 1
  let i := cTy.getArg! 2
  let j ← synthInstance (mkApp (mkConst ``LeanDb.ColCodec) σ)
  let (fE, hE) ← withLocalDeclD `a τ fun a => do
    let fE ← mkLambdaFVars #[a] (f a)
    let lhs := mkApp3 (mkConst ``LeanDb.ColCodec.toCol) τ i a
    let hE ← mkLambdaFVars #[a] (mkApp2 (mkConst ``Eq.refl [.one]) (mkConst ``LeanDb.Col) lhs)
    pure (fE, hE)
  mkAppOptM ``Pred.Col.via #[ctx.ts, τ, σ, i, j, c, fE, hE]

/-- If `e` is a column access on one of the row components, return its
    `Pred.Col` term and the component index. Recognizes `Stored.val c
    |>.field` (as projection-fn application or `Expr.proj`),
    `Stored.id`/`.ref`, and a projection *through* a column whose codec is
    that very projection — `col.field` on a validated newtype (see
    `throughCodec?`). `fuel` bounds how many such projections are
    unwrapped. -/
private partial def colOf? (ctx : Ctx) (e : Expr) (fuel : Nat := 8) :
    MetaM (Option (Expr × Nat)) := do
  let e ← whnfR e
  match e with
  | .proj s i x =>
      if s == ``Stored && i == 0 then
        let some k ← compIdx? x | return none
        return ← idCol ctx k
      if let some k ← storedValComp? x then
        let some info := getStructureInfo? (← getEnv) s | return none
        let some fname := info.fieldNames[i]? | return none
        return ← fieldCol ctx k s fname.toString
      if let some info := getStructureInfo? (← getEnv) s then
        if let some fname := info.fieldNames[i]? then
          if let some r ← inlineCol? x fname.toString then return some r
      throughCodec? x e fun a => .proj s i a
  | _ =>
      let .const declName _ := e.getAppFn | return none
      if (declName == ``Stored.id || declName == ``Stored.ref) && e.getAppNumArgs == 2 then
        let some k ← compIdx? (e.getArg! 1) | return none
        return ← idCol ctx k
      let some _ := (← getEnv).getProjectionFnInfo? declName | return none
      let args := e.getAppArgs
      let some x := args.back? | return none
      if let some k ← storedValComp? x then
        return ← fieldCol ctx k declName.getPrefix declName.getString!
      if let some r ← inlineCol? x declName.getString! then return some r
      throughCodec? x e fun a => mkAppN e.getAppFn (args.set! (args.size - 1) a)
where
  compIdx? (x : Expr) : MetaM (Option Nat) := do
    let x ← whnfR x
    return ctx.comps.findIdx? (· == x)
  storedValComp? (x : Expr) : MetaM (Option Nat) := do
    let x ← whnfR x
    if x.isAppOfArity ``Stored.val 2 then return ← compIdx? (x.getArg! 1)
    match x with
    | .proj s 1 c => if s == ``Stored then compIdx? c else return none
    | _ => return none
  /-- `x` as a structure projection `f y`, in either spelling:
      (structure, field name, `y`). -/
  projOf? (x : Expr) : MetaM (Option (Name × String × Expr)) := do
    let x ← whnfR x
    match x with
    | .proj s i y =>
        let some info := getStructureInfo? (← getEnv) s | return none
        let some fname := info.fieldNames[i]? | return none
        return some (s, fname.toString, y)
    | _ =>
        let .const declName _ := x.getAppFn | return none
        let some _ := (← getEnv).getProjectionFnInfo? declName | return none
        let some y := x.getAppArgs.back? | return none
        return some (declName.getPrefix, declName.getString!, y)
  /-- The projection of an inline field (LEP-0003 C): `whole` is `g x`
      and `x` is itself `f y` with `y` a `Stored.val` component and `f` a
      field of its entity whose type has an `Inline` instance. The entity
      flattened that field into one column per sub-field, each with its
      own symbol, so `g` of it is the declared column `f_g` of the same
      table — `Col.here Entity.Field.f_g`, nothing composed. A `via`
      newtype among the sub-fields unwraps on top of this, through
      `throughCodec?`, exactly as for a plain column. -/
  inlineCol? (x : Expr) (g : String) : MetaM (Option (Expr × Nat)) := do
    let some (s, f, y) ← projOf? x | return none
    let some k ← storedValComp? y | return none
    let τ ← instantiateMVars (← inferType x)
    let isInline ← try
        pure (← synthInstance? (mkApp (mkConst ``LeanDb.Inline) τ)).isSome
      catch _ => pure false
    unless isInline do return none
    fieldCol ctx k s s!"{f}_{g}"
  /-- `whole` is `f x` for a projection `f : α → β`, and `x` resolves to a
      column of type `α`. Push through `f` exactly when `f` *is* that
      column's encoding: `Col.via c f (fun a => rfl)` elaborates iff
      `toCol a` is definitionally `toCol (f a)`. `ColCodec.via enc dec` is
      reducible and sets `toCol a := toCol (enc a)`, so this holds
      precisely for a newtype stored through this projection — and then
      the column's bytes already *are* the encoding of `f a`, so SQLite
      compares exactly what the Lean predicate compares. The column name
      and table index stay those of the underlying field: this unwraps,
      it does not rename. Anything else (a codec that mixes two fields,
      an unrelated projection) fails the proof and stays residual. -/
  throughCodec? (x whole : Expr) (rebuild : Expr → Expr) :
      MetaM (Option (Expr × Nat)) := do
    if fuel == 0 then return none
    let some (c, k) ← colOf? ctx x (fuel - 1) | return none
    let σ ← inferType whole
    (·.map (·, k)) <$> attempt (viaCol ctx c σ rebuild)

/-! ### Comparisons -/

private def mkCmp (c : Expr) (op : CmpOp) (v : Expr) : MetaM Expr := do
  let v ← instantiateMVars v
  if op.isEq then mkAppM ``Pred.eq #[c, op.expr, v]
  else mkAppM ``Pred.ord #[c, op.expr, v]

private def mkCmp2 (a : Expr) (op : CmpOp) (b : Expr) : MetaM Expr :=
  if op.isEq then mkAppM ``Pred.eq2 #[a, op.expr, b]
  else mkAppM ``Pred.ord2 #[a, op.expr, b]

/-- Value against value, folded when the plan value is built. -/
private def mkVV (ctx : Ctx) (a : Expr) (op : CmpOp) (b : Expr) : MetaM Expr := do
  let a ← instantiateMVars a
  let b ← instantiateMVars b
  if op.isEq then mkAppOptM ``Pred.vvEq #[ctx.ts, none, none, a, op.expr, b]
  else mkAppOptM ``Pred.vvOrd #[ctx.ts, none, none, none, a, op.expr, b]

/-- Reify one comparison. `none` = not translatable. SQL ordering is only
    sound when the encoding preserves Lean's order: `Pred.ord`/`ord2`/
    `vvOrd` demand `SqlOrd τ`, so a nullable or closed-enum column (whose
    `none`/constructor order does not match SQLite NULL/TEXT ordering)
    fails to build and falls through. -/
private partial def cmpStrict (ctx : Ctx) (op : CmpOp) (a b : Expr) : MetaM (Option Expr) := do
  -- `some a OP some b` is `a OP b`, and `some _ OP none` is decided: the
  -- shapes a substituted optional filter leaves (`some col == some c`),
  -- where the column sits under the `some`
  if op.isEq then
    let aW ← whnfR a
    let bW ← whnfR b
    let aSome := aW.isAppOfArity ``Option.some 2
    let bSome := bW.isAppOfArity ``Option.some 2
    if aSome && bSome then
      return ← cmpStrict ctx op (aW.getArg! 1) (bW.getArg! 1)
    if (aSome && bW.isAppOfArity ``Option.none 1) || (bSome && aW.isAppOfArity ``Option.none 1) then
      return some (if op == .eq then ffE ctx else ttE ctx)
  let ca? ← colOf? ctx a
  let cb? ← colOf? ctx b
  match ca?, cb? with
  | some (ca, _), some (cb, _) => attempt (mkCmp2 ca op cb)
  | some (ca, _), none => oneSided ca op b
  | none, some (cb, _) => oneSided cb op.flip a
  | none, none =>
      -- neither side is a column: pushable as a value/value test when both
      -- are closed (a case split leaves `constant OP captured-param`)
      if isValue ctx a && isValue ctx b then attempt (mkVV ctx a op b)
      else return none
where
  /-- col OP other: `other` is a value, or (for eq/ne) `some <col>`. -/
  oneSided (c : Expr) (op : CmpOp) (other : Expr) : MetaM (Option Expr) := do
    let otherW ← whnfR other
    if otherW.isAppOfArity ``Option.some 2 && op.isEq then
      if let some (c2, _) ← colOf? ctx (otherW.getArg! 1) then
        let α := otherW.getArg! 0
        return ← attempt do
          let lifted ← viaCol ctx c2 (← inferType otherW) fun a =>
            mkApp2 (mkConst ``Option.some [.zero]) α a
          mkCmp2 c op lifted
    if isValue ctx other then
      return ← attempt (mkCmp c op other)   -- fails when the value's type is not the column's
    return none

/-- Reify a whole Bool expression, or `none`. Exact — safe under `or` and
    `not`. `fuel` bounds closed-world case-splitting depth. -/
private partial def strict (ctx : Ctx) (fuel : Nat) (e : Expr) :
    MetaM (Option Expr) := do
  let e ← whnfCore e
  -- a conjunct that doesn't touch the row at all: try to evaluate it (a
  -- case-split branch may be a closed constant); when captured parameters
  -- keep it undecided, fall through — the comparison dispatch below can
  -- still push it as a value/value test
  if !usesComps ctx e then
    let v ← withDefault (whnf e)
    if v.isConstOf ``Bool.true then return some (ttE ctx)
    if v.isConstOf ``Bool.false then return some (ffE ctx)
  if e.isAppOfArity ``Bool.and 2 then
    let some a ← strict ctx fuel (e.getArg! 0) | return none
    let some b ← strict ctx fuel (e.getArg! 1) | return none
    return some (mkAndS ctx a b)
  if e.isAppOfArity ``Bool.or 2 then
    let some a ← strict ctx fuel (e.getArg! 0) | return none
    let some b ← strict ctx fuel (e.getArg! 1) | return none
    return some (mkOrS ctx a b)
  if e.isAppOfArity ``Bool.not 1 then
    let some a ← strict ctx fuel (e.getArg! 0) | return none
    return some (mkNeg ctx a)
  -- `if c then t else e` on `Bool` is `(c ∧ t) ∨ (¬c ∧ e)`; the negation is
  -- exact for the same reason `!` is. `ite` carries a `Prop` condition
  -- with its `Decidable` instance, which is exactly a `decide`; `cond`
  -- carries a `Bool` directly.
  if e.isAppOfArity ``ite 5 then
    let c := mkApp2 (mkConst ``Decidable.decide) (e.getArg! 1) (e.getArg! 2)
    if let some r ← ifThenElse fuel c (e.getArg! 3) (e.getArg! 4) then return some r
    return none
  if e.isAppOfArity ``cond 4 then
    if let some r ← ifThenElse fuel (e.getArg! 1) (e.getArg! 2) (e.getArg! 3) then return some r
    return none
  if e.isAppOfArity ``bne 4 then
    if let some p ← cmpStrict ctx .ne (e.getArg! 2) (e.getArg! 3) then return some p
    return ← caseSplit fuel e
  if e.isAppOfArity ``BEq.beq 4 then
    if let some p ← cmpStrict ctx .eq (e.getArg! 2) (e.getArg! 3) then return some p
    return ← caseSplit fuel e
  if e.isAppOfArity ``decide 2 then
    let p ← whnfCore (e.getArg! 0)
    -- `a ∈ s` on an `EnumSet`: its `Membership` instance unfolds (at
    -- instances transparency) to `s.contains a = true`
    if p.isAppOfArity ``Membership.mem 5 then
      let q ← withReducibleAndInstances (whnf p)
      if q.isAppOfArity ``Eq 3 && (q.getArg! 1).isAppOfArity ``EnumSet.contains 4
          && (q.getArg! 2).isConstOf ``Bool.true then
        return ← strict ctx fuel (q.getArg! 1)
    if p.isAppOfArity ``LT.lt 4 then return ← try2 fuel e .lt (p.getArg! 2) (p.getArg! 3)
    if p.isAppOfArity ``LE.le 4 then return ← try2 fuel e .le (p.getArg! 2) (p.getArg! 3)
    if p.isAppOfArity ``GT.gt 4 then return ← try2 fuel e .gt (p.getArg! 2) (p.getArg! 3)
    if p.isAppOfArity ``GE.ge 4 then return ← try2 fuel e .ge (p.getArg! 2) (p.getArg! 3)
    if p.isAppOfArity ``Eq 3 then return ← try2 fuel e .eq (p.getArg! 1) (p.getArg! 2)
    if p.isAppOfArity ``Ne 3 then return ← try2 fuel e .ne (p.getArg! 1) (p.getArg! 2)
    return ← caseSplit fuel e
  if e.isAppOfArity ``Option.isNone 2 || e.isAppOfArity ``Option.isSome 2 then
    if let some (c, _) ← colOf? ctx (e.getArg! 1) then
      let ctor := if e.isAppOfArity ``Option.isNone 2 then ``Pred.isNull else ``Pred.isNotNull
      return ← attempt (mkAppM ctor #[c])
    -- not a column: an optional filter's `param.isNone`, decided by the
    -- case split on the parameter's world
    return ← caseSplit fuel e
  -- `EnumSet.contains col a`: a bit test when `a` is a closed value; when
  -- `a` is itself a closed-enum column, the case split below substitutes
  -- each constructor and lands here again
  if e.isAppOfArity ``EnumSet.contains 4 then
    if let some (c, _) ← colOf? ctx (e.getArg! 2) then
      if isValue ctx (e.getArg! 3) then
        if let some p ← attempt (mkAppM ``Pred.bit #[c, ← instantiateMVars (e.getArg! 3), mkConst ``Bool.true]) then
          return some p
    return ← caseSplit fuel e
  -- `List.any`/`List.all` over a child-list field (LEP-0003 D): a
  -- quantifier over the generated child table
  if e.isAppOfArity ``List.any 3 || e.isAppOfArity ``List.all 3 then
    if let some q ← childQuantifier fuel (e.isAppOfArity ``List.any 3) (e.getArg! 1) (e.getArg! 2) then
      return some q
    return none
  -- String prefix / substring (LDB-14). `s.startsWith p` and `s.contains p`
  -- are generic over the pattern; the last argument is the instance, so the
  -- column is `args[size-3]` and the pattern `args[size-2]`. A `Char`
  -- pattern (or any non-`String` one) fails `mkAppM` and falls through to
  -- the residual. `(s.toLower).contains (p.toLower)` is `icontains` — the
  -- ASCII folding the tactic can vouch for, since both sides lower. There
  -- is no case-insensitive prefix leaf: a lowered `startsWith` finds no
  -- column under `toLower` and stays residual, never a `prefix` of the
  -- unlowered column.
  if (e.getAppFn.isConstOf ``String.startsWith || e.getAppFn.isConstOf ``String.contains)
      && e.getAppNumArgs ≥ 3 then
    let isPrefix := e.getAppFn.isConstOf ``String.startsWith
    let s := e.getArg! (e.getAppNumArgs - 3)
    let pat := e.getArg! (e.getAppNumArgs - 2)
    let sL ← whnfR s
    let patL ← whnfR pat
    let icontains := !isPrefix &&
      sL.isAppOfArity ``String.toLower 1 && patL.isAppOfArity ``String.toLower 1
    if let some (c, _) ← colOf? ctx (if icontains then sL.getArg! 0 else s) then
      if isValue ctx (if icontains then patL.getArg! 0 else pat) then
        let v ← instantiateMVars (if icontains then patL.getArg! 0 else pat)
        let ctor := if isPrefix then ``Pred.prefix
          else if icontains then ``Pred.icontains else ``Pred.contains
        if let some p ← attempt (mkAppM ctor #[c, v]) then return some p
    return none
  -- bare Bool column
  if let some (c, _) ← colOf? ctx e then
    return ← attempt (mkCmp c .eq (mkConst ``Bool.true))
  -- @[db]-tagged helper: unfold and keep going
  if let .const n _ := e.getAppFn then
    if dbAttr.hasTag (← getEnv) n then
      if let some e' ← unfoldDefinition? e then
        return ← strict ctx fuel e'
  caseSplit fuel e
where
  ifThenElse (fuel : Nat) (c t e : Expr) : MetaM (Option Expr) := do
    let some c' ← strict ctx fuel c | return none
    let some t' ← strict ctx fuel t | return none
    let some e' ← strict ctx fuel e | return none
    return some (mkOrS ctx (mkAndS ctx c' t') (mkAndS ctx (mkNeg ctx c') e'))
  try2 (fuel : Nat) (whole : Expr) (op : CmpOp) (a b : Expr) : MetaM (Option Expr) := do
    if let some r ← cmpStrict ctx op a b then return some r
    caseSplit fuel whole
  /-- Case-split on a closed world. A closed-enum column mentioned in `e`
      first: `⋁_c (col IS 'c' ∧ strict (e[col := c]))`. When none is
      left, a captured parameter of closed-enum type (a free variable
      that is not a row component): `⋁_c (param IS 'c' ∧ strict (e[param := c]))`,
      the guard a value/value test; then a captured `Option α` parameter
      for closed `α`, over `none :: (ClosedEnum.all α).map some`, guarded
      the same way. All are exhaustive because the world is closed, and
      each branch is guarded by the equality that justifies its
      substitution. -/
  caseSplit (fuel : Nat) (e : Expr) : MetaM (Option Expr) := do
    if fuel == 0 then return none
    if let some (colExpr, c, enumName) ← findEnumCol e then
      return ← splitWorld fuel e colExpr (← enumWorld enumName) fun ctor => attempt (mkCmp c .eq ctor)
    if let some (param, enumName) ← findEnumParam e then
      return ← splitWorld fuel e param (← enumWorld enumName) fun ctor => attempt (mkVV ctx param .eq ctor)
    let some (param, world) ← findOptEnumParam e | return none
    splitWorld fuel e param world fun ctor => attempt (mkVV ctx param .eq ctor)
  /-- `⋁_c (tag c ∧ strict (e[x := c]))` over the values `world` of a closed type. -/
  splitWorld (fuel : Nat) (e x : Expr) (world : Array Expr) (tag : Expr → MetaM (Option Expr)) :
      MetaM (Option Expr) := do
    let mut acc := ffE ctx
    for ctor in world do
      let e' := e.replace fun y => if y == x then some ctor else none
      let some branch ← strict ctx (fuel - 1) e' | return none
      let some guard ← tag ctor | return none
      acc := mkOrS ctx acc (mkAndS ctx guard branch)
    return some acc
  /-- First subterm that is a closed-enum column access. -/
  findEnumCol (e : Expr) : MetaM (Option (Expr × Expr × Name)) := do
    let cands := (collectApps e #[]).filter fun x => usesComps ctx x
    for x in cands do
      if let some (c, _) ← colOf? ctx x then
        let ty ← whnfR (← inferType x)
        if let .const tyName _ := ty then
          if (← synthInstance? (← mkAppM ``LeanDb.ClosedEnum #[ty])).isSome then
            return some (x, c, tyName)
    return none
  /-- First free variable of closed-enum type in `e` that is not a row
      component: a captured parameter of the query. Restricted to fvars
      (not arbitrary closed subterms) so the split stays predictable. -/
  findEnumParam (e : Expr) : MetaM (Option (Expr × Name)) := do
    let st := collectFVars {} e
    for fv in st.fvarIds do
      let x := mkFVar fv
      if ctx.comps.contains x then continue
      let ty ← whnfR (← inferType x)
      if let .const tyName _ := ty then
        if (← synthInstance? (← mkAppM ``LeanDb.ClosedEnum #[ty])).isSome then
          return some (x, tyName)
    return none
  /-- First free variable of type `Option α`, `α` a closed enum, that is
      not a row component — an optional filter — with its world,
      `none :: (ClosedEnum.all α).map some`. Runs after `findEnumParam`,
      so plain closed-enum parameters split first. -/
  findOptEnumParam (e : Expr) : MetaM (Option (Expr × Array Expr)) := do
    let st := collectFVars {} e
    for fv in st.fvarIds do
      let x := mkFVar fv
      if ctx.comps.contains x then continue
      let ty ← whnfR (← instantiateMVars (← inferType x))
      unless ty.isAppOfArity ``Option 1 do continue
      let .const _ us := ty.getAppFn | continue
      let α ← whnfR (ty.getArg! 0)
      let .const αName _ := α | continue
      unless (← synthInstance? (← mkAppM ``LeanDb.ClosedEnum #[α])).isSome do continue
      let noneE := mkApp (mkConst ``Option.none us) α
      let somes := (← enumWorld αName).map fun c => mkApp2 (mkConst ``Option.some us) α c
      return some (x, #[noneE] ++ somes)
    return none
  /-- `xs.any f` / `xs.all f` with `xs` the child-list field `f` of a
      `Stored.val` component (table `k`) whose entity generated the child
      `Parent.F` (`childTypeName`): `Pred.exists`/`Pred.forall` with
      `parent := Col.id` of table `k`, `fk := Col.here Parent.F.Field.parent`
      and the body reified over `Parent.F :: ts` — a fresh component
      `c : Stored Parent.F` at position 0, the lambda's binder replaced by
      the record rebuilt from `c.val`'s fields (a projection of a
      constructor reduces by `whnfR`, so `colOf?` needs nothing new).
      `none` — the whole conjunct goes opaque — when the list is not a
      child-list field or the body does not translate entirely. -/
  childQuantifier (fuel : Nat) (isAny : Bool) (xs f : Expr) : MetaM (Option Expr) := do
    let xs ← whnfR xs
    let some (parentName, field, y) ← projOf? xs | return none
    let some k ← storedValComp? y | return none
    let env ← getEnv
    let childName := childTypeName parentName (Name.mkSimple field)
    let fkSym := (childName ++ `Field).str "parent"
    unless env.contains childName && env.contains fkSym do return none
    let some childInfo := getStructureInfo? env childName | return none
    let some recordInfo := getStructureInfo? env (← recordTypeName xs) | return none
    let childTy := mkConst childName
    let storedChild := mkApp (mkConst ``Stored) childTy
    withLocalDeclD `child storedChild fun c => do
      -- the record, rebuilt from the child row: `R.mk c.val.f₁ … c.val.fₙ`
      let cVal := mkApp2 (mkConst ``Stored.val) childTy c
      let recordCtor := mkConst (recordInfo.structName ++ `mk)
      let fieldsOfChild ← recordInfo.fieldNames.mapM fun fname => do
        unless childInfo.fieldNames.contains fname do throwError "child field mismatch"
        mkProjection cVal fname
      let some record ← attempt (mkAppM' recordCtor fieldsOfChild) | return none
      let body := (mkApp f record).headBeta
      -- the body's context: the child at position 0, everything else shifted
      let ts' := mkApp3 (mkConst ``List.cons [.succ .zero]) (mkSort (.succ .zero)) childTy ctx.ts
      let ctx' : Ctx := { ts := ts', suffixes := #[ts'] ++ ctx.suffixes
                          tys := #[childTy] ++ ctx.tys, comps := #[c] ++ ctx.comps }
      let some bodyP ← strict ctx' fuel body | return none
      let bodyP ← instantiateMVars bodyP
      if bodyP.containsFVar c.fvarId! then return none
      let some (parentCol, _) ← idCol ctx k | return none
      let nil := mkApp (mkConst ``List.nil [.succ .zero]) (mkSort (.succ .zero))
      attempt do
        let fk ← mkAppOptM ``Pred.Col.here #[none, childTy, nil, none, none, mkConst fkSym]
        let ctor := if isAny then ``Pred.«exists» else ``Pred.«forall»
        mkAppOptM ctor #[ctx.ts, none, none, none, none, none, parentCol, fk, bodyP]
  /-- The element type of a `List` expression, as a structure name. -/
  recordTypeName (xs : Expr) : MetaM Name := do
    let ty ← whnfR (← inferType xs)
    unless ty.isAppOfArity ``List 1 do throwError "not a list"
    let .const n _ := (← whnfR (ty.getArg! 0)).getAppFn | throwError "not a structure"
    return n
  /-- `x` as a structure projection `f y`, in either spelling. -/
  projOf? (x : Expr) : MetaM (Option (Name × String × Expr)) := do
    let x ← whnfR x
    match x with
    | .proj s i y =>
        let some info := getStructureInfo? (← getEnv) s | return none
        let some fname := info.fieldNames[i]? | return none
        return some (s, fname.toString, y)
    | _ =>
        let .const declName _ := x.getAppFn | return none
        let some _ := (← getEnv).getProjectionFnInfo? declName | return none
        let some y := x.getAppArgs.back? | return none
        return some (declName.getPrefix, declName.getString!, y)
  storedValComp? (x : Expr) : MetaM (Option Nat) := do
    let x ← whnfR x
    if x.isAppOfArity ``Stored.val 2 then return ← compIdx? (x.getArg! 1)
    match x with
    | .proj s 1 c => if s == ``Stored then compIdx? c else return none
    | _ => return none
  compIdx? (x : Expr) : MetaM (Option Nat) := do
    let x ← whnfR x
    return ctx.comps.findIdx? (· == x)
  /-- The constructors of a closed enum, as terms. -/
  enumWorld (enumName : Name) : MetaM (Array Expr) :=
    return (← getConstInfoInduct enumName).ctors.toArray.map mkConst
  collectApps (e : Expr) (acc : Array Expr) : Array Expr :=
    match e with
    | .app f a => collectApps f (collectApps a (acc.push e))
    | .proj _ _ x => collectApps x (acc.push e)
    | .mdata _ x => collectApps x acc
    | _ => acc

/-- Top level: conjuncts may individually fail — each becomes an opaque
    leaf over its own conjunct, which `approx` drops (omission only widens
    the fetch) and `denote` still means. -/
private partial def lenient (ctx : Ctx) (e : Expr) : MetaM Expr := do
  let e' ← whnfCore e
  if e'.isAppOfArity ``Bool.and 2 then
    let a ← lenient ctx (e'.getArg! 0)
    let b ← lenient ctx (e'.getArg! 1)
    return mkAndS ctx a b
  match ← (try strict ctx 2 e' catch _ => pure none) with
  | some p => return p
  | none => mkOpaque ctx e

/-- Reflect the predicate in a `PlanFor pred` goal into a `Pred ts` term. -/
def reflectPlan (goalTy : Expr) : MetaM Expr := do
  let goalTy ← instantiateMVars goalTy
  unless goalTy.isAppOfArity ``LeanDb.PlanFor 2 do
    throwError "leandb_plan: goal is not PlanFor"
  let ts := goalTy.getArg! 0
  let pred := goalTy.getArg! 1
  let (tys, suffixes) ← listSpine ts
  withComps (mkApp (mkConst ``LeanDb.Rows) ts) fun comps pair => do
    unless comps.size == tys.size do
      throwError "leandb_plan: {comps.size} row components for {tys.size} tables"
    let ctx : Ctx := { ts, suffixes, tys, comps }
    let body ← whnfCore (mkApp pred pair)
    lenient ctx body

/-- The plan that pushes nothing and says so: one opaque leaf carrying the
    whole predicate. -/
private def fallbackPlan (goalTy : Expr) : MetaM Expr := do
  let goalTy ← instantiateMVars goalTy
  unless goalTy.isAppOfArity ``LeanDb.PlanFor 2 do
    throwError "leandb_plan: goal is not PlanFor"
  return mkApp2 (mkConst ``Pred.opaque) (goalTy.getArg! 0) (goalTy.getArg! 1)

/-- Reflect, or fall back; log when `leandb.explain` is set. -/
private def planFor (goalTy : Expr) : MetaM Expr := do
  let plan ← try reflectPlan goalTy catch _ => fallbackPlan goalTy
  if leandb.explain.get (← getOptions) then
    logInfo m!"leandb plan: {← instantiateMVars plan}"
  return plan

elab "leandb_plan" : tactic => do
  let g ← getMainGoal
  let ty ← g.getType
  let plan ← planFor ty
  recordFootprint plan
  g.assign (← mkExpectedTypeHint plan ty)

/-- `pred% [T1, T2] fun (a, b) => … : Pred [T1, T2]` — the plan
    `leandb_plan` would reify for that lambda, as a term. This is how a
    plan is written as data: for `selectP`, and for the bodies of
    `Pred.exists`/`Pred.forall` (LEP-0004), which quantify over rows no
    lambda over the outer tables could mention. Same recognizer, same
    fallback — a conjunct the tactic cannot translate becomes an opaque
    leaf, and the whole predicate one on any surprise. -/
elab "pred% " ts:term:max f:term:max : term => do
  let listType := mkApp (mkConst ``List [.succ .zero]) (mkSort (.succ .zero))
  let tsE ← Term.elabTermEnsuringType ts (some listType)
  Term.synthesizeSyntheticMVarsNoPostponing
  let tsE ← instantiateMVars tsE
  let fTy := mkForall `r .default (mkApp (mkConst ``LeanDb.Rows) tsE) (mkConst ``Bool)
  let fE ← Term.elabTermEnsuringType f (some fTy)
  Term.synthesizeSyntheticMVarsNoPostponing
  let fE ← instantiateMVars fE
  let goalTy := mkApp2 (mkConst ``LeanDb.PlanFor) tsE fE
  let plan ← planFor goalTy
  recordFootprint plan
  mkExpectedTypeHint plan (mkApp (mkConst ``LeanDb.Pred) tsE)

end LeanDb.PlanElab
