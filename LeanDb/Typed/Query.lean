import LeanDb.Typed.State
import LeanDb.PlanElab

namespace LeanDb

/-! # Typed queries (M14)

A `Query s ts ρ` is a `Pred` over tables `ts` producing row type `ρ`,
typed order keys that always end with the id, and a `Window`. Its meaning
extends `selectSpec`. SQL pushes LIMIT/OFFSET only when the plan is exact
(`!pred.hasOpaque`).
-/

/-- A typed order key over an entity's columns. `.desc .email` is
    `OrderKey.desc Entity.Field.email`. -/
inductive OrderKey (α : Type) [Entity α] where
  | asc (f : Entity.Field α)
  | desc (f : Entity.Field α)

def OrderKey.dir [Entity α] : OrderKey α → Dir
  | .asc _ => .asc
  | .desc _ => .desc

def OrderKey.field [Entity α] : OrderKey α → Entity.Field α
  | .asc f | .desc f => f

/-- A query over schema `s` answering rows of type `ρ` from tables `ts`.
    Single-table queries have `ts = [α]` and `ρ = Stored α`; a `join`
    answers a pair. Indexed by `ts` so `where'`/`orderBy` see a `Pred` of
    the right table list. -/
structure Query (s : Type) (ts : List Type) (ρ : Type) : Type 1 where
  rowsOf : RowsOf ts
  pred : Pred ts
  sortBy : SortBy (Rows ts)
  order : Array (Order ts)
  window : Window := {}
  toRow : Rows ts → ρ

namespace Query

/-- Exactness: no opaque leaf, so a pushed window/count/exists is sound. -/
def exact {s ts ρ} (q : Query s ts ρ) : Bool := !q.pred.hasOpaque

/-- The base query: every row of `α`, id order. -/
def «from» (α : Type) [Entity α] {s : Type} [IsSchema s] [IsSchema.Has s α] :
    Query s [α] (Stored α) where
  rowsOf := inferInstance
  pred := .tt
  sortBy := .preserve
  order := #[]
  window := {}
  toRow := id

/-- Filter. `where'` is the existing name: `where` is a Lean keyword.
    The predicate is over `Stored α`, like `select`. `leandb_plan` reifies
    it; a conjunct it cannot translate becomes an opaque leaf, and
    windows/counts then run in Lean. -/
def where' {s α} [Entity α] (q : Query s [α] (Stored α)) (p : Stored α → Bool)
    (plan : PlanFor (ts := [α]) p := by leandb_plan) : Query s [α] (Stored α) :=
  { q with pred := Pred.andS q.pred plan }

/-- Filter a joined query. -/
def where2 {s α β} [Entity α] [Entity β]
    (q : Query s [α, β] (Stored α × Stored β)) (p : Stored α × Stored β → Bool)
    (plan : PlanFor (ts := [α, β]) p := by leandb_plan) :
    Query s [α, β] (Stored α × Stored β) :=
  { q with pred := Pred.andS q.pred plan }

def keySort [Entity α] (k : OrderKey α) [o : Ord (Entity.fieldTy k.field)] :
    SortBy (Stored α) :=
  match k, o with
  | .asc f, o => .key (ord := o) (fun r => Entity.get f r.val)
  | .desc f, o => .desc (.key (ord := o) (fun r => Entity.get f r.val))

def andSort (a b : SortBy ρ) : SortBy ρ :=
  match a with
  | .preserve => b
  | _ => .andThen a b

/-- One typed order key, composed after any already set. The id tiebreak
    is added by `finishRows` / SQL `, id ASC`. The field must have `Ord`. -/
def orderBy {s α} [Entity α] (q : Query s [α] (Stored α)) (k : OrderKey α)
    [Ord (Entity.fieldTy k.field)] : Query s [α] (Stored α) :=
  { q with
    sortBy := andSort q.sortBy (keySort k)
    order := q.order.push { column := Entity.fieldName k.field, dir := k.dir } }

def withWindow {s ts ρ} (q : Query s ts ρ) (w : Window) : Query s ts ρ :=
  { q with window := w }

/-- Extend a single-table column reference to a two-table plan. -/
def Col.extend {α β : Type} {τ : Type} {i : ColCodec τ} :
    Pred.Col [α] τ i → Pred.Col [α, β] τ i
  | .here (ent := e) (fo := fo) f => .here (ent := e) (fo := fo) f
  | .id (ent := e) => .id (ent := e)
  | .via c f h => .via (Col.extend c) f h
  | .there c => (Pred.Col.nil_elim c).elim

/-- Extend a single-table plan with a second table (the join target). -/
def Pred.extend {α β : Type} : Pred [α] → Pred [α, β]
  | .tt => .tt
  | .ff => .ff
  | .eq c op v => .eq (Col.extend c) op v
  | .ord (so := so) c op v => .ord (so := so) (Col.extend c) op v
  | .eq2 a op b => .eq2 (Col.extend a) op (Col.extend b)
  | .ord2 (so := so) a op b => .ord2 (so := so) (Col.extend a) op (Col.extend b)
  | .isNull c => .isNull (Col.extend c)
  | .isNotNull c => .isNotNull (Col.extend c)
  | .bit (ce := ce) c a set => .bit (ce := ce) (Col.extend c) a set
  | .and a b => .and (Pred.extend a) (Pred.extend b)
  | .or a b => .or (Pred.extend a) (Pred.extend b)
  | .opaque f => .opaque fun r => f r.1
  | .«exists» (ent := _) parent fk body =>
      .opaque fun r => (Pred.«exists» parent fk body).denote .empty r.1
  | .«forall» (ent := _) parent fk body =>
      .opaque fun r => (Pred.«forall» parent fk body).denote .empty r.1

/-- Join along a declared foreign key: rows of `α` paired with the
    referenced row of `Target fk`. The residual `get fk = id` is the
    meaning. The residual is opaque, so windows over a join run in Lean. -/
def join {s α} [IsSchema s] [Entity α] [h : HasForeignKey α]
    (q : Query s [α] (Stored α)) (fk : h.ForeignKey)
    [Entity (h.Target fk)] [IsSchema.Has s (h.Target fk)] :
    Query s [α, h.Target fk] (Stored α × Stored (h.Target fk)) where
  rowsOf := inferInstance
  pred :=
    let β := h.Target fk
    Pred.andS (Pred.extend (α := α) (β := β) q.pred)
      (.opaque fun r => (h.get fk r.1.val : Id β) == r.2.id)
  sortBy := .cmp fun x y => q.sortBy.ord x.1 y.1
  order := #[]
  window := q.window
  toRow := id

/-- Meaning: `selectSpec` over the in-memory tables, then the window.
    Always applies the window after the residual filter, matching
    compilation of non-exact plans. -/
def denote {s ts ρ} [IsSchema s] (q : Query s ts ρ) (st : DbState s) : Array ρ :=
  let src := DbState.source st
  let snap := DbState.snapshot st
  let rows := _root_.Id.run <|
    @selectSpec _root_.Id _ ts q.rowsOf src (q.pred.denote snap) q.sortBy
  q.window.apply (rows.map q.toRow)

/-- Compilation: `selectP` pushes LIMIT/OFFSET only when the plan is exact.
    Non-exact plans apply the window in Lean after the residual filter. -/
def exec {s ts ρ} (q : Query s ts ρ) : Db (Array ρ) := do
  if q.exact then
    let rows ← @selectP ts q.rowsOf q.pred q.sortBy q.order q.window
    return rows.map q.toRow
  else
    let rows ← @selectP ts q.rowsOf q.pred q.sortBy q.order {}
    return q.window.apply (rows.map q.toRow)

def execCount {s ts ρ} (q : Query s ts ρ) : Db Nat :=
  @countP ts q.rowsOf q.pred

def execExists {s ts ρ} (q : Query s ts ρ) : Db Bool :=
  @existsP ts q.rowsOf q.pred

end Query

end LeanDb
