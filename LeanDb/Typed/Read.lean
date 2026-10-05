import LeanDb.Typed.Query
import LeanDb.Typed.Fault
import LeanDb.Runtime

namespace LeanDb

/-! # Read programs (M14)

`Read s α` has no write constructor and no failure channel. On a
well-formed state its meaning `denote` is total. `run` executes in one
deferred snapshot and reports infrastructure problems as `DbFault`.
-/

/-- One page of a query, from the same snapshot as its total. -/
structure Page (α : Type) where
  items : List α
  total : Nat
  deriving Repr, BEq

/-- Recover the `Valid` proof stored in the table for a gathered `Stored`
    row. `Query.denote` gathers `Valid.toStored`, so the lookup succeeds
    on those rows. -/
def recoverValid {s α} [IsSchema s] [Entity α] [IsSchema.Has s α]
    (st : DbState s) (r : Stored α) : Option (Valid α) :=
  (DbState.get (α := α) st).rows.find? (fun v => v.id == r.id)

/-- How `first`/`all`/`page` present a query's `ρ`. `Query.from` / `where'` /
    `orderBy` still work over `Stored α` (and `Valid` coerces to it). -/
class QueryRow (s : Type) [IsSchema s] (ts : List Type) (ρ : Type) where
  Out : Type
  wrap : DbState s → ρ → Option Out
  wrapExec : ρ → Db Out

instance {s α : Type} [IsSchema s] [Entity α] [IsSchema.Has s α] :
    QueryRow s [α] (Stored α) where
  Out := Valid α
  wrap st r := recoverValid st r
  wrapExec := Valid.ofStoredM

instance {s α β : Type} [IsSchema s] [Entity α] [Entity β]
    [IsSchema.Has s α] [IsSchema.Has s β] :
    QueryRow s [α, β] (Stored α × Stored β) where
  Out := Valid α × Valid β
  wrap st r :=
    match recoverValid (α := α) st r.1, recoverValid (α := β) st r.2 with
    | some a, some b => some (a, b)
    | _, _ => none
  wrapExec r := do
    let a ← Valid.ofStoredM r.1
    let b ← Valid.ofStoredM r.2
    return (a, b)

/-- A read-only program over schema `s`. -/
inductive Read (s : Type) [IsSchema s] : Type → Type 1 where
  | pure : α → Read s α
  | bind : Read s α → (α → Read s β) → Read s β
  | get (α : Type) [Entity α] [IsSchema.Has s α]
      (id : Id α) : Read s (Option (Valid α))
  | lookup (α : Type) [Entity α] [HasUnique α] [IsSchema.Has s α]
      (ix : Unique α) (key : Unique.Key ix) : Read s (Option (Valid α))
  | firstQ : {ts : List Type} → {ρ : Type} → [GatherState s ts] → [out : QueryRow s ts ρ] →
      Query s ts ρ → Read s (Option out.Out)
  | all : {ts : List Type} → {ρ : Type} → [GatherState s ts] → [out : QueryRow s ts ρ] →
      Query s ts ρ → Read s (List out.Out)
  | pageQ : {ts : List Type} → {ρ : Type} → [GatherState s ts] → [out : QueryRow s ts ρ] →
      Query s ts ρ → Window → Read s (Page out.Out)
  | countQ : {ts : List Type} → {ρ : Type} → [GatherState s ts] →
      Query s ts ρ → Read s Nat
  | existsQ : {ts : List Type} → {ρ : Type} → [GatherState s ts] →
      Query s ts ρ → Read s Bool
  /-- Indexed existence on a generated unique association, without hydration. -/
  | memberContains {p t e : Type} [Entity p] [Entity t] [Entity e]
      [HasUnique e] [HasForeignKey e] [IsSchema.Has s e]
      (relation : MemberRelation p t e) (parent : Id p) (target : Id t) : Read s Bool
  /-- Native/admin column projection. Protected adapters expose this only
      through their policy-first capability. SQL selects this column alone. -/
  | memberField {p t e : Type} [Entity p] [Entity t] [Entity e]
      [HasUnique e] [HasForeignKey e] [IsSchema.Has s e] [IsSchema.Has s t]
      (relation : MemberRelation p t e) (parent : Id p)
      (field : Entity.Field t) : Read s (List (Entity.fieldTy field))
  /-- Native/admin column projection through an ordinary link entity (a
      typed semi-join, e.g. `Loan ⋈ Member`): one target column for every target
      some edge relates to `parent`, each target once, in target-ID order.
      SQL selects this column alone; the target row is never hydrated. -/
  | linkField {p t e : Type} [Entity p] [Entity t] [Entity e]
      [IsSchema.Has s e] [IsSchema.Has s t]
      (relation : LinkRelation p t e) (parent : Id p)
      (field : Entity.Field t) : Read s (List (Entity.fieldTy field))

instance {s : Type} [IsSchema s] : Monad (Read s) where
  pure := .pure
  bind := .bind

namespace Read

/-- Policy and projection execute under `Read.run`'s one snapshot. The hidden
    branch does not evaluate the projection. The caller supplies the portable
    disclosure constructors; LeanDB does not own a second disclosure type. -/
def discloseWith {s α β} [IsSchema s] (policy : Read s Bool)
    (projection : Read s α) (visible : α → β) (hidden : β) : Read s β := do
  if ← policy then return visible (← projection) else return hidden

def memberContainsDenote {s p t e} [IsSchema s] [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e] [IsSchema.Has s e]
    (relation : MemberRelation p t e) (parent : Id p) (target : Id t)
    (st : DbState s) : Bool :=
  (st.get (α := e)).rows.any fun edge =>
    relation.getParent edge.val == parent && relation.getTarget edge.val == target

def memberFieldDenote {s p t e} [IsSchema s] [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e] [IsSchema.Has s e] [IsSchema.Has s t]
    (relation : MemberRelation p t e) (parent : Id p) (field : Entity.Field t)
    (st : DbState s) : List (Entity.fieldTy field) :=
  ((st.get (α := t)).rows.filter fun target =>
    memberContainsDenote relation parent target.id st).map fun target => Entity.get field target.val

def memberContainsSql {p t e} [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e] (relation : MemberRelation p t e) : String :=
  s!"SELECT EXISTS(SELECT 1 FROM {quoteIdent (Entity.tableName e)} WHERE {quoteIdent (Entity.fieldName relation.parentField)} = ? AND {quoteIdent (Entity.fieldName relation.targetField)} = ?)"

def memberContainsExec {p t e} [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e]
    (relation : MemberRelation p t e) (parent : Id p) (target : Id t) : Db Bool :=
  untrackedSqlite fun db => do
    let stmt ← db.prepare (memberContainsSql relation)
    stmt.bindInt64 1 parent.toInt64
    stmt.bindInt64 2 target.toInt64
    discard stmt.step
    return (← stmt.columnInt64 0) != 0

def memberFieldSql {p t e} [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e]
    (relation : MemberRelation p t e) (field : Entity.Field t) : String :=
  s!"SELECT t.{quoteIdent (Entity.fieldName field)} FROM {quoteIdent (Entity.tableName t)} AS t JOIN {quoteIdent (Entity.tableName e)} AS e ON e.{quoteIdent (Entity.fieldName relation.targetField)} = t.id WHERE e.{quoteIdent (Entity.fieldName relation.parentField)} = ? ORDER BY t.id ASC"

def memberFieldExec {p t e} [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e]
    (relation : MemberRelation p t e) (parent : Id p) (field : Entity.Field t) :
    Db (List (Entity.fieldTy field)) := do
  let cols ← untrackedSqlite fun db => do
    let stmt ← db.prepare (memberFieldSql relation field)
    stmt.bindInt64 1 parent.toInt64
    let mut cols : List (Option Col) := []
    while ← stmt.step do cols := (← readCol stmt 0) :: cols
    return cols.reverse
  cols.mapM fun col => do
    let some col := col | throw (.decode (Entity.tableName t) (Entity.fieldName field) "unsupported SQLite value")
    match (Entity.codec field).fromCol col with
    | .ok value => return value
    | .error why => throw (.decode (Entity.tableName t) (Entity.fieldName field) why)

/-- Proof-carrying disclosure. The projection can only be built from a proof
    of `allowed`; the decision is made first. When it is negative the program
    *is* `pure hidden` (`Read.discloseIf_denied`), so the executor prepares no
    statement at all — the protected table need not even exist. -/
def discloseIf {s α β} [IsSchema s] (allowed : Prop) [Decidable allowed]
    (projection : allowed → Read s α) (visible : α → β) (hidden : β) : Read s β :=
  if h : allowed then .bind (projection h) (fun a => .pure (visible a)) else .pure hidden

def linkContainsDenote {s p t e} [IsSchema s] [Entity p] [Entity t] [Entity e]
    [IsSchema.Has s e] (relation : LinkRelation p t e) (parent : Id p) (target : Id t)
    (st : DbState s) : Bool :=
  (st.get (α := e)).rows.any fun edge =>
    relation.getParent edge.val == parent && relation.getTarget edge.val == target

def linkFieldDenote {s p t e} [IsSchema s] [Entity p] [Entity t] [Entity e]
    [IsSchema.Has s e] [IsSchema.Has s t]
    (relation : LinkRelation p t e) (parent : Id p) (field : Entity.Field t)
    (st : DbState s) : List (Entity.fieldTy field) :=
  ((st.get (α := t)).rows.filter fun target =>
    linkContainsDenote relation parent target.id st).map fun target => Entity.get field target.val

/-- The one statement `linkField` prepares. `IN` keeps each target once even
    when several edges relate it, so the answer is the meaning's on any
    state; the edge side is answered from an index that starts with the
    parent column (for `Loan`, a `(book, member)` unique index covers it). -/
def linkFieldSql {p t e} [Entity p] [Entity t] [Entity e]
    (relation : LinkRelation p t e) (field : Entity.Field t) : String :=
  s!"SELECT t.{quoteIdent (Entity.fieldName field)} FROM {quoteIdent (Entity.tableName t)} AS t WHERE t.id IN (SELECT e.{quoteIdent (Entity.fieldName relation.targetField)} FROM {quoteIdent (Entity.tableName e)} AS e WHERE e.{quoteIdent (Entity.fieldName relation.parentField)} = ?) ORDER BY t.id ASC"

def linkFieldExec {p t e} [Entity p] [Entity t] [Entity e]
    (relation : LinkRelation p t e) (parent : Id p) (field : Entity.Field t) :
    Db (List (Entity.fieldTy field)) := do
  let cols ← untrackedSqlite fun db => do
    let stmt ← db.prepare (linkFieldSql relation field)
    stmt.bindInt64 1 parent.toInt64
    let mut cols : List (Option Col) := []
    while ← stmt.step do cols := (← readCol stmt 0) :: cols
    return cols.reverse
  cols.mapM fun col => do
    let some col := col | throw (.decode (Entity.tableName t) (Entity.fieldName field) "unsupported SQLite value")
    match (Entity.codec field).fromCol col with
    | .ok value => return value
    | .error why => throw (.decode (Entity.tableName t) (Entity.fieldName field) why)

/-- Row by one declared unique key of `α`: a single field or a composite.
    The same program as `lookup`; it executes as an equality lookup on that
    unique index (`lookupSql`). Backs portable `T.findBy`. -/
abbrev findBy {s} [IsSchema s] (α : Type) [Entity α] [HasUnique α] [IsSchema.Has s α]
    (ix : Unique α) (key : Unique.Key ix) : Read s (Option (Valid α)) :=
  .lookup α ix key

/-- The statement `lookup`/`findBy` (and `Txn.lookup`) prepare for `ix`, with
    its bound key: `selectP` routes the equality plan through `fetchFiltered`
    for table 0. For `EXPLAIN QUERY PLAN`. -/
def lookupSql {α} [Entity α] [HasUnique α] (ix : Unique α) (key : Unique.Key ix) :
    String × Array Col :=
  filteredSelectSql α ((Unique.predOf ix key).approx.forTable 0)

/-- `exists q` — `exists` is a Lean keyword. Requires an exact plan. -/
def «exists» {s ts ρ} [IsSchema s] [GatherState s ts] (q : Query s ts ρ)
    (_h : q.exact = true := by exact_plan) : Read s Bool :=
  .existsQ q

/-- `first q` requires an exact plan (no opaque leaf). Answers `Valid α`
    for a from-query (and `Valid α × Valid β` for a join). -/
def first {s ts ρ} [IsSchema s] [GatherState s ts] [out : QueryRow s ts ρ]
    (q : Query s ts ρ) (_h : q.exact = true := by exact_plan) :
    Read s (Option out.Out) :=
  .firstQ q

/-- `count q` requires an exact plan. -/
def count {s ts ρ} [IsSchema s] [GatherState s ts] (q : Query s ts ρ)
    (_h : q.exact = true := by exact_plan) : Read s Nat :=
  .countQ q

/-- One page; the query must be exact so the window is sound. -/
def page {s ts ρ} [IsSchema s] [GatherState s ts] [out : QueryRow s ts ρ]
    (q : Query s ts ρ) (w : Window) (_h : q.exact = true := by exact_plan) :
    Read s (Page out.Out) :=
  .pageQ q w

/-- Unwindowed `all` may keep a Lean residual. A windowed query must go
    through `withWindow`, which already demands exactness. -/
abbrev exists' {s ts ρ} [IsSchema s] [GatherState s ts] (q : Query s ts ρ)
    (h : q.exact = true := by exact_plan) : Read s Bool :=
  «exists» q h

/-- Row by unique key, from in-memory state. -/
def lookupDenote {s α} [IsSchema s] [Entity α] [HasUnique α] [IsSchema.Has s α]
    (st : DbState s) (ix : Unique α) (key : Unique.Key ix) : Option (Valid α) :=
  let enc := Unique.encodeKey ix key
  (DbState.get (α := α) st).rows.findSome? fun r =>
    if Unique.keyClash (Unique.encodeKey ix (Unique.keyOf ix r.val)) enc then
      some r
    else none

/-- Pure meaning. Total on a well-formed state. -/
def denote {s : Type} [IsSchema s] : {α : Type} → Read s α → DbState s → α
  | _, .pure a, _ => a
  | _, .bind r f, st => denote (f (denote r st)) st
  | _, @Read.get _ _ α _ent _has id, st =>
      ((@DbState.get s α inferInstance _ent _has st).rows.find? (·.id == id))
  | _, @Read.lookup _ _ α _ent _hu _has ix key, st =>
      @lookupDenote s α inferInstance _ent _hu _has st ix key
  | _, @Read.firstQ _ _ ts ρ _gs _out q, st =>
      ((@Query.denote s ts ρ inferInstance _gs q st)[0]?).bind (_out.wrap st)
  | _, @Read.all _ _ ts ρ _gs _out q, st =>
      ((@Query.denote s ts ρ inferInstance _gs q st).toList).filterMap (_out.wrap st)
  | _, @Read.pageQ _ _ ts ρ _gs _out q w, st =>
      let all := @Query.denote s ts ρ inferInstance _gs { q with window := {} } st
      { items := (w.apply all).toList.filterMap (_out.wrap st), total := all.size }
  | _, @Read.countQ _ _ ts ρ _gs q, st =>
      (@Query.denote s ts ρ inferInstance _gs { q with window := {} } st).size
  | _, @Read.existsQ _ _ ts ρ _gs q, st =>
      !(@Query.denote s ts ρ inferInstance _gs { q with window := { limit := some 1 } } st).isEmpty
  | _, @Read.memberContains _ _ p t e ep et ee hu hf he relation parent target, st =>
      @memberContainsDenote s p t e inferInstance ep et ee hu hf he relation parent target st
  | _, @Read.memberField _ _ p t e ep et ee hu hf he ht relation parent field, st =>
      @memberFieldDenote s p t e inferInstance ep et ee hu hf he ht relation parent field st
  | _, @Read.linkField _ _ p t e ep et ee he ht relation parent field, st =>
      @linkFieldDenote s p t e inferInstance ep et ee he ht relation parent field st

/-- Execute against SQLite. `get`/`lookup` use the engine verbs;
    `first`/`all`/`page`/`count`/`exists` go through `Query.exec`, which
    pushes LIMIT/OFFSET/COUNT/EXISTS only for exact plans. -/
def exec {s : Type} [IsSchema s] : {α : Type} → Read s α → Db α
  | _, .pure a => (Pure.pure a : Db _)
  | _, .bind r f => do exec (f (← exec r))
  | _, @Read.get _ _ α _ent _has id => do
      match ← @LeanDb.get α _ent id with
      | none => (Pure.pure (f := Db) none)
      | some r =>
          match Valid.ofStored? r with
          | some v => (Pure.pure (f := Db) (some v))
          | none => DbM.ofExcept (.error (.invariant (Entity.tableName α) "Valid.ofStored?"))
  | _, @Read.lookup _ _ α _ent _hu _has ix key => do
      let rows ← selectP (ts := [α]) (@Unique.predOf α _ent _hu ix key)
      match rows[0]? with
      | none => (Pure.pure (f := Db) none)
      | some r =>
          match Valid.ofStored? r with
          | some v => (Pure.pure (f := Db) (some v))
          | none => DbM.ofExcept (.error (.invariant (Entity.tableName α) "Valid.ofStored?"))
  | _, @Read.firstQ _ _ ts ρ _gs _out q => do
      -- Honour an existing `limit := some 0` (empty); otherwise cap at 1.
      -- Overwriting 0 with 1 made `first` after a zero window disagree
      -- with denote.
      let lim : Option Nat :=
        match q.window.limit with
        | some 0 => some 0
        | _ => some 1
      let rows ← Query.exec (s := s) (ts := ts) { q with window := { q.window with limit := lim } }
      match rows[0]? with
      | none => (Pure.pure (f := Db) none)
      | some r => some <$> _out.wrapExec r
  | _, @Read.all _ _ ts ρ _gs _out q => do
      let rows ← Query.exec (s := s) (ts := ts) q
      rows.toList.mapM _out.wrapExec
  | _, @Read.pageQ _ _ ts ρ _gs _out q w => do
      let total ← Query.execCount (s := s) (ts := ts) { q with window := {} }
      let items ← (← Query.exec (s := s) (ts := ts) { q with window := w }).toList.mapM _out.wrapExec
      return { items, total }
  | _, @Read.countQ _ _ ts _ρ _gs q => Query.execCount (s := s) (ts := ts) { q with window := {} }
  | _, @Read.existsQ _ _ ts _ρ _gs q => Query.execExists (s := s) (ts := ts) { q with window := {} }
  | _, @Read.memberContains _ _ p t e ep et ee hu hf _he relation parent target =>
      @memberContainsExec p t e ep et ee hu hf relation parent target
  | _, @Read.memberField _ _ p t e ep et ee hu hf _he _ht relation parent field =>
      @memberFieldExec p t e ep et ee hu hf relation parent field
  | _, @Read.linkField _ _ p t e ep et ee _he _ht relation parent field =>
      @linkFieldExec p t e ep et ee relation parent field

/-- One deferred snapshot on this connection. Faults, not domain errors. -/
def runPrepared {s α env} [IsSchema s] (prepare : Db env) (build : env → Read s α) :
    Db (Except DbFault α) :=
  fun conn => ExceptT.mk do
    match ← (readSnapshot (do let environment ← prepare; exec (build environment)) conn).run with
    | .ok a => return .ok (.ok a)
    | .error e => return .ok (.error (DbFault.ofDbError e))

def run {s α} [IsSchema s] (r : Read s α) : Db (Except DbFault α) :=
  runPrepared (Pure.pure (f := Db) ()) (fun _ => r)

end Read

/-- Map a service lifecycle error onto a `DbFault`. -/
def Runtime.Service.faultOfRuntime : Runtime.RuntimeError → DbFault
  | .host m => .io m
  | .notReady st => .io s!"service is not ready ({repr st})"
  | .reentrant => .io "withConnection called reentrantly from its own callback"
  | .gated e => DbFault.ofDbError e
  | .snapshotBusy => .io "a snapshot is already running"
  | .snapshotAborted => .io "snapshot aborted: restore claimed the connection"

/-- Run a `Read` on a pooled reader connection, in one deferred snapshot.
    The writer connection is never used (`withReader`); a writable
    connection here is a `DbFault`. -/
def Runtime.Service.runRead {s α} [IsSchema s] (svc : Runtime.Service)
    (r : Read s α) : IO (Except DbFault α) := do
  match ← svc.withReader fun conn => do
    unless conn.readOnly do
      throw <| IO.userError "runRead obtained a writable connection"
    (Read.run (s := s) r conn).run
  with
  | .error e => return .error (Runtime.Service.faultOfRuntime e)
  | .ok (.error e) => return .error (DbFault.ofDbError e)
  | .ok (.ok (.error f)) => return .error f
  | .ok (.ok (.ok a)) => return .ok a

end LeanDb
