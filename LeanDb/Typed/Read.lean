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

/-- A read-only program over schema `s`. -/
inductive Read (s : Type) [IsSchema s] : Type → Type 1 where
  | pure : α → Read s α
  | bind : Read s α → (α → Read s β) → Read s β
  | get (α : Type) [Entity α] [IsSchema.Has s α]
      (id : Id α) : Read s (Option (Valid α))
  | lookup (α : Type) [Entity α] [HasUnique α] [IsSchema.Has s α]
      (ix : Unique α) (key : Unique.Key ix) : Read s (Option (Valid α))
  | firstQ : {ts : List Type} → {ρ : Type} → [GatherState s ts] →
      Query s ts ρ → Read s (Option ρ)
  | all : {ts : List Type} → {ρ : Type} → [GatherState s ts] →
      Query s ts ρ → Read s (List ρ)
  | pageQ : {ts : List Type} → {ρ : Type} → [GatherState s ts] →
      Query s ts ρ → Window → Read s (Page ρ)
  | countQ : {ts : List Type} → {ρ : Type} → [GatherState s ts] →
      Query s ts ρ → Read s Nat
  | existsQ : {ts : List Type} → {ρ : Type} → [GatherState s ts] →
      Query s ts ρ → Read s Bool

instance {s : Type} [IsSchema s] : Monad (Read s) where
  pure := .pure
  bind := .bind

namespace Read

/-- `exists q` — `exists` is a Lean keyword. Requires an exact plan. -/
def «exists» {s ts ρ} [IsSchema s] [GatherState s ts] (q : Query s ts ρ)
    (_h : q.exact = true := by exact_plan) : Read s Bool :=
  .existsQ q

/-- `first q` requires an exact plan (no opaque leaf). -/
def first {s ts ρ} [IsSchema s] [GatherState s ts] (q : Query s ts ρ)
    (_h : q.exact = true := by exact_plan) : Read s (Option ρ) :=
  .firstQ q

/-- `count q` requires an exact plan. -/
def count {s ts ρ} [IsSchema s] [GatherState s ts] (q : Query s ts ρ)
    (_h : q.exact = true := by exact_plan) : Read s Nat :=
  .countQ q

/-- One page; the query must be exact so the window is sound. -/
def page {s ts ρ} [IsSchema s] [GatherState s ts] (q : Query s ts ρ) (w : Window)
    (_h : q.exact = true := by exact_plan) : Read s (Page ρ) :=
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
    if Unique.encodeKey ix (Unique.keyOf ix r.val) == enc then
      Valid.ofStored? r
    else none

/-- Wrap a stored row; an invalid value is not a returned row (corruption). -/
def wrapStored {α} [Entity α] (r : Stored α) : Option (Valid α) :=
  Valid.ofStored? r

/-- Pure meaning. Total on a well-formed state. -/
def denote {s : Type} [IsSchema s] : {α : Type} → Read s α → DbState s → α
  | _, .pure a, _ => a
  | _, .bind r f, st => denote (f (denote r st)) st
  | _, @Read.get _ _ α _ent _has id, st =>
      ((@DbState.get s α inferInstance _ent _has st).rows.find? (·.id == id)).bind
        Valid.ofStored?
  | _, @Read.lookup _ _ α _ent _hu _has ix key, st =>
      @lookupDenote s α inferInstance _ent _hu _has st ix key
  | _, @Read.firstQ _ _ ts ρ _gs q, st =>
      (@Query.denote s ts ρ inferInstance _gs q st)[0]?
  | _, @Read.all _ _ ts ρ _gs q, st =>
      (@Query.denote s ts ρ inferInstance _gs q st).toList
  | _, @Read.pageQ _ _ ts ρ _gs q w, st =>
      let all := @Query.denote s ts ρ inferInstance _gs { q with window := {} } st
      { items := (w.apply all).toList, total := all.size }
  | _, @Read.countQ _ _ ts ρ _gs q, st =>
      (@Query.denote s ts ρ inferInstance _gs { q with window := {} } st).size
  | _, @Read.existsQ _ _ ts ρ _gs q, st =>
      !(@Query.denote s ts ρ inferInstance _gs { q with window := { limit := some 1 } } st).isEmpty

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
  | _, @Read.firstQ _ _ ts ρ _gs q => do
      let rows ← Query.exec (s := s) (ts := ts) { q with window := { q.window with limit := some 1 } }
      return rows[0]?
  | _, @Read.all _ _ ts ρ _gs q => do
      let rows ← Query.exec (s := s) (ts := ts) q
      return rows.toList
  | _, @Read.pageQ _ _ ts ρ _gs q w => do
      let total ← Query.execCount (s := s) (ts := ts) { q with window := {} }
      let items := (← Query.exec (s := s) (ts := ts) { q with window := w }).toList
      return { items, total }
  | _, @Read.countQ _ _ ts _ρ _gs q => Query.execCount (s := s) (ts := ts) { q with window := {} }
  | _, @Read.existsQ _ _ ts _ρ _gs q => Query.execExists (s := s) (ts := ts) { q with window := {} }

/-- One deferred snapshot on this connection. Faults, not domain errors. -/
def run {s α} [IsSchema s] (r : Read s α) : Db (Except DbFault α) :=
  fun conn => ExceptT.mk do
    match ← (readSnapshot (exec r) conn).run with
    | .ok a => return .ok (.ok a)
    | .error e => return .ok (.error (DbFault.ofDbError e))

end Read

/-- Map a service lifecycle error onto a `DbFault`. -/
def Runtime.Service.faultOfRuntime : Runtime.RuntimeError → DbFault
  | .host m => .io m
  | .notReady st => .io s!"service is not ready ({repr st})"
  | .reentrant => .io "withConnection called reentrantly from its own callback"
  | .gated e => DbFault.ofDbError e

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
