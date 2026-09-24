import LeanDb.Typed.Query
import LeanDb.Typed.Fault

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
inductive Read (s : Type) : Type → Type 1 where
  | pure : α → Read s α
  | bind : Read s α → (α → Read s β) → Read s β
  | get (α : Type) [Entity α] (id : Id α) : Read s (Option (Stored α))
  | lookup (α : Type) [Entity α] [HasUnique α]
      (ix : Unique α) (key : Unique.Key ix) : Read s (Option (Stored α))
  | first : {ts : List Type} → {ρ : Type} → Query s ts ρ → Read s (Option ρ)
  | all : {ts : List Type} → {ρ : Type} → Query s ts ρ → Read s (List ρ)
  | page : {ts : List Type} → {ρ : Type} → Query s ts ρ → Window → Read s (Page ρ)
  | count : {ts : List Type} → {ρ : Type} → Query s ts ρ → Read s Nat
  | exists' : {ts : List Type} → {ρ : Type} → Query s ts ρ → Read s Bool

instance {s : Type} : Monad (Read s) where
  pure := .pure
  bind := .bind

namespace Read

/-- `exists q` — `exists` is a Lean keyword. -/
abbrev «exists» {s ts ρ} (q : Query s ts ρ) : Read s Bool := .exists' q

/-- Row by unique key, from in-memory state. -/
def lookupDenote {s α} [IsSchema s]
    (st : DbState s) (ent : Entity α) (hu : HasUnique α)
    (ix : @Unique α ent hu) (key : @Unique.Key α ent hu ix) : Option (Stored α) :=
  let enc := @Unique.encodeKey α ent hu ix key
  let rows := _root_.Id.run (@st.source.load 0 α ent)
  rows.toList.find? fun r =>
    @Unique.encodeKey α ent hu ix (@Unique.keyOf α ent hu ix r.val) == enc

/-- Pure meaning. Total on a well-formed state. -/
def denote {s : Type} [IsSchema s] : {α : Type} → Read s α → DbState s → α
  | _, .pure a, _ => a
  | _, .bind r f, st => denote (f (denote r st)) st
  | _, @Read.get _ α inst id, st =>
      (_root_.Id.run (@st.source.load 0 α inst)).toList.find? (·.id == id)
  | _, @Read.lookup _ α instE instU ix key, st =>
      lookupDenote st instE instU ix key
  | _, .first q, st => (Query.denote (s := s) q st)[0]?
  | _, .all q, st => (Query.denote (s := s) q st).toList
  | _, .page q w, st =>
      let all := Query.denote (s := s) { q with window := {} } st
      { items := (w.apply all).toList, total := all.size }
  | _, .count q, st => (Query.denote (s := s) { q with window := {} } st).size
  | _, .exists' q, st =>
      !(Query.denote (s := s) { q with window := { limit := some 1 } } st).isEmpty

/-- Execute against SQLite. `get`/`lookup` use the engine verbs;
    `first`/`all`/`page`/`count`/`exists` go through `Query.exec`, which
    pushes LIMIT/OFFSET/COUNT/EXISTS only for exact plans. -/
def exec {s : Type} [IsSchema s] : {α : Type} → Read s α → Db α
  | _, .pure a => (Pure.pure a : Db _)
  | _, .bind r f => do exec (f (← exec r))
  | _, @Read.get _ α inst id =>
      @LeanDb.get α inst id
  | _, @Read.lookup _ α instE instU ix key => do
      let rows ← selectP (ts := [α]) (@Unique.predOf α instE instU ix key)
      return rows[0]?
  | _, .first q => do
      let rows ← Query.exec (s := s) { q with window := { q.window with limit := some 1 } }
      return rows[0]?
  | _, .all q => do
      let rows ← Query.exec (s := s) q
      return rows.toList
  | _, .page q w => do
      -- Same snapshot: count and the page share `readSnapshot` in `run`.
      let total ← Query.execCount (s := s) { q with window := {} }
      let items := (← Query.exec (s := s) { q with window := w }).toList
      return { items, total }
  | _, .count q => Query.execCount (s := s) { q with window := {} }
  | _, .exists' q => Query.execExists (s := s) { q with window := {} }

/-- One deferred snapshot on this connection. Faults, not domain errors. -/
def run {s α} [IsSchema s] (r : Read s α) : Db (Except DbFault α) :=
  fun conn => ExceptT.mk do
    match ← (readSnapshot (exec r) conn).run with
    | .ok a => return .ok (.ok a)
    | .error e => return .ok (.error (DbFault.ofDbError e))

end Read

end LeanDb
