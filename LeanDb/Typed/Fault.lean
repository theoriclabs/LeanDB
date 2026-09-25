import LeanDb.Core

namespace LeanDb

/-! # Infrastructure faults (M14)

These are not failures of a `Read`/`Txn` program: the meaning never
produces them. If execution stops for one, the request aborts with no
effect. On a well-formed state a decode failure cannot happen; if it
does, it is corruption (a raw-SQL edit, a bad migration).
-/

inductive DbFault where
  /-- SQLITE_BUSY / SQLITE_LOCKED past `busy_timeout`. -/
  | locking (message : String)
  /-- Host I/O, a poisoned connection, or an unclassified SQLite error. -/
  | io (message : String)
  /-- A row that does not decode, or fails its invariant — the state is
      not well-formed. -/
  | corruption (message : String)
  /-- The file's fingerprint is not the code's. -/
  | schemaMismatch (expected actual : String)
  deriving Repr, BEq

def DbFault.message : DbFault → String
  | .locking m => m
  | .io m => m
  | .corruption m => m
  | .schemaMismatch e a =>
      s!"schema fingerprint mismatch: code has {e}, instance has {a}"

instance : ToString DbFault := ⟨DbFault.message⟩

private def busyMsg (msg : String) : Bool :=
  let m := msg.toLower
  (m.splitOn "locked").length > 1 || (m.splitOn "busy").length > 1

/-- Map an engine error onto a fault. Domain errors (`notFound`, `stale`,
    `duplicate`, …) become `.io` here: they are not `Read` failures, and
    a well-formed read should not produce them. -/
def DbFault.ofDbError : DbError → DbFault
  | .schemaMismatch e a => .schemaMismatch e a
  | .decode t f m => .corruption s!"{t}.{f}: {m}"
  | .invariant t n => .corruption s!"{t}: invariant {n}"
  | .enumDrift t c v => .corruption s!"{t}.{c}: {v}"
  | .sqlite m => if busyMsg m then .locking m else .io m
  | .poisoned m => .io s!"connection poisoned: {m}"
  | .transport m => .io m
  | e => .io e.message

end LeanDb
