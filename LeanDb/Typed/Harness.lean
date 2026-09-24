import LeanDb.Typed.Txn

/-! # Execution-equals-meaning harness (M14b)

Compare `Txn.run` against `Txn.denote` on a well-formed `DbState`: same
answer, same failure constructor and payload, same final tables.
-/

namespace LeanDb.Harness

def tableEq {α} [Entity α] [BEq α] (a b : Table α) : Bool :=
  a.next == b.next && a.rows.length == b.rows.length &&
    (a.rows.zip b.rows).all fun (x, y) => x.id == y.id && x.val == y.val

def storedEq {α} [BEq α] (a b : Stored α) : Bool :=
  a.id == b.id && a.val == b.val

def optStoredEq {α} [BEq α] : Option (Stored α) → Option (Stored α) → Bool
  | none, none => true
  | some a, some b => storedEq a b
  | _, _ => false

instance {α} [BEq α] : BEq (Stored α) where
  beq := storedEq

def exceptEq {ε α} (eqE : ε → ε → Bool) (eqA : α → α → Bool) :
    Except ε α → Except ε α → Bool
  | .ok a, .ok b => eqA a b
  | .error e, .error f => eqE e f
  | _, _ => false

/-- Compare two `DbState`s on the listed entities. -/
def stateEq {s} [IsSchema s] (st₁ st₂ : DbState s)
    (checks : List (DbState s → DbState s → Bool)) : Bool :=
  checks.all (fun c => c st₁ st₂)

structure Rng where
  n : UInt32

def Rng.ofNat (seed : Nat) : Rng := ⟨UInt32.ofNat seed⟩

def Rng.next (r : Rng) : Rng × Nat :=
  let n' := r.n * 1664525 + 1013904223
  (⟨n'⟩, n'.toNat)

def Rng.nat (r : Rng) (lo hi : Nat) : Rng × Nat :=
  let (r, n) := r.next
  if hi ≤ lo then (r, lo)
  else (r, lo + n % (hi - lo + 1))

def Rng.bool (r : Rng) : Rng × Bool :=
  let (r, n) := r.next
  (r, n % 2 == 0)

/-- `checkWF` after a completed program. Production `load` must be WF. -/
def requireWF {s} [IsSchema s] (st : DbState s) (msg : String) : DbM Unit :=
  unless DbState.checkWF st do
    throw (.sqlite s!"FAIL: {msg}: DbState.checkWF failed")

end LeanDb.Harness
