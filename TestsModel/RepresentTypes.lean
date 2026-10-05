/- Library-free value types with private constructors, as an app's rules module would keep
   them (no library import). `Represent.lean` stores and sends them through `represent`. -/

/-- A closed interval of naturals. The constructor is private, so `lo ≤ hi` always holds. -/
structure Interval where
  private mk ::
  lo : Nat
  hi : Nat
  deriving BEq, Repr

namespace Interval
def make (lo hi : Nat) (_ : lo ≤ hi) : Interval := ⟨lo, hi⟩
def toPair (interval : Interval) : Nat × Nat := (interval.lo, interval.hi)
/-- The only way back from a pair: checks `lo ≤ hi`. -/
def check (pair : Nat × Nat) : Option Interval :=
  if h : pair.1 ≤ pair.2 then some (make pair.1 pair.2 h) else none
end Interval

def isSorted : List Nat → Bool
  | a :: b :: rest => a ≤ b && isSorted (b :: rest)
  | _ => true

/-- A list of naturals in nondecreasing order. -/
structure SortedList where
  private mk ::
  items : List Nat
  deriving BEq, Repr

namespace SortedList
def ofList? (items : List Nat) : Except String SortedList :=
  if isSorted items then .ok ⟨items⟩ else .error "items are not in nondecreasing order"
def empty : SortedList := ⟨[]⟩
end SortedList

/-- A value type with a private constructor and no adapter (see `negative/RepresentMissing`). -/
structure Opaque where
  private mk ::
  secret : Nat
