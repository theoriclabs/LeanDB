import LeanDb.Typed.Read
import LeanDb.Typed.Write

/-! # Transaction programs (M14b)

`Txn σ s ε α` reads and writes over schema `s`, may abort with `ε`, and
is all-or-nothing. `σ` is an ST-style transaction index: `Current σ α`
handles cannot leave `Txn.run` (rank-2). `Read` embeds; writes take
`Checked α`.
-/

namespace LeanDb

/-- A row this transaction has seen. Coerces to `Stored α`. Cannot leave
    its transaction: `Txn.run` takes `{σ : Type} → Txn σ s ε α`. -/
structure Current (σ : Type) (α : Type) [Entity α] where
  stored : Stored α

def Current.id {σ α} [Entity α] (c : Current σ α) : Id α := c.stored.id

def Current.val {σ α} [Entity α] (c : Current σ α) : α := c.stored.val

def Current.toStored {σ α} [Entity α] (c : Current σ α) : Stored α := c.stored

instance {σ α} [Entity α] : CoeOut (Current σ α) (Stored α) where
  coe := Current.toStored

/-- Reads and writes over schema `s`. Aborts with `ε` discard every write. -/
inductive Txn (σ : Type) (s : Type) (ε : Type) : Type → Type 1 where
  | pure : α → Txn σ s ε α
  | bind : Txn σ s ε α → (α → Txn σ s ε β) → Txn σ s ε β
  | liftRead : Read s α → Txn σ s ε α
  | get (α : Type) [Entity α] (id : Id α) : Txn σ s ε (Option (Current σ α))
  | lookup (α : Type) [Entity α] [HasUnique α]
      (ix : Unique α) (key : Unique.Key ix) : Txn σ s ε (Option (Current σ α))
  | throw : ε → Txn σ s ε α
  | orAbort : Txn σ s ε (Except E α) → (E → ε) → Txn σ s ε α
  | orElse : Txn σ s ε (Except E α) → (E → Txn σ s ε α) → Txn σ s ε α
  | insert (α : Type) [Entity α] [HasUnique α] [HasForeignKey α]
      (v : Checked α) : Txn σ s ε (Except (InsertError α) (Current σ α))
  | update (α : Type) [Entity α] [HasUnique α] [HasForeignKey α]
      (old : Stored α) (new : Checked α) :
      Txn σ s ε (Except (UpdateError α) (Stored α))
  | set (α : Type) [Entity α] [HasUnique α] [HasForeignKey α]
      (row : Current σ α) (new : Checked α) :
      Txn σ s ε (Except (SetError α (Fields.all α)) (Current σ α))
  | patch (α : Type) [Entity α] [HasUnique α] [HasForeignKey α]
      (row : Current σ α) (fs : Fields α) (new : Checked α) :
      Txn σ s ε (Except (SetError α fs) (Current σ α))
  | append (α : Type) [Entity α] [HasListField α]
      (old : Stored α) (new : Checked α) :
      Txn σ s ε (Except (AppendError α) (Stored α))
  | delete (α : Type) [Entity α] [HasReferencedBy s α] (id : Id α) :
      Txn σ s ε (Except (DeleteError s α) (Stored α))

instance {σ s ε : Type} : Monad (Txn σ s ε) where
  pure := .pure
  bind := .bind

namespace Txn

def ofRead {σ s ε α} (r : Read s α) : Txn σ s ε α := .liftRead r

instance {σ s ε α} : Coe (Read s α) (Txn σ s ε α) where
  coe := ofRead

/-- Insert when the schema makes `InsertError` uninhabited. `IsEmpty` is
    generated for tables with no unique index and no `Ref`. -/
def insertNew {σ s ε α} [Entity α] [HasUnique α] [HasForeignKey α]
    [IsEmpty (InsertError α)] (v : Checked α) : Txn σ s ε (Current σ α) :=
  Txn.bind (.insert α v) fun
    | .ok row => Txn.pure row
    | .error e => IsEmpty.elim e

end Txn

/-- Lift a checked/`Except` value into the transaction, aborting on error. -/
def Except.orAbort {σ s ε E α} (x : Except E α) (f : E → ε) : Txn σ s ε α :=
  match x with
  | .ok a => Txn.pure a
  | .error e => Txn.throw (f e)

end LeanDb
