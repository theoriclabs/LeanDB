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

/-! ## Pure meaning -/

namespace Txn

def parentEq {α} [Entity α] (a b : α) : Bool :=
  Entity.encode a == Entity.encode b

def firstDuplicate {s α} [IsSchema s] [Entity α] [HasUnique α]
    (v : α) (st : DbState s) (except : Option (Id α)) : Option (Unique α × Id α) :=
  Unique.all α |>.findSome? fun ix =>
    let enc := Unique.encodeKey ix (Unique.keyOf ix v)
    (DbState.get (α := α) st).rows.findSome? fun r =>
      if except == some r.id then none
      else if Unique.encodeKey ix (Unique.keyOf ix r.val) == enc then some (ix, r.id)
      else none

def fkMissing {s α} [IsSchema s] [Entity α] [hf : HasForeignKey α]
    (fk : hf.ForeignKey) (v : α) (st : DbState s) : Bool :=
  let tgt := hf.get fk v
  let inst := hf.targetEntity fk
  let tbl := @DbState.get s (hf.Target fk) inferInstance inst st
  !(tbl.rows.any fun r => r.id.toInt64 == tgt.toInt64)

def firstMissingRef {s α} [IsSchema s] [Entity α] [HasForeignKey α]
    (v : α) (st : DbState s) : Option (ForeignKey α) :=
  ForeignKey.all α |>.find? (fkMissing · v st)

def firstDuplicateTouching {s α} [IsSchema s] [Entity α] [HasUnique α]
    (fs : Fields α) (v : α) (st : DbState s) (except : Option (Id α)) :
    Option (Unique.Touching fs × Id α) :=
  Unique.all α |>.findSome? fun ix =>
    if h : Unique.touches ix fs then
      let enc := Unique.encodeKey ix (Unique.keyOf ix v)
      (DbState.get (α := α) st).rows.findSome? fun r =>
        if except == some r.id then none
        else if Unique.encodeKey ix (Unique.keyOf ix r.val) == enc then
          some (Unique.toTouching ix h, r.id)
        else none
    else none

def firstMissingWithin {s α} [IsSchema s] [Entity α] [HasForeignKey α]
    (fs : Fields α) (v : α) (st : DbState s) : Option (ForeignKey.Within fs) :=
  ForeignKey.all α |>.findSome? fun fk =>
    if h : ForeignKey.within fk fs then
      if fkMissing fk v st then some (ForeignKey.toWithin fk h) else none
    else none

def listsMoved {α} [Entity α] (stored old : α) : Bool :=
  (Entity.children (α := α)).any fun link =>
    (link.rows stored).size != (link.rows old).size

def firstNotAppend {α} [Entity α] [HasListField α] (old new : α) : Option (ListField α) :=
  (Entity.children (α := α)).findSome? fun link =>
    let before := link.rows old
    let after := link.rows new
    if before.size ≤ after.size && after.extract 0 before.size == before then none
    else ListField.all α |>.find? (fun f => ListField.table f == link.table)

def firstRestricted {s α} [IsSchema s] [HasReferencedBy s α]
    (st : DbState s) (id : Id α) : Option (ReferencedBy s α × Nat) :=
  ReferencedBy.all s α |>.findSome? fun r =>
    let n := ReferencedBy.count r st id
    if n == 0 then none else some (r, n)

def replaceRow {s α} [IsSchema s] [Entity α]
    (st : DbState s) (id : Id α) (v : α) : DbState s :=
  let tbl := DbState.get (α := α) st
  st.set { tbl with rows := tbl.rows.map fun r => if r.id == id then ⟨id, v⟩ else r }

def removeRow {s α} [IsSchema s] [Entity α] (st : DbState s) (id : Id α) : DbState s :=
  let tbl := DbState.get (α := α) st
  st.set { tbl with rows := tbl.rows.filter (fun r => !(r.id == id)) }

def assign {s α} [IsSchema s] [Entity α] (st : DbState s) (v : α) :
    Stored α × DbState s :=
  let tbl := DbState.get (α := α) st
  let id : Id α := ⟨Int64.ofNat tbl.next⟩
  let row : Stored α := ⟨id, v⟩
  (row, st.set { next := tbl.next + 1, rows := tbl.rows ++ [row] })

/-- Inner interpreter; `st0` is the state at the start of the program (abort). -/
def denote.go {σ s ε : Type} [IsSchema s] (st0 : DbState s) :
    {α : Type} → Txn σ s ε α → DbState s → Except ε α × DbState s
  | _, .pure a, st => (.ok a, st)
  | _, .bind m f, st =>
      match denote.go st0 m st with
      | (.error e, st') => (.error e, st')
      | (.ok a, st') => denote.go st0 (f a) st'
  | _, .liftRead r, st => (.ok (Read.denote (s := s) r st), st)
  | _, @Txn.get _ _ _ α _inst id, st =>
      let found := (DbState.get (α := α) st).rows.find? (·.id == id)
      (.ok (found.map fun row => ⟨row⟩), st)
  | _, @Txn.lookup _ _ _ α instE instU ix key, st =>
      let found := Read.lookupDenote (s := s) st instE instU ix key
      (.ok (found.map fun row => ⟨row⟩), st)
  | _, .throw e, _ => (.error e, st0)
  | _, .orAbort m f, st =>
      match denote.go st0 m st with
      | (.error e, st') => (.error e, st')
      | (.ok (.error err), _) => (.error (f err), st0)
      | (.ok (.ok a), st') => (.ok a, st')
  | _, .orElse m g, st =>
      match denote.go st0 m st with
      | (.error e, st') => (.error e, st')
      | (.ok (.error err), st') => denote.go st0 (g err) st'
      | (.ok (.ok a), st') => (.ok a, st')
  | _, @Txn.insert _ _ _ α _ _ _ v, st =>
      match firstDuplicate v.val st none with
      | some (ix, holder) => (.ok (.error (.duplicate ix holder)), st)
      | none =>
          match firstMissingRef v.val st with
          | some fk => (.ok (.error (.missingRef fk)), st)
          | none =>
              let (row, st') := assign st v.val
              (.ok (.ok ⟨row⟩), st')
  | _, @Txn.update _ _ _ α _ _ _ old new, st =>
      match (DbState.get (α := α) st).rows.find? (·.id == old.id) with
      | none => (.ok (.error .gone), st)
      | some cur =>
          if !parentEq cur.val old.val then
            (.ok (.error (.stale cur)), st)
          else
            match firstDuplicate new.val st (some old.id) with
            | some (ix, holder) => (.ok (.error (.duplicate ix holder)), st)
            | none =>
                match firstMissingRef new.val st with
                | some fk => (.ok (.error (.missingRef fk)), st)
                | none =>
                    let st' := replaceRow st old.id new.val
                    (.ok (.ok ⟨old.id, new.val⟩), st')
  | _, @Txn.set _ _ _ α _ _ _ row new, st =>
      match (DbState.get (α := α) st).rows.find? (·.id == row.id) with
      | none => (.ok (.error .gone), st)
      | some _ =>
          match firstDuplicateTouching (Fields.all α) new.val st (some row.id) with
          | some (ix, holder) => (.ok (.error (.duplicate ix holder)), st)
          | none =>
              match firstMissingWithin (Fields.all α) new.val st with
              | some fk => (.ok (.error (.missingRef fk)), st)
              | none =>
                  let st' := replaceRow st row.id new.val
                  (.ok (.ok ⟨⟨row.id, new.val⟩⟩), st')
  | _, @Txn.patch _ _ _ α _ _ _ row fs new, st =>
      match (DbState.get (α := α) st).rows.find? (·.id == row.id) with
      | none => (.ok (.error .gone), st)
      | some _ =>
          match firstDuplicateTouching fs new.val st (some row.id) with
          | some (ix, holder) => (.ok (.error (.duplicate ix holder)), st)
          | none =>
              match firstMissingWithin fs new.val st with
              | some fk => (.ok (.error (.missingRef fk)), st)
              | none =>
                  let st' := replaceRow st row.id new.val
                  (.ok (.ok ⟨⟨row.id, new.val⟩⟩), st')
  | _, @Txn.append _ _ _ α _ _ old new, st =>
      match (DbState.get (α := α) st).rows.find? (·.id == old.id) with
      | none => (.ok (.error .gone), st)
      | some cur =>
          if !parentEq cur.val old.val || listsMoved cur.val old.val then
            (.ok (.error (.stale cur)), st)
          else
            match firstNotAppend old.val new.val with
            | some lf => (.ok (.error (.notAppend lf)), st)
            | none =>
                let st' := replaceRow st old.id new.val
                (.ok (.ok ⟨old.id, new.val⟩), st')
  | _, @Txn.delete _ _ _ α _ _ id, st =>
      match (DbState.get (α := α) st).rows.find? (·.id == id) with
      | none => (.ok (.error .gone), st)
      | some row =>
          match firstRestricted st id with
          | some (who, n) => (.ok (.error (.restricted who n)), st)
          | none => (.ok (.ok row), removeRow st id)

/-- Pure meaning. An abort (`throw` / `orAbort`) returns the original state. -/
def denote {σ s ε α : Type} [IsSchema s] (p : Txn σ s ε α) (st : DbState s) :
    Except ε α × DbState s :=
  denote.go (σ := σ) (s := s) (ε := ε) st p st

end Txn

end LeanDb
