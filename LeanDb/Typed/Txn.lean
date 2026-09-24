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
  /-- Write only the columns in `fs`. `new` supplies those columns (it is
      a full `Checked` row); the stored row is `Fields.apply fs old new.val`,
      so a different value of a non-written field in `new` is discarded.
      The merged row stays `Checked` for invariants that do not mix
      written and unwritten fields — callers typically build `new` as
      `{old with f := v}`, which makes merge equal `new`. -/
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
      | some cur =>
          let merged := Fields.apply fs cur.val new.val
          match firstDuplicateTouching fs merged st (some row.id) with
          | some (ix, holder) => (.ok (.error (.duplicate ix holder)), st)
          | none =>
              match firstMissingWithin fs merged st with
              | some fk => (.ok (.error (.missingRef fk)), st)
              | none =>
                  let st' := replaceRow st row.id merged
                  (.ok (.ok ⟨⟨row.id, merged⟩⟩), st')
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

/-! ## Execution -/

def firstDuplicateDb {α} [Entity α] [HasUnique α]
    (v : α) (except : Option (Id α)) : Db (Option (Unique α × Id α)) :=
  Unique.all α |>.foldlM (m := Db) (init := none) fun acc ix => do
    match acc with
    | some _ => return acc
    | none =>
        let rows ← selectP (ts := [α]) (Unique.predOf ix (Unique.keyOf ix v))
        match rows.find? (fun r => !(except == some r.id)) with
        | none => return none
        | some r => return some (ix, r.id)

def fkExistsDb {α} [Entity α] [hf : HasForeignKey α] (fk : hf.ForeignKey) (v : α) : Db Bool := do
  let tgt := hf.get fk v
  let inst := hf.targetEntity fk
  let row ← @LeanDb.get (hf.Target fk) inst tgt
  return row.isSome

def firstMissingRefDb {α} [Entity α] [HasForeignKey α] (v : α) :
    Db (Option (ForeignKey α)) :=
  ForeignKey.all α |>.foldlM (m := Db) (init := none) fun acc fk => do
    match acc with
    | some _ => return acc
    | none =>
        if ← fkExistsDb fk v then return none else return some fk

def firstDuplicateTouchingDb {α} [Entity α] [HasUnique α]
    (fs : Fields α) (v : α) (except : Option (Id α)) :
    Db (Option (Unique.Touching fs × Id α)) :=
  Unique.all α |>.foldlM (m := Db) (init := none) fun acc ix => do
    match acc with
    | some _ => return acc
    | none =>
        if h : Unique.touches ix fs then
          let rows ← selectP (ts := [α]) (Unique.predOf ix (Unique.keyOf ix v))
          match rows.find? (fun r => !(except == some r.id)) with
          | none => return none
          | some r => return some (Unique.toTouching ix h, r.id)
        else
          return none

def firstMissingWithinDb {α} [Entity α] [HasForeignKey α]
    (fs : Fields α) (v : α) : Db (Option (ForeignKey.Within fs)) :=
  ForeignKey.all α |>.foldlM (m := Db) (init := none) fun acc fk => do
    match acc with
    | some _ => return acc
    | none =>
        if h : ForeignKey.within fk fs then
          if ← fkExistsDb fk v then return none
          else return some (ForeignKey.toWithin fk h)
        else
          return none

def countRefsDb {s α} [HasReferencedBy s α] (r : ReferencedBy s α) (id : Id α) : Db Nat :=
  untrackedSqlite fun db => do
    let sql :=
      s!"SELECT COUNT(*) FROM {quoteIdent (ReferencedBy.sourceName r)} WHERE {quoteIdent (ReferencedBy.columnName r)} = ?"
    let stmt ← db.prepare sql
    stmt.bindInt64 1 id.toInt64
    if ← stmt.step then
      return (← stmt.columnInt64 0).toNatClampNeg
    else return 0

def firstRestrictedDb {s α} [HasReferencedBy s α] (id : Id α) :
    Db (Option (ReferencedBy s α × Nat)) :=
  ReferencedBy.all s α |>.foldlM (m := Db) (init := none) fun acc r => do
    match acc with
    | some _ => return acc
    | none =>
        let n ← countRefsDb r id
        if n == 0 then return none else return some (r, n)

def insertExec {σ α} [Entity α] [HasUnique α] [HasForeignKey α]
    (v : Checked α) : Db (Except (InsertError α) (Current σ α)) :=
  withTransaction do
    match ← firstDuplicateDb v.val none with
    | some (ix, holder) => return .error (.duplicate ix holder)
    | none =>
        match ← firstMissingRefDb v.val with
        | some fk => return .error (.missingRef fk)
        | none =>
            let row ← LeanDb.insert α v.val
            return .ok ⟨row⟩

def updateExec {α} [Entity α] [HasUnique α] [HasForeignKey α]
    (old : Stored α) (new : Checked α) : Db (Except (UpdateError α) (Stored α)) :=
  withTransaction do
    match ← LeanDb.get old.id with
    | none => return .error .gone
    | some cur =>
        if !parentEq cur.val old.val then
          return .error (.stale cur)
        match ← firstDuplicateDb new.val (some old.id) with
        | some (ix, holder) => return .error (.duplicate ix holder)
        | none =>
            match ← firstMissingRefDb new.val with
            | some fk => return .error (.missingRef fk)
            | none =>
                let row ← LeanDb.update old new.val
                return .ok row

def setExec {σ α} [Entity α] [HasUnique α] [HasForeignKey α]
    (row : Current σ α) (fs : Fields α) (new : Checked α) :
    Db (Except (SetError α fs) (Current σ α)) :=
  withTransaction do
    match ← LeanDb.get row.id with
    | none => return .error .gone
    | some cur =>
        match ← firstDuplicateTouchingDb fs new.val (some row.id) with
        | some (ix, holder) => return .error (.duplicate ix holder)
        | none =>
            match ← firstMissingWithinDb fs new.val with
            | some fk => return .error (.missingRef fk)
            | none =>
                let written ← LeanDb.update cur new.val
                return .ok ⟨written⟩

/-- `patch`: merge `fs` into the stored row and `UPDATE` only those columns. -/
def patchExec {σ α} [Entity α] [HasUnique α] [HasForeignKey α]
    (row : Current σ α) (fs : Fields α) (new : Checked α) :
    Db (Except (SetError α fs) (Current σ α)) :=
  withTransaction do
    match ← LeanDb.get row.id with
    | none => return .error .gone
    | some cur =>
        let merged := Fields.apply fs cur.val new.val
        match ← firstDuplicateTouchingDb fs merged (some row.id) with
        | some (ix, holder) => return .error (.duplicate ix holder)
        | none =>
            match ← firstMissingWithinDb fs merged with
            | some fk => return .error (.missingRef fk)
            | none =>
                match ← LeanDb.patch cur.id (Fields.toEnginePatch fs merged) with
                | .notFound => return .error .gone
                | .guardFailed => return .error .gone
                | .updated =>
                    match ← LeanDb.get row.id with
                    | none => return .error .gone
                    | some written => return .ok ⟨written⟩

def appendExec {α} [Entity α] [HasListField α]
    (old : Stored α) (new : Checked α) : Db (Except (AppendError α) (Stored α)) :=
  withTransaction do
    match ← LeanDb.get old.id with
    | none => return .error .gone
    | some cur =>
        if !parentEq cur.val old.val || listsMoved cur.val old.val then
          return .error (.stale cur)
        match firstNotAppend old.val new.val with
        | some lf => return .error (.notAppend lf)
        | none =>
            let row ← LeanDb.append old new.val
            return .ok row

def deleteExec {s α} [Entity α] [HasReferencedBy s α] (id : Id α) :
    Db (Except (DeleteError s α) (Stored α)) :=
  withTransaction do
    match ← LeanDb.get id with
    | none => return .error .gone
    | some row =>
        match ← firstRestrictedDb (s := s) id with
        | some (who, n) => return .error (.restricted who n)
        | none =>
            LeanDb.delete id
            return .ok row

def exec.go {σ s ε : Type} [IsSchema s] :
    {α : Type} → Txn σ s ε α → Db (Except ε α)
  | _, .pure a => (Pure.pure (f := Db) (Except.ok a))
  | _, .bind m f => do
      match ← exec.go m with
      | .error e => return Except.error e
      | .ok a => exec.go (f a)
  | _, .liftRead r => Except.ok <$> Read.exec (s := s) r
  | _, @Txn.get _ _ _ α _ id => do
      let found ← LeanDb.get id
      return Except.ok (found.map fun row => ⟨row⟩)
  | _, @Txn.lookup _ _ _ α instE instU ix key => do
      let rows ← selectP (ts := [α]) (@Unique.predOf α instE instU ix key)
      return Except.ok (rows[0]?.map fun row => ⟨row⟩)
  | _, .throw e => (Pure.pure (f := Db) (Except.error e))
  | _, .orAbort m f => do
      match ← exec.go m with
      | .error e => return Except.error e
      | .ok (.error err) => return Except.error (f err)
      | .ok (.ok a) => return Except.ok a
  | _, .orElse m g => do
      match ← exec.go m with
      | .error e => return Except.error e
      | .ok (.error err) => exec.go (g err)
      | .ok (.ok a) => return Except.ok a
  | _, @Txn.insert _ _ _ α _ _ _ v => Except.ok <$> insertExec (σ := σ) v
  | _, @Txn.update _ _ _ α _ _ _ old new => Except.ok <$> updateExec old new
  | _, @Txn.set _ _ _ α _ _ _ row new =>
      Except.ok <$> setExec (σ := σ) row (Fields.all α) new
  | _, @Txn.patch _ _ _ α _ _ _ row fs new =>
      Except.ok <$> patchExec (σ := σ) row fs new
  | _, @Txn.append _ _ _ α _ _ old new => Except.ok <$> appendExec old new
  | _, @Txn.delete _ _ _ α _ _ id => Except.ok <$> deleteExec (s := s) id

/-- `BEGIN IMMEDIATE`; a SAVEPOINT around each write. Domain abort rolls
    back. Infrastructure problems are `DbFault`, not `ε`. -/
def run {s ε α} [IsSchema s] (p : {σ : Type} → Txn σ s ε α) :
    Db (Except DbFault (Except ε α)) :=
  fun conn => ExceptT.mk do
    let body : DbM (Tx ε α) := do
      match ← exec.go (σ := Unit) (s := s) (ε := ε) (p (σ := Unit)) with
      | .ok a => return Tx.commit a
      | .error e => return Tx.abort e
    match ← (LeanDb.transaction body conn).run with
    | .ok r => return .ok (.ok r)
    | .error e => return .ok (.error (DbFault.ofDbError e))

end Txn

end LeanDb
