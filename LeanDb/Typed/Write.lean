import LeanDb.Typed.State

/-! # Typed write failures (M14b)

Each write's error type is derived from the schema: which unique index
clashed, which reference is missing, who still references the row, and
the current row when a compare-and-swap loses. Failures that cannot
happen are uninhabited (`Unique α := Empty` when there is no index), and
`IsEmpty` is found automatically.
-/

namespace LeanDb

/-! ## Written fields -/

/-- A set of field symbols of `α`. `patch` records the written fields in
    `SetError α fs`, so only indexes and references that overlap `fs`
    appear in the type. -/
structure Fields (α : Type) [Entity α] where
  mem : Entity.Field α → Bool

@[reducible] def Fields.all (α : Type) [Entity α] : Fields α := ⟨fun _ => true⟩

@[reducible] def Fields.none (α : Type) [Entity α] : Fields α := ⟨fun _ => false⟩

@[reducible] def Fields.of {α : Type} [Entity α] [DecidableEq (Entity.Field α)]
    (fs : List (Entity.Field α)) : Fields α :=
  ⟨fun f => fs.contains f⟩

@[reducible] def Fields.singleton {α : Type} [Entity α] [DecidableEq (Entity.Field α)]
    (f : Entity.Field α) : Fields α :=
  Fields.of [f]

/-! ## Constraints restricted to written fields -/

/-- Whether unique index `ix` names a column in `fs`. -/
def Unique.touches {α : Type} [Entity α] [HasUnique α]
    (ix : Unique α) (fs : Fields α) : Bool :=
  (Unique.columns ix).any fun col =>
    match Entity.fieldOfName? α col with
    | some f => fs.mem f
    | none => false

/-- Unique indexes that overlap the written fields `fs`. Uninhabited when
    `Unique α` is empty, or when no declared index names a field of `fs`,
    so `duplicate` cannot be built. -/
def Unique.Touching {α : Type} [Entity α] [HasUnique α] (fs : Fields α) : Type :=
  { ix : Unique α // Unique.touches ix fs = true }

def Unique.Touching.ix {α : Type} [Entity α] [HasUnique α] {fs : Fields α}
    (t : Unique.Touching fs) : Unique α :=
  t.1

def Unique.toTouching {α : Type} [Entity α] [HasUnique α] {fs : Fields α}
    (ix : Unique α) (h : Unique.touches ix fs = true) : Unique.Touching fs :=
  ⟨ix, h⟩

instance {α : Type} [Entity α] [hu : HasUnique α] [IsEmpty hu.Unique] (fs : Fields α) :
    IsEmpty (@Unique.Touching α _ hu fs) where
  false t := IsEmpty.false t.1

/-- Whether foreign key `fk` is among the written fields. -/
def ForeignKey.within {α : Type} [Entity α] [HasForeignKey α]
    (fk : ForeignKey α) (fs : Fields α) : Bool :=
  fs.mem (ForeignKey.field fk)

/-- Foreign keys among the written fields `fs`. Uninhabited when there is
    no `Ref`, or none of the written fields is a `Ref`. -/
def ForeignKey.Within {α : Type} [Entity α] [HasForeignKey α] (fs : Fields α) : Type :=
  { fk : ForeignKey α // ForeignKey.within fk fs = true }

def ForeignKey.Within.fk {α : Type} [Entity α] [HasForeignKey α] {fs : Fields α}
    (w : ForeignKey.Within fs) : ForeignKey α :=
  w.1

def ForeignKey.toWithin {α : Type} [Entity α] [HasForeignKey α] {fs : Fields α}
    (fk : ForeignKey α) (h : ForeignKey.within fk fs = true) : ForeignKey.Within fs :=
  ⟨fk, h⟩

instance {α : Type} [Entity α] [hf : HasForeignKey α] [IsEmpty hf.ForeignKey]
    (fs : Fields α) : IsEmpty (@ForeignKey.Within α _ hf fs) where
  false w := IsEmpty.false w.1

/-! ## Inbound reference counts (for `DeleteError.restricted`) -/

def ReferencedBy.count {s α : Type} [IsSchema s] [h : HasReferencedBy s α]
    (r : ReferencedBy s α) (st : DbState s) (id : Id α) : Nat :=
  let inst := h.sourceEntity r
  let tbl := @DbState.get s (h.Source r) inferInstance inst st
  tbl.rows.foldl (init := 0) fun n row =>
    if (h.getFk r row.val).toInt64 == id.toInt64 then n + 1 else n

/-! ## Failure types -/

/-- Failures of `insert`. `duplicate` is uninhabited without a unique
    index; `missingRef` without a `Ref` field. -/
inductive InsertError (α : Type) [Entity α] [HasUnique α] [HasForeignKey α] where
  | duplicate (ix : Unique α) (holder : Id α)
  | missingRef (fk : ForeignKey α)

/-- Failures of compare-and-swap `update` on a row read before this
    transaction. -/
inductive UpdateError (α : Type) [Entity α] [HasUnique α] [HasForeignKey α] where
  | stale (current : Stored α)
  | gone
  | duplicate (ix : Unique α) (holder : Id α)
  | missingRef (fk : ForeignKey α)

/-- Failures of writing the fields `fs` of a row read in this
    transaction. No `stale`: nothing else can change the row before the
    transaction ends. `duplicate` / `missingRef` only for constraints
    over written fields. -/
inductive SetError (α : Type) [Entity α] [HasUnique α] [HasForeignKey α]
    (fs : Fields α) where
  | gone
  | duplicate (ix : Unique.Touching fs) (holder : Id α)
  | missingRef (fk : ForeignKey.Within fs)

/-- Failures of `append` (child lists must grow). -/
inductive AppendError (α : Type) [Entity α] [HasListField α] where
  | stale (current : Stored α)
  | gone
  | notAppend (list : ListField α)

/-- Failures of `delete`. `restricted` names who still references the
    row, and how many such rows. -/
inductive DeleteError (s : Type) (α : Type) [Entity α] [HasReferencedBy s α] where
  | gone
  | restricted (who : ReferencedBy s α) (rows : Nat)

instance {α : Type} [Entity α] [hu : HasUnique α] [hf : HasForeignKey α]
    [IsEmpty hu.Unique] [IsEmpty hf.ForeignKey] : IsEmpty (@InsertError α _ hu hf) where
  false
    | .duplicate ix _ => IsEmpty.false ix
    | .missingRef fk => IsEmpty.false fk

/-- `insertNew` needs this instance; the `Txn` combinator is defined with
    the program type. -/
theorem InsertError.isEmpty {α : Type} [Entity α] [HasUnique α] [HasForeignKey α]
    [IsEmpty (InsertError α)] (e : InsertError α) : False :=
  IsEmpty.false e

/-! ## `BEq` / `Repr` for constructors the harness compares -/

instance {α : Type} [Entity α] [HasUnique α] [HasForeignKey α]
    [BEq (Unique α)] [BEq (ForeignKey α)] : BEq (InsertError α) where
  beq
    | .duplicate i1 h1, .duplicate i2 h2 => i1 == i2 && h1 == h2
    | .missingRef f1, .missingRef f2 => f1 == f2
    | _, _ => false

instance {α : Type} [Entity α] [HasUnique α] [HasForeignKey α]
    [Repr (Unique α)] [Repr (ForeignKey α)] : Repr (InsertError α) where
  reprPrec
    | .duplicate ix holder, _ =>
        Std.Format.bracket "InsertError.duplicate ("
          (repr ix ++ ", Id " ++ repr holder.toInt64) ")"
    | .missingRef fk, _ =>
        Std.Format.bracket "InsertError.missingRef (" (repr fk) ")"

instance {s α : Type} [Entity α] [HasReferencedBy s α]
    [BEq (ReferencedBy s α)] : BEq (DeleteError s α) where
  beq
    | .gone, .gone => true
    | .restricted b1 n1, .restricted b2 n2 => b1 == b2 && n1 == n2
    | _, _ => false

instance {s α : Type} [Entity α] [HasReferencedBy s α]
    [Repr (ReferencedBy s α)] : Repr (DeleteError s α) where
  reprPrec
    | .gone, _ => "DeleteError.gone"
    | .restricted b n, _ =>
        Std.Format.bracket "DeleteError.restricted (" (repr b ++ ", " ++ repr n) ")"

instance {α : Type} [Entity α] [HasListField α] [BEq (ListField α)] :
    BEq (AppendError α) where
  beq
    | .gone, .gone => true
    | .notAppend a, .notAppend b => a == b
    | .stale c1, .stale c2 => c1.id == c2.id
    | _, _ => false

instance {α : Type} [Entity α] [HasUnique α] [HasForeignKey α]
    [BEq (Unique α)] [BEq (ForeignKey α)] : BEq (UpdateError α) where
  beq
    | .gone, .gone => true
    | .stale c1, .stale c2 => c1.id == c2.id
    | .duplicate i1 h1, .duplicate i2 h2 => i1 == i2 && h1 == h2
    | .missingRef f1, .missingRef f2 => f1 == f2
    | _, _ => false

instance {α : Type} [Entity α] [HasUnique α] [HasForeignKey α] {fs : Fields α}
    [BEq (Unique α)] [BEq (ForeignKey α)] : BEq (SetError α fs) where
  beq
    | .gone, .gone => true
    | .duplicate i1 h1, .duplicate i2 h2 => i1.ix == i2.ix && h1 == h2
    | .missingRef f1, .missingRef f2 => f1.fk == f2.fk
    | _, _ => false

end LeanDb
