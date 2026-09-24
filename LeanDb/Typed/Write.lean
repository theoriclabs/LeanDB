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

/-- Re-attach `old`'s child lists onto a parent decoded from columns. -/
def Fields.withOldChildren {α} [Entity α] (old v : α) : α :=
  (Entity.children (α := α)).foldl (init := v) fun acc link =>
    let pairs := (link.rows old).zipIdx.map fun (cols, i) => (i, cols)
    match link.attach pairs acc with
    | .ok a => a
    | .error _ => acc

/-- The stored row after a `patch`: `old` with only columns in `fs` taken
    from `new`. Child lists stay `old`'s — they are not `Entity.Field`s,
    so `patch` cannot name them (`append` / `set`).

    The merged row is `Checked` when `old` is well-formed and `new` is
    `Checked`, for any invariant that does not mix a written field with
    an unwritten one (the usual case: `User.invariant` is `name ≠ ""`,
    and a patch of `email` keeps `name`). Callers pass a `Checked α` of
    the intended full row; only `fs` is written, so a different value in
    a non-written field of `new` does not land in the database. -/
def Fields.apply {α} [Entity α] (fs : Fields α) (old new : α) : α :=
  let oldC := Entity.encode old
  let newC := Entity.encode new
  let fields := Entity.fields (α := α)
  if oldC.size != newC.size || oldC.size != fields.size then
    old
  else
    let merged := Id.run do
      let mut out : Array Col := Array.mkEmpty oldC.size
      for i in [0:fields.size] do
        match fields[i]?, oldC[i]?, newC[i]? with
        | some f, some o, some n =>
            out := out.push (if fs.mem f then n else o)
        | _, _, _ => pure ()
      return out
    match Entity.decode merged with
    | .error _ => old
    | .ok v => Fields.withOldChildren old v

/-- Engine `Patch` that `UPDATE`s only the columns in `fs`. -/
def Fields.toEnginePatch {α} [Entity α] (fs : Fields α) (v : α) : Patch α :=
  ⟨(Entity.fields (α := α)).filterMap fun f =>
      if fs.mem f then some (Assignment.of f (Entity.get f v)) else Option.none⟩

/-! ## Constraints restricted to written fields -/

/-- Whether unique index `ix` names a column in `fs`. -/
@[reducible] def Unique.touches {α : Type} [Entity α] [HasUnique α]
    (ix : Unique α) (fs : Fields α) : Bool :=
  (Unique.fieldSyms ix).toList.any fs.mem

/-- Whether any unique index overlaps `fs`. Reduces on concrete `fs`, so
    `Unique.Touching fs` becomes `Empty` when none do. -/
@[reducible] def Unique.anyTouch {α : Type} [Entity α] [HasUnique α]
    (fs : Fields α) : Bool :=
  (Unique.all α).toList.any (Unique.touches · fs)

/-- Unique indexes that overlap the written fields `fs`. `Empty` (not a
    subtype of `Unique α`) when no declared index names a field of `fs`,
    so `SetError.duplicate` is omitted from an exhaustive match. -/
@[reducible] def Unique.Touching {α : Type} [Entity α] [HasUnique α]
    (fs : Fields α) : Type :=
  if Unique.anyTouch (α := α) fs then
    { ix : Unique α // Unique.touches ix fs = true }
  else
    Empty

def Unique.Touching.ix {α : Type} [Entity α] [HasUnique α] {fs : Fields α}
    (t : Unique.Touching fs) : Unique α :=
  if hAny : Unique.anyTouch (α := α) fs then
    (cast (by simp [Unique.Touching, hAny]) t : { ix : Unique α // Unique.touches ix fs = true }).1
  else
    nomatch (cast (by simp [Unique.Touching, hAny]) t : Empty)

def Unique.toTouching {α : Type} [Entity α] [HasUnique α] {fs : Fields α}
    (ix : Unique α) (h : Unique.touches ix fs = true)
    (hAny : Unique.anyTouch (α := α) fs = true) : Unique.Touching fs :=
  cast (by simp [Unique.Touching, hAny])
    (⟨ix, h⟩ : { ix : Unique α // Unique.touches ix fs = true })

instance {α : Type} [Entity α] [hu : HasUnique α] [IsEmpty hu.Unique] (fs : Fields α) :
    IsEmpty (@Unique.Touching α _ hu fs) where
  false t :=
    if hAny : Unique.anyTouch (α := α) fs then
      IsEmpty.false
        (cast (by simp [Unique.Touching, hAny]) t :
          { ix : Unique α // Unique.touches ix fs = true }).1
    else
      nomatch (cast (by simp [Unique.Touching, hAny]) t : Empty)

/-- Whether foreign key `fk` is among the written fields. -/
@[reducible] def ForeignKey.within {α : Type} [Entity α] [HasForeignKey α]
    (fk : ForeignKey α) (fs : Fields α) : Bool :=
  fs.mem (ForeignKey.field fk)

/-- Whether any foreign key is among `fs`. -/
@[reducible] def ForeignKey.anyWithin {α : Type} [Entity α] [HasForeignKey α]
    (fs : Fields α) : Bool :=
  (ForeignKey.all α).toList.any (ForeignKey.within · fs)

/-- Foreign keys among the written fields `fs`. `Empty` when there is no
    `Ref`, or none of the written fields is a `Ref`, so `missingRef` is
    omitted from an exhaustive match (`IsEmpty` is found). -/
@[reducible] def ForeignKey.Within {α : Type} [Entity α] [HasForeignKey α]
    (fs : Fields α) : Type :=
  if ForeignKey.anyWithin (α := α) fs then
    { fk : ForeignKey α // ForeignKey.within fk fs = true }
  else
    Empty

def ForeignKey.Within.fk {α : Type} [Entity α] [HasForeignKey α] {fs : Fields α}
    (w : ForeignKey.Within fs) : ForeignKey α :=
  if hAny : ForeignKey.anyWithin (α := α) fs then
    (cast (by simp [ForeignKey.Within, hAny]) w :
      { fk : ForeignKey α // ForeignKey.within fk fs = true }).1
  else
    nomatch (cast (by simp [ForeignKey.Within, hAny]) w : Empty)

def ForeignKey.toWithin {α : Type} [Entity α] [HasForeignKey α] {fs : Fields α}
    (fk : ForeignKey α) (h : ForeignKey.within fk fs = true)
    (hAny : ForeignKey.anyWithin (α := α) fs = true) : ForeignKey.Within fs :=
  cast (by simp [ForeignKey.Within, hAny])
    (⟨fk, h⟩ : { fk : ForeignKey α // ForeignKey.within fk fs = true })

instance {α : Type} [Entity α] [hf : HasForeignKey α] [IsEmpty hf.ForeignKey]
    (fs : Fields α) : IsEmpty (@ForeignKey.Within α _ hf fs) where
  false w :=
    if hAny : ForeignKey.anyWithin (α := α) fs then
      IsEmpty.false
        (cast (by simp [ForeignKey.Within, hAny]) w :
          { fk : ForeignKey α // ForeignKey.within fk fs = true }).1
    else
      nomatch (cast (by simp [ForeignKey.Within, hAny]) w : Empty)

/-! ## Inbound reference counts (for `DeleteError.restricted`) -/

def ReferencedBy.count {s α : Type} [IsSchema s] [h : HasReferencedBy s α]
    (r : ReferencedBy s α) (st : DbState s) (id : Id α) : Nat :=
  let inst := h.sourceEntity r
  let tbl := DbState.getSource (s := s) (α := α) st r
  (@Table.rows (h.Source r) inst tbl).foldl (init := 0) fun n row =>
    match h.getFk r (@Valid.val (h.Source r) inst row) with
    | some tgt => if tgt.toInt64 == id.toInt64 then n + 1 else n
    | none => n

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

/-- Failures of `append` (child lists must grow). Unique and foreign-key
    constraints on the parent's columns are checked: `append` writes
    those columns under the same CAS as `update`. -/
inductive AppendError (α : Type) [Entity α] [HasListField α]
    [HasUnique α] [HasForeignKey α] where
  | stale (current : Stored α)
  | gone
  | notAppend (list : ListField α)
  | duplicate (ix : Unique α) (holder : Id α)
  | missingRef (fk : ForeignKey α)

/-- Failures of `delete`. `restricted` names who still references the
    row, and how many such rows. -/
inductive DeleteError (s : Type) (α : Type) [IsSchema s]
    [Entity α] [HasReferencedBy s α] where
  | gone
  | restricted (who : ReferencedBy.Restricting s α) (rows : Nat)

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

instance {s α : Type} [IsSchema s] [Entity α] [HasReferencedBy s α]
    [BEq (ReferencedBy s α)] : BEq (DeleteError s α) where
  beq
    | .gone, .gone => true
    | .restricted b1 n1, .restricted b2 n2 =>
        ReferencedBy.Restricting.val b1 == ReferencedBy.Restricting.val b2 && n1 == n2
    | _, _ => false

instance {s α : Type} [IsSchema s] [Entity α] [HasReferencedBy s α]
    [Repr (ReferencedBy s α)] : Repr (DeleteError s α) where
  reprPrec
    | .gone, _ => "DeleteError.gone"
    | .restricted b n, _ =>
        Std.Format.bracket "DeleteError.restricted ("
          (repr (ReferencedBy.Restricting.val b) ++ ", " ++ repr n) ")"

instance {α : Type} [Entity α] [HasListField α] [HasUnique α] [HasForeignKey α]
    [BEq α] [BEq (ListField α)] [BEq (Unique α)] [BEq (ForeignKey α)] :
    BEq (AppendError α) where
  beq
    | .gone, .gone => true
    | .notAppend a, .notAppend b => a == b
    | .stale c1, .stale c2 => c1.id == c2.id && c1.val == c2.val
    | .duplicate i1 h1, .duplicate i2 h2 => i1 == i2 && h1 == h2
    | .missingRef f1, .missingRef f2 => f1 == f2
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
