import LeanDb.Typed.Txn
import LeanDb.Typed.Laws

namespace LeanDb

/-- Transaction-bound native relation handle. Its constructor is private;
    binding requires a parent observed in this same transaction. -/
structure MemberHandle (σ p t e : Type) [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e] where
  private mk ::
  relation : MemberRelation p t e
  parent : Id p

def MemberRelation.bind {σ p t e} [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e] (relation : MemberRelation p t e)
    (parent : Current σ p) : MemberHandle σ p t e := ⟨relation, parent.id⟩

/-- An include removes only the generated exact pair duplicate alternative.
    It never suppresses missing references or an infrastructure exception.
    `Txn.insert` checks/inserts under the enclosing admitted writer transaction. -/
def Txn.includeMember {σ s ε p t e} [IsSchema s] [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e] [IsSchema.Has s e]
    (handle : MemberHandle σ p t e) (target : Id t) :
    Txn σ s ε (Except (ForeignKey e) Unit) := do
  match ← Txn.insert e (handle.relation.row handle.parent target) with
  | .ok _ => return .ok ()
  | .error (.duplicate ix _) =>
      -- The descriptor proves there are no unrelated unique alternatives.
      have _exactPair := handle.relation.onlyPair ix
      return .ok ()
  | .error (.missingRef fk) => return .error fk

def MemberHandle.contains {σ s ε p t e} [IsSchema s] [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e] [IsSchema.Has s e]
    (handle : MemberHandle σ p t e) (target : Id t) : Txn σ s ε Bool :=
  Txn.ofRead (.memberContains handle.relation handle.parent target)

/-- Protected native primitive: authorize first, then select one target column
    on the same transaction/snapshot. Use portable disclosure constructors. -/
def MemberHandle.discloseField {σ s ε p t e β} [IsSchema s]
    [Entity p] [Entity t] [Entity e] [HasUnique e] [HasForeignKey e]
    [IsSchema.Has s e] [IsSchema.Has s t]
    (handle : MemberHandle σ p t e) (policy : Txn σ s ε Bool)
    (field : Entity.Field t) (visible : List (Entity.fieldTy field) → β) (hidden : β) :
    Txn σ s ε β := do
  if ← policy then
    return visible (← Txn.ofRead (.memberField handle.relation handle.parent field))
  else return hidden

/-- A retry of an existing exact association succeeds and changes no table or
    counter. The only-pair evidence ties this premise to the generated key. -/
theorem Txn.includeMember_existing {σ s ε p t e} [IsSchema s]
    [Entity p] [Entity t] [Entity e] [HasUnique e] [HasForeignKey e] [IsSchema.Has s e]
    (handle : MemberHandle σ p t e) (target : Id t) (state : DbState s)
    (index : Unique e) (holder : Id e)
    (duplicate : Txn.firstDuplicate (handle.relation.row handle.parent target).val state none = some (index, holder)) :
    Txn.denote (ε := ε) (Txn.includeMember handle target) state = (.ok (.ok ()), state) := by
  simp [Txn.includeMember, Txn.denote, Txn.denote.go, duplicate, Bind.bind, Pure.pure]

private theorem MemberRelation.pairClash {p t e} [Entity p] [Entity t] [Entity e]
    [HasUnique e] [HasForeignKey e] (relation : MemberRelation p t e) (parent : Id p) (target : Id t) :
    Unique.keyClash (Unique.encodeKey relation.pairIndex
      (Unique.keyOf relation.pairIndex (relation.row parent target).val))
      (Unique.encodeKey relation.pairIndex (Unique.keyOf relation.pairIndex (relation.row parent target).val)) = true := by
  rw [relation.pairKey]
  simp [Unique.keyClash, BEq.beq, toCol, List.isEqv, LeanDb.instBEqCol.beq]

private theorem MemberRelation.duplicate_after_assign {s p t e} [IsSchema s]
    [Entity p] [Entity t] [Entity e] [HasUnique e] [HasForeignKey e] [IsSchema.Has s e]
    (relation : MemberRelation p t e) (parent : Id p) (target : Id t) (state : DbState s)
    (available : ¬ ((state.get (α := e)).next = 0 ∨ natSqlMax < (state.get (α := e)).next)) :
    (Txn.firstDuplicate (relation.row parent target).val
      (Txn.assign state (relation.row parent target)).2 none).isSome = true := by
  simp only [Txn.firstDuplicate, relation.pairAll, Array.findSome?_singleton]
  simp only [Txn.assign, available, dite_false, DbState.get_set_same]
  apply List.findSome?_isSome_iff.mpr
  refine ⟨Valid.ofChecked ⟨Int64.ofNat (state.get (α := e)).next⟩ (relation.row parent target), ?_, ?_⟩
  · simp
  · simp [Valid.ofChecked, Valid.val, Valid.id, MemberRelation.pairClash]

/-- Repeating an include has exactly the same answer and final state as one
    include, including missing references and counter exhaustion. This is a
    pure set law; it does not assume SQLite execution correspondence. -/
theorem Txn.includeMember_idempotent {σ s ε p t e} [IsSchema s]
    [Entity p] [Entity t] [Entity e] [HasUnique e] [HasForeignKey e] [IsSchema.Has s e]
    (handle : MemberHandle σ p t e) (target : Id t) (state : DbState s) :
    Txn.denote (ε := ε) (do
      let _ ← Txn.includeMember handle target
      Txn.includeMember handle target) state =
    Txn.denote (ε := ε) (Txn.includeMember handle target) state := by
  cases hd : Txn.firstDuplicate (handle.relation.row handle.parent target).val state none with
  | some pair =>
      rcases pair with ⟨index, holder⟩
      simp [Txn.includeMember, Txn.denote, Txn.denote.go, Bind.bind, Pure.pure, hd]
  | none =>
      cases hf : Txn.firstMissingRef (handle.relation.row handle.parent target).val state with
      | some fk =>
          simp [Txn.includeMember, Txn.denote, Txn.denote.go, Bind.bind, Pure.pure, hd, hf]
      | none =>
          by_cases unavailable : (state.get (α := e)).next = 0 ∨ natSqlMax < (state.get (α := e)).next
          · simp [Txn.includeMember, Txn.denote, Txn.denote.go, Bind.bind, Pure.pure, hd, hf,
              Txn.assign, unavailable]
          · have duplicate := handle.relation.duplicate_after_assign handle.parent target state unavailable
            cases nextDuplicate : Txn.firstDuplicate (handle.relation.row handle.parent target).val
                (Txn.assign state (handle.relation.row handle.parent target)).2 none with
            | none => simp [nextDuplicate] at duplicate
            | some pair =>
                rcases pair with ⟨index, holder⟩
                simp [Txn.includeMember, Txn.denote, Txn.denote.go, Bind.bind, Pure.pure, hd, hf, nextDuplicate]

/-- Includes inherit the genuine insert WF law, including unique/FK checks.
    Proof requires a lawful generated codec; no empty evidence is substituted. -/
theorem Txn.includeMember_wf {σ s ε p t e} [IsSchema s]
    [Entity p] [Entity t] [Entity e] [HasUnique e] [HasForeignKey e]
    [IsSchema.Has s e] [IsSchema.HasPack s e] [LawfulEntity e]
    (handle : MemberHandle σ p t e) (target : Id t) (state : DbState s) (wf : state.WF) :
    (Txn.denote (ε := ε) (Txn.includeMember handle target) state).2.WF := by
  have law := Txn.insert_wf (σ := σ) (ε := ε) (handle.relation.row handle.parent target) state wf
  cases hd : Txn.firstDuplicate (handle.relation.row handle.parent target).val state none with
  | some pair =>
      rcases pair with ⟨index, holder⟩
      simpa [Txn.includeMember, Txn.denote, Txn.denote.go, Bind.bind, Pure.pure, hd] using wf
  | none =>
      cases hf : Txn.firstMissingRef (handle.relation.row handle.parent target).val state with
      | some fk =>
          simpa [Txn.includeMember, Txn.denote, Txn.denote.go, Bind.bind, Pure.pure, hd, hf] using wf
      | none =>
          simpa [Txn.includeMember, Txn.denote, Txn.denote.go, Bind.bind, Pure.pure, hd, hf] using law

theorem Read.discloseWith_hidden {s α β} [IsSchema s] (policy : Read s Bool)
    (projection : Read s α) (visible : α → β) (hidden : β) (state : DbState s)
    (denied : Read.denote policy state = false) :
    Read.denote (Read.discloseWith policy projection visible hidden) state = hidden := by
  simp [Read.discloseWith, Read.denote, denied, Bind.bind, Pure.pure]

/-- Noninterference under the explicit permission release: denied viewers see
    the same payload-free constructor even when hidden associations differ. -/
theorem Read.discloseWith_denied_equal {s α β} [IsSchema s]
    (policy : Read s Bool) (projection : Read s α) (visible : α → β) (hidden : β)
    (a b : DbState s) (ha : Read.denote policy a = false) (hb : Read.denote policy b = false) :
    Read.denote (Read.discloseWith policy projection visible hidden) a =
      Read.denote (Read.discloseWith policy projection visible hidden) b := by
  rw [Read.discloseWith_hidden _ _ _ _ _ ha, Read.discloseWith_hidden _ _ _ _ _ hb]

/-- Every projected value comes from a stored target in this parent's exact
    member relation. The projection contains only the selected field value. -/
theorem Read.memberField_provenance {s p t e} [IsSchema s]
    [Entity p] [Entity t] [Entity e] [HasUnique e] [HasForeignKey e]
    [IsSchema.Has s e] [IsSchema.Has s t]
    (relation : MemberRelation p t e) (parent : Id p) (field : Entity.Field t)
    (state : DbState s) (value : Entity.fieldTy field)
    (present : value ∈ Read.denote (.memberField relation parent field) state) :
    ∃ row : Valid t, row ∈ (state.get (α := t)).rows ∧
      Read.memberContainsDenote relation parent row.id state = true ∧
      value = Entity.get field row.val := by
  change value ∈ _ at present
  rcases List.mem_map.mp present with ⟨row, member, equal⟩
  rcases List.mem_filter.mp member with ⟨stored, related⟩
  exact ⟨row, stored, related, equal.symm⟩

end LeanDb
