import LeanDb.Typed.Txn
import LeanDb.Typed.Laws

/-! # Ordinary link entities and named unique conflicts

A link can be an ordinary entity: a library's `Loan { book, member }`, with
a composite unique `(book, member)` and a reference that cascades when a book
is deleted. This module adds what the native layer needs for such entities,
next to the `members%` association (which stays):

- `Txn.insertUnique`: an insert whose failure type is exactly the declared
  unique alternatives (the native side of a portable `T.Conflict`). Missing
  references are not conflicts; they abort the transaction.
- `Read.linkField` (in `Read`): the typed semi-join projection, with the
  provenance law below.
- `Read.discloseIf` (in `Read`): proof-carrying disclosure. A denied read *is*
  `pure hidden`, so no statement is prepared.
-/

namespace LeanDb

/-- `Id`'s `BEq` compares the row number, so it decides equality. -/
theorem Id.eq_of_beq {α} : ∀ {a b : Id α}, (a == b) = true → a = b
  | ⟨x⟩, ⟨y⟩, h => by
    have h' : (x == y) = true := h
    rw [beq_iff_eq] at h'
    rw [h']

/-- Insert whose failure type is exactly the unique constraints declared for
    `α` (`unique% α.name := …`): one alternative per declaration, named after
    it, in declaration order, with no conflict holder. A missing reference is
    not a conflict: it aborts the transaction with `missingRef fk`, which
    rolls back every write (`Txn.denote_abort_restores`). Without a unique
    declaration `Unique α` is `Empty`. -/
def Txn.insertUnique {σ s ε α} [IsSchema s] [Entity α] [HasUnique α] [HasForeignKey α]
    [IsSchema.Has s α] (v : Checked α) (missingRef : ForeignKey α → ε) :
    Txn σ s ε (Except (Unique α) (Current σ α)) :=
  .bind (.insert α v) fun
    | .ok row => .pure (.ok row)
    | .error (.duplicate ix _) => .pure (.error ix)
    | .error (.missingRef fk) => .throw (missingRef fk)

/-- A duplicate returns the clashing declared alternative and leaves every
    table and counter exactly as it was. -/
theorem Txn.insertUnique_duplicate {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α] (v : Checked α) (missingRef : ForeignKey α → ε)
    (st : DbState s) (ix : Unique α) (holder : Id α)
    (clash : Txn.firstDuplicate v.val st none = some (ix, holder)) :
    Txn.denote (σ := σ) (Txn.insertUnique v missingRef) st = (.ok (.error ix), st) := by
  simp [Txn.insertUnique, Txn.denote, Txn.denote.go, clash]

/-- A missing reference is not a conflict: the transaction aborts with the
    mapped error and the state it started from. -/
theorem Txn.insertUnique_missingRef {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α] (v : Checked α) (missingRef : ForeignKey α → ε)
    (st : DbState s) (fk : ForeignKey α)
    (noClash : Txn.firstDuplicate v.val st none = none)
    (missing : Txn.firstMissingRef v.val st = some fk) :
    Txn.denote (σ := σ) (Txn.insertUnique v missingRef) st = (.error (missingRef fk), st) := by
  simp [Txn.insertUnique, Txn.denote, Txn.denote.go, noClash, missing]

/-- A denied proof-carrying read is literally `pure hidden`: equality of
    programs, not just of meanings, so `Read.exec` prepares nothing. -/
theorem Read.discloseIf_denied {s α β} [IsSchema s] (allowed : Prop) [Decidable allowed]
    (projection : allowed → Read s α) (visible : α → β) (hidden : β) (denied : ¬ allowed) :
    Read.discloseIf allowed projection visible hidden = .pure hidden := by
  simp [Read.discloseIf, denied]

theorem Read.discloseIf_allowed {s α β} [IsSchema s] (allowed : Prop) [Decidable allowed]
    (projection : allowed → Read s α) (visible : α → β) (hidden : β) (granted : allowed)
    (st : DbState s) :
    Read.denote (Read.discloseIf allowed projection visible hidden) st =
      visible (Read.denote (projection granted) st) := by
  simp [Read.discloseIf, granted, Read.denote]

/-- Denied viewers observe the same constructor whatever the hidden rows are. -/
theorem Read.discloseIf_denied_equal {s α β} [IsSchema s] (allowed : Prop) [Decidable allowed]
    (projection : allowed → Read s α) (visible : α → β) (hidden : β) (denied : ¬ allowed)
    (a b : DbState s) :
    Read.denote (Read.discloseIf allowed projection visible hidden) a =
      Read.denote (Read.discloseIf allowed projection visible hidden) b := by
  rw [Read.discloseIf_denied _ _ _ _ denied]
  rfl

/-- Every projected value comes from a stored target that a stored edge links
    to this parent, and it is exactly the selected field of that target. -/
theorem Read.linkField_provenance {s p t e} [IsSchema s]
    [Entity p] [Entity t] [Entity e] [IsSchema.Has s e] [IsSchema.Has s t]
    (relation : LinkRelation p t e) (parent : Id p) (field : Entity.Field t)
    (state : DbState s) (value : Entity.fieldTy field)
    (present : value ∈ Read.denote (.linkField relation parent field) state) :
    ∃ row : Valid t, row ∈ (state.get (α := t)).rows ∧
      (∃ edge : Valid e, edge ∈ (state.get (α := e)).rows ∧
        relation.getParent edge.val = parent ∧ relation.getTarget edge.val = row.id) ∧
      value = Entity.get field row.val := by
  change value ∈ Read.linkFieldDenote relation parent field state at present
  rcases List.mem_map.mp present with ⟨row, member, equal⟩
  rcases List.mem_filter.mp member with ⟨stored, related⟩
  refine ⟨row, stored, ?_, equal.symm⟩
  rcases List.any_eq_true.mp related with ⟨edge, edgeStored, linked⟩
  simp only [Bool.and_eq_true] at linked
  exact ⟨edge, edgeStored, Id.eq_of_beq linked.1, Id.eq_of_beq linked.2⟩

end LeanDb
