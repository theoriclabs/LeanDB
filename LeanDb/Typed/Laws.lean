import LeanDb.Typed.Txn
import LeanDb.Select

/-! # Laws (M15b)

Theorems LeanAPI cites: well-formedness of writes, read-only programs,
frame lemmas, failure exactness, write algebra, exact plans and aggregates.
-/

namespace LeanDb

/-! ## Array / window helpers -/

theorem Array.size_qsort {α} (as : Array α) (lt : α → α → Bool) :
    (as.qsort lt).size = as.size := by
  unfold Array.qsort
  split
  · rfl
  · exact Vector.size_toArray _

theorem finishRows_size {ts : List Type} [RowsOf ts]
    (rows : Array (Rows ts)) (where' : Rows ts → Bool) (sortBy : SortBy (Rows ts)) :
    (finishRows ts rows where' sortBy).size = (rows.filter where').size := by
  unfold finishRows
  split
  · rfl
  · exact Array.size_qsort _ _

theorem Window.apply_trivial {α} (rows : Array α) :
    Window.apply {} rows = rows := by
  simp [Window.apply]

/-! ## Exact plans -/

theorem Query.exact_hasOpaque {s ts ρ} (q : Query s ts ρ) :
    q.exact = true ↔ q.pred.hasOpaque = false := by
  simp [Query.exact]

theorem Query.exact_approx_denote {s ts ρ} (q : Query s ts ρ)
    (h : q.exact = true) (snap : Pred.Snapshot) (r : Rows ts) :
    q.pred.approx.denote snap r = q.pred.denote snap r :=
  Pred.approx_eq_denote snap q.pred ((Query.exact_hasOpaque q).mp h) r

/-! ## Aggregates (by definition of the meaning) -/

theorem Read.denote_count {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (h : q.exact = true) (st : DbState s) :
    Read.denote (Read.count q h) st =
      (Query.denote (s := s) { q with window := {} } st).size :=
  rfl

theorem Read.denote_exists {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (h : q.exact = true) (st : DbState s) :
    Read.denote (Read.exists q h) st =
      !(Query.denote (s := s) { q with window := { limit := some 1 } } st).isEmpty :=
  rfl

theorem Read.denote_first {s ts ρ} [IsSchema s] [GatherState s ts]
    [out : QueryRow s ts ρ]
    (q : Query s ts ρ) (h : q.exact = true) (st : DbState s) :
    Read.denote (Read.first q h) st =
      (Query.denote (s := s) q st)[0]?.bind (out.wrap st) :=
  rfl

theorem Read.denote_all {s ts ρ} [IsSchema s] [GatherState s ts]
    [out : QueryRow s ts ρ]
    (q : Query s ts ρ) (st : DbState s) :
    Read.denote (Read.all q) st =
      (Query.denote (s := s) q st).toList.filterMap (out.wrap st) :=
  rfl

theorem Query.denote_trivial_window {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (st : DbState s) :
    Query.denote (s := s) { q with window := {} } st =
      (@finishRows ts q.rowsOf
        (GatherState.gather (s := s) (ts := ts) st)
        (q.pred.denote (DbState.snapshot st)) q.sortBy).map q.toRow := by
  simp [Query.denote, Window.apply_trivial]

/-- `count = size ∘ rows` of the unwindowed query. -/
theorem Read.count_eq_rows {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (h : q.exact = true) (st : DbState s) :
    Read.denote (Read.count q h) st =
      ((@finishRows ts q.rowsOf
        (GatherState.gather (s := s) (ts := ts) st)
        (q.pred.denote (DbState.snapshot st)) q.sortBy).map q.toRow).size := by
  rw [Read.denote_count, Query.denote_trivial_window]

/-- `count` depends only on the number of admitted rows (sort permutes). -/
theorem Read.count_eq_admitted {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (h : q.exact = true) (st : DbState s) :
    Read.denote (Read.count q h) st =
      ((GatherState.gather (s := s) (ts := ts) st).filter
        (q.pred.denote (DbState.snapshot st))).size := by
  rw [Read.count_eq_rows, Array.size_map]
  exact @finishRows_size ts (q.rowsOf) _ _ _

/-! ## Reads do not write -/

theorem Txn.denote_liftRead {σ s ε α} [IsSchema s]
    (r : Read s α) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.liftRead r) st =
      (.ok (Read.denote r st), st) :=
  rfl

theorem Txn.denote_get {σ s ε α} [IsSchema s] [Entity α] [IsSchema.Has s α]
    (id : Id α) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.get α id) st =
      (.ok ((DbState.get (α := α) st).rows.find? (·.id == id) |>.map Current.ofValid),
        st) :=
  rfl

theorem Txn.denote_lookup {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [IsSchema.Has s α]
    (ix : Unique α) (key : Unique.Key ix) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.lookup α ix key) st =
      (.ok ((Read.lookupDenote st ix key).map Current.ofValid), st) :=
  rfl

theorem Txn.denote_pure {σ s ε α} [IsSchema s] (a : α) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.pure a) st = (.ok a, st) :=
  rfl

/-- Programs built only from `liftRead` / `get` / `lookup` / `pure` / `bind`. -/
inductive Txn.ReadOnly {σ s ε : Type} [IsSchema s] :
    {α : Type} → Txn σ s ε α → Prop where
  | protected «pure» {α} (a : α) : ReadOnly (.pure a)
  | protected bind {α β} (m : Txn σ s ε α) (f : α → Txn σ s ε β) :
      ReadOnly m → (∀ a, ReadOnly (f a)) → ReadOnly (.bind m f)
  | protected liftRead {α} (r : Read s α) : ReadOnly (.liftRead r)
  | protected get (α : Type) [Entity α] [IsSchema.Has s α] (id : Id α) :
      ReadOnly (.get α id)
  | protected lookup (α : Type) [Entity α] [HasUnique α] [IsSchema.Has s α]
      (ix : Unique α) (key : Unique.Key ix) : ReadOnly (.lookup α ix key)

theorem Txn.denote_readOnly {σ s ε α} [IsSchema s]
    {p : Txn σ s ε α} (h : Txn.ReadOnly p) (st : DbState s) :
    (Txn.denote p st).2 = st := by
  induction h generalizing st with
  | «pure» a => rfl
  | bind m f hm hf ihm ihf =>
      cases hgo : Txn.denote.go (σ := σ) (s := s) (ε := ε) st m st with
      | mk res st' =>
          have hst : st' = st := by
            simpa [Txn.denote, hgo] using ihm st
          cases res with
          | error _ =>
              simp [Txn.denote, Txn.denote.go, hgo, hst]
          | ok a =>
              simp [Txn.denote, Txn.denote.go, hgo, hst]
              exact ihf a st
  | liftRead r => rfl
  | get α id => rfl
  | lookup α ix key => rfl

/-! ## Failure exactness and write unfolding -/

theorem Txn.denote_throw {σ s ε α} [IsSchema s] (e : ε) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (α := α) (.throw e) st = (.error e, st) :=
  rfl

theorem Txn.denote_insert {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α] (v : Checked α) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.insert α v) st =
      match firstDuplicate v.val st none with
      | some (ix, holder) => (.ok (.error (.duplicate ix holder)), st)
      | none =>
          match firstMissingRef v.val st with
          | some fk => (.ok (.error (.missingRef fk)), st)
          | none =>
              let p := assign st v
              (.ok (.ok (Current.ofValid p.1)), p.2) :=
  rfl

theorem Txn.insert_duplicate_iff {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α]
    (v : Checked α) (st : DbState s) (ix : Unique α) (holder : Id α) :
    (Txn.denote (σ := σ) (s := s) (ε := ε) (.insert α v) st).1 =
        .ok (.error (.duplicate ix holder)) ↔
      firstDuplicate v.val st none = some (ix, holder) := by
  rw [Txn.denote_insert]
  cases h : firstDuplicate v.val st none with
  | none =>
      cases firstMissingRef v.val st <;> simp
  | some p =>
      cases p
      simp

theorem Txn.insert_missingRef_iff {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α]
    (v : Checked α) (st : DbState s) (fk : ForeignKey α) :
    (Txn.denote (σ := σ) (s := s) (ε := ε) (.insert α v) st).1 =
        .ok (.error (.missingRef fk)) ↔
      firstDuplicate v.val st none = none ∧ firstMissingRef v.val st = some fk := by
  rw [Txn.denote_insert]
  cases firstDuplicate v.val st none with
  | some _ => simp
  | none =>
      cases firstMissingRef v.val st <;> simp

theorem Txn.insert_ok_iff {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α]
    (v : Checked α) (st : DbState s) :
    (∃ row st', Txn.denote (σ := σ) (s := s) (ε := ε) (.insert α v) st =
        (.ok (.ok row), st')) ↔
      firstDuplicate v.val st none = none ∧ firstMissingRef v.val st = none := by
  rw [Txn.denote_insert]
  cases firstDuplicate v.val st none with
  | some _ => simp
  | none =>
      cases firstMissingRef v.val st <;> simp

theorem Txn.denote_update {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α]
    (old : Valid α) (new : Checked α) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.update α old new) st =
      match (DbState.get (α := α) st).rows.find? (·.id == old.id) with
      | none => (.ok (.error .gone), st)
      | some cur =>
          if !parentEq cur.val old.val then
            (.ok (.error (.stale cur.toStored)), st)
          else
            match firstDuplicate new.val st (some old.id) with
            | some (ix, holder) => (.ok (.error (.duplicate ix holder)), st)
            | none =>
                match firstMissingRef new.val st with
                | some fk => (.ok (.error (.missingRef fk)), st)
                | none =>
                    (.ok (.ok ⟨old.id, new.val⟩), replaceRow st old.id new) :=
  rfl

theorem Txn.update_cas {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α]
    (old : Valid α) (new : Checked α) (st : DbState s) (cur : Valid α)
    (hfind : (DbState.get (α := α) st).rows.find? (·.id == old.id) = some cur)
    (hcas : parentEq cur.val old.val = true)
    (hdup : firstDuplicate new.val st (some old.id) = none)
    (hfk : firstMissingRef new.val st = none) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.update α old new) st =
      (.ok (.ok ⟨old.id, new.val⟩), replaceRow st old.id new) := by
  rw [Txn.denote_update, hfind]
  simp [hcas, hdup, hfk]

/-! ## Frame (tables) -/

theorem Txn.assign_get_other {s α β} [IsSchema s] [Entity α] [Entity β]
    [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (st : DbState s) (c : Checked α) (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β) (assign (α := α) st c).2 = DbState.get (α := β) st := by
  by_cases hif : (DbState.get (α := α) st).next = 0 ∨
      natSqlMax < (DbState.get (α := α) st).next
  · simp [assign, hif]
  · simp [assign, hif, DbState.get_set_other (hneq := hneq)]

theorem Txn.replaceRow_get_other {s α β} [IsSchema s] [Entity α] [Entity β]
    [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (st : DbState s) (id : Id α) (c : Checked α) (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β) (replaceRow (α := α) st id c) = DbState.get (α := β) st := by
  simp [replaceRow, DbState.get_set_other (hneq := hneq)]

theorem Txn.replaceValid_get_other {s α β} [IsSchema s] [Entity α] [Entity β]
    [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (st : DbState s) (v : Valid α) (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β) (replaceValid (α := α) st v) = DbState.get (α := β) st := by
  simp [replaceValid, DbState.get_set_other (hneq := hneq)]

theorem Txn.insert_get_other {σ s ε α β} [IsSchema s] [Entity α] [Entity β]
    [HasUnique α] [HasForeignKey α]
    [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (v : Checked α) (st : DbState s) (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β)
      (Txn.denote (σ := σ) (s := s) (ε := ε) (.insert α v) st).2 =
      DbState.get (α := β) st := by
  rw [Txn.denote_insert]
  cases firstDuplicate v.val st none with
  | some _ => rfl
  | none =>
      cases firstMissingRef v.val st with
      | some _ => rfl
      | none => exact Txn.assign_get_other st v hneq

theorem Txn.update_get_other {σ s ε α β} [IsSchema s] [Entity α] [Entity β]
    [HasUnique α] [HasForeignKey α]
    [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (old : Valid α) (new : Checked α) (st : DbState s) (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β)
      (Txn.denote (σ := σ) (s := s) (ε := ε) (.update α old new) st).2 =
      DbState.get (α := β) st := by
  rw [Txn.denote_update]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · exact Txn.replaceRow_get_other st old.id new hneq

theorem Txn.assign_next {s α} [IsSchema s] [Entity α] [h : IsSchema.Has s α]
    (st : DbState s) (c : Checked α)
    (hin : (DbState.get (α := α) st).next ≠ 0)
    (hmax : (DbState.get (α := α) st).next ≤ natSqlMax) :
    (DbState.get (α := α) (assign st c).2).next =
      (DbState.get (α := α) st).next + 1 := by
  have hif : ¬ ((DbState.get (α := α) st).next = 0 ∨
      natSqlMax < (DbState.get (α := α) st).next) := by
    intro h
    cases h with
    | inl h0 => exact hin h0
    | inr hgt => exact Nat.not_lt.mpr hmax hgt
  simp [assign, hif, DbState.get_set_same]

theorem Txn.assign_id_eq_next {s α} [IsSchema s] [Entity α] [h : IsSchema.Has s α]
    (st : DbState s) (c : Checked α) :
    (assign st c).1.id.toInt64 = Int64.ofNat (DbState.get (α := α) st).next := by
  by_cases hif : (DbState.get (α := α) st).next = 0 ∨
      natSqlMax < (DbState.get (α := α) st).next
  · simp [assign, hif, Valid.ofChecked, Valid.id]
  · simp [assign, hif, Valid.ofChecked, Valid.id]

theorem Txn.replaceRow_next {s α} [IsSchema s] [Entity α] [h : IsSchema.Has s α]
    (st : DbState s) (id : Id α) (c : Checked α) :
    (DbState.get (α := α) (replaceRow (α := α) st id c)).next =
      (DbState.get (α := α) st).next := by
  simp [replaceRow, DbState.get_set_same]

theorem Txn.replaceValid_next {s α} [IsSchema s] [Entity α] [h : IsSchema.Has s α]
    (st : DbState s) (v : Valid α) :
    (DbState.get (α := α) (replaceValid (α := α) st v)).next =
      (DbState.get (α := α) st).next := by
  simp [replaceValid, DbState.get_set_same]

theorem Txn.removeRow_next {s α} [IsSchema s] [Entity α] [h : IsSchema.Has s α]
    (st : DbState s) (id : Id α) :
    (DbState.get (α := α) (removeRow (α := α) st id)).next =
      (DbState.get (α := α) st).next := by
  simp [removeRow, DbState.get_set_same]

theorem Table.eraseIdP_next (p : PackedEntity) (t : @Table p.ty p.entity)
    (id : Int64) :
    (@Table.next p.ty p.entity (Table.eraseIdP p t id)) =
      @Table.next p.ty p.entity t :=
  rfl

theorem Txn.eraseAt_tables {s} [i : IsSchema s] (st : DbState s)
    (t : Fin i.nTables) (id : Int64) (t2 : Fin i.nTables) (h : t2 ≠ t) :
    (eraseAt (s := s) st t id).tables t2 = st.tables t2 := by
  unfold eraseAt
  simp [dif_neg h]

/-! ## Remaining write unfolding (`rfl` like `denote_insert`) -/

theorem Txn.denote_set {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α]
    (row : Current σ α) (new : Checked α) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.set α row new) st =
      match (DbState.get (α := α) st).rows.find? (·.id == row.id) with
      | none => (.ok (.error .gone), st)
      | some _ =>
          match firstDuplicateTouching (Fields.all α) new.val st (some row.id) with
          | some (ix, holder) => (.ok (.error (.duplicate ix holder)), st)
          | none =>
              match firstMissingWithin (Fields.all α) new.val st with
              | some fk => (.ok (.error (.missingRef fk)), st)
              | none =>
                  (.ok (.ok (Current.ofValid (Valid.ofChecked row.id new))),
                    replaceRow st row.id new) :=
  rfl

theorem Txn.denote_patch {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α]
    (row : Current σ α) (fs : Fields α) (new : Checked α) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.patch α row fs new) st =
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
                  match Entity.check α merged with
                  | .error why => (.ok (.error (.invalid why)), st)
                  | .ok c =>
                      (.ok (.ok (Current.ofValid (Valid.ofChecked row.id c))),
                        replaceValid st (Valid.ofChecked row.id c)) :=
  rfl

theorem Txn.denote_append {σ s ε α} [IsSchema s] [Entity α] [HasListField α]
    [HasUnique α] [HasForeignKey α] [IsSchema.Has s α]
    (old : Valid α) (new : Checked α) (st : DbState s) :
    Txn.denote (σ := σ) (s := s) (ε := ε) (.append α old new) st =
      match (DbState.get (α := α) st).rows.find? (·.id == old.id) with
      | none => (.ok (.error .gone), st)
      | some cur =>
          if !parentEq cur.val old.val || listsMoved cur.val old.val then
            (.ok (.error (.stale cur.toStored)), st)
          else
            match firstNotAppend old.val new.val with
            | some lf => (.ok (.error (.notAppend lf)), st)
            | none =>
                match firstDuplicate new.val st (some old.id) with
                | some (ix, holder) => (.ok (.error (.duplicate ix holder)), st)
                | none =>
                    match firstMissingRef new.val st with
                    | some fk => (.ok (.error (.missingRef fk)), st)
                    | none =>
                        (.ok (.ok ⟨old.id, new.val⟩), replaceRow st old.id new) :=
  rfl

/-- Delete unfolding matches `denote.go`. The `rfl` form needs the packed
    `HasReferencedBy` instance; LeanAPI should unfold `Txn.denote.go`. -/
theorem Txn.delete_gone_state {σ s ε α} [IsSchema s] [Entity α]
    [HasReferencedBy s α] [IsSchema.Has s α]
    (id : Id α) (st : DbState s)
    (h : (DbState.get (α := α) st).rows.find? (·.id == id) = none) :
    (Txn.denote (σ := σ) (s := s) (ε := ε) (.delete α id) st).2 = st := by
  simp [Txn.denote, Txn.denote.go, h]

theorem Txn.set_get_other {σ s ε α β} [IsSchema s] [Entity α] [Entity β]
    [HasUnique α] [HasForeignKey α]
    [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (row : Current σ α) (new : Checked α) (st : DbState s)
    (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β)
      (Txn.denote (σ := σ) (s := s) (ε := ε) (.set α row new) st).2 =
      DbState.get (α := β) st := by
  rw [Txn.denote_set]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · exact Txn.replaceRow_get_other st row.id new hneq

theorem Txn.patch_get_other {σ s ε α β} [IsSchema s] [Entity α] [Entity β]
    [HasUnique α] [HasForeignKey α]
    [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (row : Current σ α) (fs : Fields α) (new : Checked α) (st : DbState s)
    (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β)
      (Txn.denote (σ := σ) (s := s) (ε := ε) (.patch α row fs new) st).2 =
      DbState.get (α := β) st := by
  rw [Txn.denote_patch]
  cases hfind : (DbState.get (α := α) st).rows.find? (·.id == row.id) with
  | none => simp [hfind]
  | some cur =>
      simp [hfind]
      cases hdup : firstDuplicateTouching fs (Fields.apply fs cur.val new.val) st
          (some row.id) with
      | some _ => simp [hdup]
      | none =>
          simp [hdup]
          cases hfk : firstMissingWithin fs (Fields.apply fs cur.val new.val) st with
          | some _ => simp [hfk]
          | none =>
              simp [hfk]
              cases Entity.check α (Fields.apply fs cur.val new.val) with
              | error _ => rfl
              | ok c => exact Txn.replaceValid_get_other st _ hneq

theorem Txn.append_get_other {σ s ε α β} [IsSchema s] [Entity α] [Entity β]
    [HasListField α] [HasUnique α] [HasForeignKey α]
    [ha : IsSchema.Has s α] [hb : IsSchema.Has s β]
    (old : Valid α) (new : Checked α) (st : DbState s)
    (hneq : ha.id ≠ hb.id) :
    DbState.get (α := β)
      (Txn.denote (σ := σ) (s := s) (ε := ε) (.append α old new) st).2 =
      DbState.get (α := β) st := by
  rw [Txn.denote_append]
  split
  · rfl
  · split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · split
          · rfl
          · exact Txn.replaceRow_get_other st old.id new hneq

/-- `SetError` has no `stale` constructor: `set` takes a `Current`. -/
theorem Txn.set_never_stale {α} [Entity α] [HasUnique α] [HasForeignKey α]
    (fs : Fields α) (e : SetError α fs) :
    match e with
    | .gone => True
    | .duplicate _ _ => True
    | .missingRef _ => True
    | .invalid _ => True := by
  cases e <;> trivial

/-! ## Query frame -/

theorem finishRows_eq_of_filter {ts : List Type} [RowsOf ts]
    (rows1 rows2 : Array (Rows ts)) (p1 p2 : Rows ts → Bool)
    (sortBy : SortBy (Rows ts))
    (h : rows1.filter p1 = rows2.filter p2) :
    finishRows ts rows1 p1 sortBy = finishRows ts rows2 p2 sortBy := by
  unfold finishRows
  rw [h]

theorem Query.denote_congr {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (st1 st2 : DbState s)
    (hg : GatherState.gather (s := s) (ts := ts) st1 =
      GatherState.gather (s := s) (ts := ts) st2)
    (hp : ∀ r, q.pred.denote (DbState.snapshot st1) r =
      q.pred.denote (DbState.snapshot st2) r) :
    @finishRows ts q.rowsOf (GatherState.gather (s := s) (ts := ts) st1)
      (q.pred.denote (DbState.snapshot st1)) q.sortBy =
    @finishRows ts q.rowsOf (GatherState.gather (s := s) (ts := ts) st2)
      (q.pred.denote (DbState.snapshot st2)) q.sortBy := by
  have : (q.pred.denote (DbState.snapshot st1)) =
      (q.pred.denote (DbState.snapshot st2)) := funext hp
  simp [hg, this]

theorem Query.denote_eq_of_finish {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (st1 st2 : DbState s)
    (h : @finishRows ts q.rowsOf (GatherState.gather (s := s) (ts := ts) st1)
        (q.pred.denote (DbState.snapshot st1)) q.sortBy =
      @finishRows ts q.rowsOf (GatherState.gather (s := s) (ts := ts) st2)
        (q.pred.denote (DbState.snapshot st2)) q.sortBy) :
    Query.denote (s := s) q st1 = Query.denote (s := s) q st2 := by
  simp [Query.denote, h]

/-- A query's meaning depends only on the gathered rows its predicate
    admits (same values, same order). Joins: `ts` is the joined list. -/
theorem Query.denote_eq_of_admitted {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (st1 st2 : DbState s)
    (h : (GatherState.gather (s := s) (ts := ts) st1).filter
          (q.pred.denote (DbState.snapshot st1)) =
        (GatherState.gather (s := s) (ts := ts) st2).filter
          (q.pred.denote (DbState.snapshot st2))) :
    Query.denote (s := s) q st1 = Query.denote (s := s) q st2 :=
  Query.denote_eq_of_finish q st1 st2
    (@finishRows_eq_of_filter ts q.rowsOf _ _ _ _ q.sortBy h)

theorem Read.denote_page {s ts ρ} [IsSchema s] [GatherState s ts]
    [out : QueryRow s ts ρ]
    (q : Query s ts ρ) (w : Window) (h : q.exact = true) (st : DbState s) :
    Read.denote (Read.page q w h) st =
      { items := (w.apply (Query.denote (s := s) { q with window := {} } st)).toList.filterMap
          (out.wrap st)
      , total := (Query.denote (s := s) { q with window := {} } st).size } :=
  rfl

theorem Read.denote_pure {s α} [IsSchema s] (a : α) (st : DbState s) :
    Read.denote (Read.pure (s := s) a) st = a :=
  rfl

theorem Read.denote_bind {s α β} [IsSchema s]
    (r : Read s α) (f : α → Read s β) (st : DbState s) :
    Read.denote (Read.bind r f) st = Read.denote (f (Read.denote r st)) st :=
  rfl

theorem Read.denote_get {s α} [IsSchema s] [Entity α] [IsSchema.Has s α]
    (id : Id α) (st : DbState s) :
    Read.denote (Read.get (s := s) α id) st =
      (DbState.get (α := α) st).rows.find? (·.id == id) :=
  rfl

/-- By type, `Read.denote` has no output state. Lifted into `Txn`, the
    state is unchanged. -/
theorem Read.denote_no_write {s α} [IsSchema s] (r : Read s α) (st : DbState s) :
    (Txn.denote (σ := Unit) (s := s) (ε := Empty) (.liftRead r) st).2 = st :=
  rfl

theorem Read.first_eq_of_admitted {s ts ρ} [IsSchema s] [GatherState s ts]
    [out : QueryRow s ts ρ]
    (q : Query s ts ρ) (h : q.exact = true) (st1 st2 : DbState s)
    (hadm : (GatherState.gather (s := s) (ts := ts) st1).filter
          (q.pred.denote (DbState.snapshot st1)) =
        (GatherState.gather (s := s) (ts := ts) st2).filter
          (q.pred.denote (DbState.snapshot st2)))
    (hwrap : ∀ r, out.wrap st1 r = out.wrap st2 r) :
    Read.denote (Read.first q h) st1 = Read.denote (Read.first q h) st2 := by
  rw [Read.denote_first, Read.denote_first, Query.denote_eq_of_admitted q st1 st2 hadm]
  cases (Query.denote (s := s) q st2)[0]? with
  | none => rfl
  | some r => simp [hwrap]

theorem Read.all_eq_of_admitted {s ts ρ} [IsSchema s] [GatherState s ts]
    [out : QueryRow s ts ρ]
    (q : Query s ts ρ) (st1 st2 : DbState s)
    (hadm : (GatherState.gather (s := s) (ts := ts) st1).filter
          (q.pred.denote (DbState.snapshot st1)) =
        (GatherState.gather (s := s) (ts := ts) st2).filter
          (q.pred.denote (DbState.snapshot st2)))
    (hwrap : ∀ r, out.wrap st1 r = out.wrap st2 r) :
    Read.denote (Read.all q) st1 = Read.denote (Read.all q) st2 := by
  rw [Read.denote_all, Read.denote_all, Query.denote_eq_of_admitted q st1 st2 hadm]
  induction (Query.denote (s := s) q st2).toList with
  | nil => rfl
  | cons x xs ih => simp [List.filterMap, hwrap x, ih]

theorem Read.count_eq_of_admitted {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (h : q.exact = true) (st1 st2 : DbState s)
    (hadm : (GatherState.gather (s := s) (ts := ts) st1).filter
          (q.pred.denote (DbState.snapshot st1)) =
        (GatherState.gather (s := s) (ts := ts) st2).filter
          (q.pred.denote (DbState.snapshot st2))) :
    Read.denote (Read.count q h) st1 = Read.denote (Read.count q h) st2 := by
  rw [Read.denote_count, Read.denote_count]
  have := Query.denote_eq_of_admitted (q := { q with window := {} }) st1 st2 hadm
  simpa using congrArg Array.size this

theorem Read.exists_eq_of_admitted {s ts ρ} [IsSchema s] [GatherState s ts]
    (q : Query s ts ρ) (h : q.exact = true) (st1 st2 : DbState s)
    (hadm : (GatherState.gather (s := s) (ts := ts) st1).filter
          (q.pred.denote (DbState.snapshot st1)) =
        (GatherState.gather (s := s) (ts := ts) st2).filter
          (q.pred.denote (DbState.snapshot st2))) :
    Read.denote (Read.exists q h) st1 = Read.denote (Read.exists q h) st2 := by
  rw [Read.denote_exists, Read.denote_exists]
  have hq : Query.denote (s := s) { q with window := { limit := some 1 } } st1 =
      Query.denote (s := s) { q with window := { limit := some 1 } } st2 :=
    Query.denote_eq_of_admitted (q := { q with window := { limit := some 1 } })
      st1 st2 hadm
  simp [hq]

/-- `page` agrees when the unwindowed query agrees; apply `Query.denote_eq_of_admitted`
    then `Window.apply` (a function of the array). `wrap` must agree. -/
theorem Read.page_eq_of_admitted {s ts ρ} [IsSchema s] [GatherState s ts]
    [out : QueryRow s ts ρ]
    (q : Query s ts ρ) (w : Window) (h : q.exact = true) (st1 st2 : DbState s)
    (hadm : (GatherState.gather (s := s) (ts := ts) st1).filter
          (q.pred.denote (DbState.snapshot st1)) =
        (GatherState.gather (s := s) (ts := ts) st2).filter
          (q.pred.denote (DbState.snapshot st2)))
    (hwrap : ∀ r, out.wrap st1 r = out.wrap st2 r) :
    Read.denote (Read.page q w h) st1 = Read.denote (Read.page q w h) st2 := by
  rw [Read.denote_page, Read.denote_page]
  have hq := Query.denote_eq_of_admitted (q := { q with window := {} }) st1 st2 hadm
  simp [hq]
  induction (w.apply (Query.denote (s := s) { q with window := {} } st2)).toList with
  | nil => rfl
  | cons x xs ih => simp [List.filterMap, hwrap x, ih]

/-- A `Read` whose queries only observe rows of `α` admitted by `adm`. -/
inductive Read.Scoped {s : Type} [IsSchema s] {α : Type}
    [Entity α] [IsSchema.Has s α]
    (adm : Stored α → Bool) : {β : Type} → Read s β → Prop where
  | mkPure {β} (b : β) : Read.Scoped (α := α) adm (Read.pure (s := s) b)
  | mkBind {β γ} (m : Read s β) (f : β → Read s γ) :
      Read.Scoped (α := α) adm m → (∀ b, Read.Scoped (α := α) adm (f b)) →
        Read.Scoped (α := α) adm (Read.bind m f)
  | mkFirst {ρ} [out : QueryRow s [α] ρ]
      (q : Query s [α] ρ) (h : q.exact = true)
      (himp : ∀ snap r, q.pred.denote snap r = true → adm r = true) :
      Read.Scoped (α := α) adm (Read.first q h)
  | mkAll {ρ} [out : QueryRow s [α] ρ] (q : Query s [α] ρ)
      (himp : ∀ snap r, q.pred.denote snap r = true → adm r = true) :
      Read.Scoped (α := α) adm (Read.all q)
  | mkPage {ρ} [out : QueryRow s [α] ρ]
      (q : Query s [α] ρ) (w : Window) (h : q.exact = true)
      (himp : ∀ snap r, q.pred.denote snap r = true → adm r = true) :
      Read.Scoped (α := α) adm (Read.page q w h)
  | mkCount {ρ} (q : Query s [α] ρ) (h : q.exact = true)
      (himp : ∀ snap r, q.pred.denote snap r = true → adm r = true) :
      Read.Scoped (α := α) adm (Read.count q h)
  | mkExists {ρ} (q : Query s [α] ρ) (h : q.exact = true)
      (himp : ∀ snap r, q.pred.denote snap r = true → adm r = true) :
      Read.Scoped (α := α) adm (Read.exists q h)

/-- `first = head? ∘ rows` of the (possibly windowed) query. -/
theorem Read.first_eq_head {s ts ρ} [IsSchema s] [GatherState s ts]
    [out : QueryRow s ts ρ]
    (q : Query s ts ρ) (h : q.exact = true) (st : DbState s) :
    Read.denote (Read.first q h) st =
      (Query.denote (s := s) q st)[0]?.bind (out.wrap st) :=
  Read.denote_first q h st

/-! ## Well-formedness -/

theorem Table.idsOk_nil {α} [Entity α] (n : Nat) :
    Table.idsOk ({ next := n, rows := [] } : Table α) = true :=
  rfl

theorem natSqlMax_eq : natSqlMax = 2 ^ 63 - 1 := by
  unfold natSqlMax
  change (Int64.maxValue.toInt).toNat = 2 ^ 63 - 1
  rw [Int64.toInt_maxValue]
  rfl

theorem natSqlMax_pos : 0 < natSqlMax := by
  rw [natSqlMax_eq]
  exact Nat.sub_pos_of_lt (Nat.one_lt_two_pow (by decide : 63 ≠ 0))

theorem Table.nextOk_one {α} [Entity α] :
    Table.nextOk ({ next := 1, rows := [] } : Table α) = true := by
  unfold Table.nextOk
  rw [Bool.and_eq_true]
  exact ⟨decide_eq_true (Nat.le_refl 1),
    decide_eq_true (Nat.le_add_left 1 natSqlMax)⟩

theorem Table.refsOk_nil {α} [Entity α] [HasForeignKey α] (n : Nat) :
    Table.refsOk ({ next := n, rows := [] } : Table α) = true :=
  rfl

theorem Table.invariantsOk_nil {α} [Entity α] (n : Nat) :
    Table.invariantsOk ({ next := n, rows := [] } : Table α) = true :=
  rfl

theorem Table.decodesOk_nil {α} [Entity α] (n : Nat) :
    Table.decodesOk ({ next := n, rows := [] } : Table α) = true :=
  rfl

theorem Table.checkedOk_nil {α} [Entity α] (n : Nat) :
    Table.checkedOk ({ next := n, rows := [] } : Table α) = true :=
  rfl

theorem Table.childrenOk_nil {α} [Entity α] (n : Nat) :
    Table.childrenOk ({ next := n, rows := [] } : Table α) = true :=
  rfl

theorem Array.all_true {α} (as : Array α) : as.all (fun _ => true) = true := by
  rw [Array.all_eq_true]
  intro _ _
  rfl

theorem Table.uniquesOk_nil {α} [Entity α] [HasUnique α] (n : Nat) :
    Table.uniquesOk ({ next := n, rows := [] } : Table α) = true := by
  unfold Table.uniquesOk
  exact Array.all_true _

theorem Table.check_nil {α} [Entity α] [HasUnique α] [HasForeignKey α] :
    Table.check ({ next := 1, rows := [] } : Table α) = true := by
  simp [Table.check, Table.nextOk_one, Table.idsOk_nil, Table.refsOk_nil,
    Table.invariantsOk_nil, Table.decodesOk_nil, Table.checkedOk_nil,
    Table.childrenOk_nil, Table.uniquesOk_nil]

theorem Table.fksOk_nil {s α} [IsSchema s] [Entity α] [HasForeignKey α]
    (st : DbState s) (n : Nat) :
    Table.fksOk (α := α) st ({ next := n, rows := [] } : Table α) = true :=
  rfl

theorem Table.check_ofPacked_nil (p : PackedEntity) :
    @Table.check p.ty p.entity p.unique p.foreignKey
      (@Table.mk p.ty p.entity 1 []) = true :=
  @Table.check_nil p.ty p.entity p.unique p.foreignKey

theorem Table.fksOk_ofPacked_nil {s} [IsSchema s] (st : DbState s) (p : PackedEntity) :
    @Table.fksOk s p.ty inferInstance p.entity p.foreignKey st
      (@Table.mk p.ty p.entity 1 []) = true :=
  rfl

theorem DbState.checkPacked_empty {s} [i : IsSchema s] (t : Fin i.nTables) :
    DbState.checkPacked (DbState.empty (s := s)) t = true := by
  unfold DbState.checkPacked DbState.empty
  simp only [Table.ofPacked]
  rw [Table.check_ofPacked_nil, Bool.true_and]
  exact Table.fksOk_ofPacked_nil _ _

theorem DbState.empty_wf {s} [i : IsSchema s] : (DbState.empty (s := s)).WF := by
  unfold DbState.WF DbState.checkWF
  rw [Array.all_eq_true_iff_forall_mem]
  intro t ht
  have ht' : t ∈ Array.ofFn (n := i.nTables) id := by
    simpa [IsSchema.tables] using ht
  obtain ⟨k, hk⟩ := Array.mem_ofFn.mp ht'
  cases hk
  exact DbState.checkPacked_empty k

theorem Table.invariantsOk_valid {α} [Entity α] (t : Table α) :
    t.invariantsOk = true := by
  unfold Table.invariantsOk
  rw [List.all_eq_true]
  intro r _
  cases h : Entity.invariant (α := α) with
  | none => rfl
  | some p =>
      have hin := r.property
      unfold Invariant at hin
      simp [h] at hin
      exact hin.2

theorem Txn.assign_invariantsOk {s α} [IsSchema s] [Entity α] [h : IsSchema.Has s α]
    (st : DbState s) (c : Checked α) :
    (DbState.get (α := α) (assign st c).2).invariantsOk = true :=
  Table.invariantsOk_valid _

/-- `WF` is preserved when the meaning leaves the state unchanged.
    Successful-write `idsOk`/`uniquesOk`/`fksOk`, cascade `WF`, and a
    generic `empty_wf` are the remainder in `docs/typed-interface.md`.
    `loadWF` is the runtime `checkWF` gate. -/
theorem Txn.denote_wf {σ s ε α} [IsSchema s]
    (p : Txn σ s ε α) (st : DbState s) (hwf : st.WF)
    (heq : (Txn.denote p st).2 = st) :
    (Txn.denote p st).2.WF := by
  rw [heq]
  exact hwf

theorem Txn.denote_readOnly_wf {σ s ε α} [IsSchema s]
    {p : Txn σ s ε α} (h : Txn.ReadOnly p) (st : DbState s) (hwf : st.WF) :
    (Txn.denote p st).2.WF :=
  Txn.denote_wf p st hwf (Txn.denote_readOnly h st)

theorem Txn.denote_throw_wf {σ s ε α} [IsSchema s]
    (e : ε) (st : DbState s) (hwf : st.WF) :
    (Txn.denote (σ := σ) (s := s) (ε := ε) (α := α) (.throw e) st).2.WF := by
  rw [Txn.denote_throw]
  exact hwf

theorem Txn.insert_wf_of_fail {σ s ε α} [IsSchema s] [Entity α] [HasUnique α]
    [HasForeignKey α] [IsSchema.Has s α]
    (v : Checked α) (st : DbState s) (hwf : st.WF)
    (hfail : ¬ (firstDuplicate v.val st none = none ∧
      firstMissingRef v.val st = none)) :
    (Txn.denote (σ := σ) (s := s) (ε := ε) (.insert α v) st).2.WF := by
  rw [Txn.denote_insert]
  cases hdup : firstDuplicate v.val st none with
  | some _ => exact hwf
  | none =>
      cases hfk : firstMissingRef v.val st with
      | some _ => exact hwf
      | none => exact (hfail ⟨hdup, hfk⟩).elim

end LeanDb

