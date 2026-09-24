/-
  Fail if key M15-pre definitions/theorems depend on axioms beyond the
  standard trio `propext`, `Classical.choice`, `Quot.sound`.
  Compiled as part of `lake exe leandb_tests` (imported from Tests.lean).
-/
import Lean
import LeanDb
import TestsM14a

open Lean Elab Command

def allowedAxioms : NameSet :=
  ({} : NameSet)
    |>.insert ``propext
    |>.insert ``Classical.choice
    |>.insert ``Quot.sound

def assertAxioms (n : Name) : CommandElabM Unit := do
  let env ← getEnv
  unless env.contains n do
    throwError "axiom check: unknown constant {n}"
  let axs ← collectAxioms n
  let extra := axs.toList.filter (fun a => !allowedAxioms.contains a)
  unless extra.isEmpty do
    throwError "axiom check: {n} depends on {extra} (allowed: propext, Classical.choice, Quot.sound)"
  logInfo m!"axiom check: {n} OK {axs.toList}"

elab "#check_m15_axioms" : command => do
  assertAxioms ``LeanDb.DbState.get_set_same
  assertAxioms ``LeanDb.DbState.get_set_other
  assertAxioms ``LeanDb.DbState.set_tables_other
  assertAxioms ``LeanDb.DbState.empty_rows
  assertAxioms ``LeanDb.Txn.denote
  assertAxioms ``LeanDb.Read.denote
  assertAxioms ``TestsM14a.insert_team_on_empty
  -- M15b: codecs / exact plans / order
  assertAxioms ``LeanDb.LawfulColCodec.roundTrip
  assertAxioms ``LeanDb.fromCol_toCol_nat
  assertAxioms ``LeanDb.fromCol_toCol_float
  assertAxioms ``LeanDb.ColCodec.via_roundTrip
  assertAxioms ``LeanDb.Pred.approx_eq_denote
  assertAxioms ``LeanDb.Pred.residuals_eq_zero_of_not_opaque
  assertAxioms ``LeanDb.LawfulSqlOrd.order_toCol
  assertAxioms ``LeanDb.nat_order_toCol
  -- M15b: aggregates and exact queries
  assertAxioms ``LeanDb.Query.exact_approx_denote
  assertAxioms ``LeanDb.Query.exact_hasOpaque
  assertAxioms ``LeanDb.Read.denote_count
  assertAxioms ``LeanDb.Read.denote_exists
  assertAxioms ``LeanDb.Read.denote_first
  assertAxioms ``LeanDb.Read.denote_all
  assertAxioms ``LeanDb.Read.count_eq_rows
  assertAxioms ``LeanDb.Read.count_eq_admitted
  assertAxioms ``LeanDb.Read.first_eq_head
  -- M15b: reads do not write
  assertAxioms ``LeanDb.Read.denote_no_write
  assertAxioms ``LeanDb.Txn.denote_liftRead
  assertAxioms ``LeanDb.Txn.denote_readOnly
  assertAxioms ``LeanDb.Txn.ReadOnly.pure
  -- M15b: failure exactness
  assertAxioms ``LeanDb.Txn.denote_insert
  assertAxioms ``LeanDb.Txn.insert_duplicate_iff
  assertAxioms ``LeanDb.Txn.insert_missingRef_iff
  assertAxioms ``LeanDb.Txn.insert_ok_iff
  assertAxioms ``LeanDb.Txn.denote_update
  assertAxioms ``LeanDb.Txn.update_cas
  assertAxioms ``LeanDb.Txn.denote_set
  assertAxioms ``LeanDb.Txn.denote_patch
  assertAxioms ``LeanDb.Txn.denote_append
  assertAxioms ``LeanDb.Txn.set_never_stale
  -- M15b: frames and write algebra
  assertAxioms ``LeanDb.Txn.insert_get_other
  assertAxioms ``LeanDb.Txn.update_get_other
  assertAxioms ``LeanDb.Txn.set_get_other
  assertAxioms ``LeanDb.Txn.patch_get_other
  assertAxioms ``LeanDb.Txn.append_get_other
  assertAxioms ``LeanDb.Txn.assign_next
  assertAxioms ``LeanDb.Txn.assign_id_eq_next
  assertAxioms ``LeanDb.Txn.replaceRow_next
  assertAxioms ``LeanDb.Txn.removeRow_next
  assertAxioms ``LeanDb.Table.eraseIdP_next
  assertAxioms ``LeanDb.Txn.eraseAt_tables
  assertAxioms ``LeanDb.Query.denote_eq_of_admitted
  assertAxioms ``LeanDb.Read.first_eq_of_admitted
  assertAxioms ``LeanDb.Read.all_eq_of_admitted
  assertAxioms ``LeanDb.Read.count_eq_of_admitted
  assertAxioms ``LeanDb.Read.exists_eq_of_admitted
  assertAxioms ``LeanDb.Read.page_eq_of_admitted
  -- M15b: well-formedness
  assertAxioms ``LeanDb.Table.check_nil
  assertAxioms ``LeanDb.Table.invariantsOk_valid
  assertAxioms ``LeanDb.Txn.denote_wf
  assertAxioms ``LeanDb.Txn.denote_readOnly_wf
  assertAxioms ``LeanDb.Txn.denote_throw_wf
  assertAxioms ``LeanDb.Txn.insert_wf_of_fail
  assertAxioms ``LeanDb.Txn.assign_invariantsOk
  assertAxioms ``LeanDb.Txn.delete_gone_state
  -- M15b2: nextOk / empty_wf
  assertAxioms ``LeanDb.natSqlMax_eq
  assertAxioms ``LeanDb.natSqlMax_pos
  assertAxioms ``LeanDb.Table.nextOk_one
  assertAxioms ``LeanDb.Table.check_ofPacked_nil
  assertAxioms ``LeanDb.DbState.checkPacked_empty
  assertAxioms ``LeanDb.DbState.empty_wf
  -- remaining M15b theorems
  assertAxioms ``LeanDb.Array.size_qsort
  assertAxioms ``LeanDb.finishRows_size
  assertAxioms ``LeanDb.Window.apply_trivial
  assertAxioms ``LeanDb.Query.denote_trivial_window
  assertAxioms ``LeanDb.Txn.denote_get
  assertAxioms ``LeanDb.Txn.denote_lookup
  assertAxioms ``LeanDb.Txn.denote_pure
  assertAxioms ``LeanDb.Txn.denote_throw
  assertAxioms ``LeanDb.Txn.assign_get_other
  assertAxioms ``LeanDb.Txn.replaceRow_get_other
  assertAxioms ``LeanDb.Txn.replaceValid_get_other
  assertAxioms ``LeanDb.Txn.replaceValid_next
  assertAxioms ``LeanDb.finishRows_eq_of_filter
  assertAxioms ``LeanDb.Query.denote_congr
  assertAxioms ``LeanDb.Query.denote_eq_of_finish
  assertAxioms ``LeanDb.Read.denote_page
  assertAxioms ``LeanDb.Read.denote_pure
  assertAxioms ``LeanDb.Read.denote_bind
  assertAxioms ``LeanDb.Read.denote_get
  assertAxioms ``LeanDb.Table.idsOk_nil
  assertAxioms ``LeanDb.Table.refsOk_nil
  assertAxioms ``LeanDb.Table.invariantsOk_nil
  assertAxioms ``LeanDb.Table.decodesOk_nil
  assertAxioms ``LeanDb.Table.checkedOk_nil
  assertAxioms ``LeanDb.Table.childrenOk_nil
  assertAxioms ``LeanDb.Array.all_true
  assertAxioms ``LeanDb.Table.uniquesOk_nil
  assertAxioms ``LeanDb.Table.fksOk_nil
  assertAxioms ``LeanDb.LawfulEntity.decode_encode
  assertAxioms ``LeanDb.LawfulEntity.children_attach
  assertAxioms ``LeanDb.DbState.loadWF
  assertAxioms ``LeanDb.natToSql_of_le

#check_m15_axioms
