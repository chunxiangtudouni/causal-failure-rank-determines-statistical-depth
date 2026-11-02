module

public import PaperProofs.Star.PStarLR_RepairSelection_010
public import PaperProofs.Star.PStarLR_ReportedBarrier_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star PaperProofs.Star.Parameters

namespace PStarLR

theorem retained_bad_prefix_no_corrections (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) :
    allWritten state.ledger → P.tools < (PaperProofs.Retained.ordinaryMismatches state.ledger).card →
      state.ledger.commitments = [] ∧ state.ledger.executions = [] := by
  classical
  induction path with
  | initial => intro _complete _bad; exact ⟨rfl, rfl⟩
  | @next n state next earlier step ih =>
    generalize haction : P.starReferenceRule order kind r limit seed state.history = action at step
    cases step with
    | review stage live port resources =>
      intro complete _bad
      exact (complete stage port).elim
    | write stage bit live port resources =>
      intro _complete _bad
      have before : state.cursor < (starInstance P.tools order).stageCount := by
        rw [live.2]
        exact stage.isLt
      have empty := retained_prefix_no_corrections_before_terminal P order kind retained r limit
        C mode accounting seed truth tapes earlier before
      change (reportedWriteLedger C state stage bit).commitments = [] ∧
        (reportedWriteLedger C state stage bit).executions = []
      simp only [reportedWriteLedger]
      split_ifs <;> exact empty
    | advance | stop | abandon => exact ih
    | allocate handle tool active valid compatible unused unallocated window resources =>
      intro complete bad
      change allWritten state.ledger at complete
      change P.tools < (PaperProofs.Retained.ordinaryMismatches state.ledger).card at bad
      have correcting : IsCorrection (P.starReferenceRule order kind r limit seed state.history) := by
        rw [haction]
        trivial
      have terminal := star_retained_correction_cursor P order kind retained r limit seed state.history correcting
      have historyActive : historyHalted state.history = false :=
        (prefix_historyHalted (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
          seed truth tapes earlier).trans active
      have barrier := retained_rule_at_barrier P order kind retained r limit seed state.history historyActive terminal
      obtain ⟨_stage, size, _wrong, _visible, _choice, _noCommit, _noExec, _hstage⟩ :=
        barrierAction_allocate_selection P order state.history handle tool (barrier.symm.trans haction)
      rw [prefix_complete_errors (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
        seed truth tapes earlier complete] at size
      exact (Nat.not_lt_of_ge size bad).elim
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro complete bad
      change allWritten state.ledger at complete
      change P.tools < (PaperProofs.Retained.ordinaryMismatches state.ledger).card at bad
      have correcting : IsCorrection (P.starReferenceRule order kind r limit seed state.history) := by
        rw [haction]
        trivial
      have terminal := star_retained_correction_cursor P order kind retained r limit seed state.history correcting
      have historyActive : historyHalted state.history = false :=
        (prefix_historyHalted (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
          seed truth tapes earlier).trans active
      have barrier := retained_rule_at_barrier P order kind retained r limit seed state.history historyActive terminal
      obtain ⟨_stage, size, _wrong, _committed, _hstage, _noExec⟩ :=
        barrierAction_execute_selection P order state.history handle tool (barrier.symm.trans haction)
      rw [prefix_complete_errors (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
        seed truth tapes earlier complete] at size
      exact (Nat.not_lt_of_ge size bad).elim

end PStarLR
