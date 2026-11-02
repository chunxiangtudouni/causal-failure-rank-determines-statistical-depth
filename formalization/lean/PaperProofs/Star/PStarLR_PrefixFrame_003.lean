module

public import PaperProofs.Star.PStarLR_ActionShape_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PStarLR

theorem retained_prefix_no_corrections_before_terminal (P : PaperProofs.Star.Parameters)
    (order : Order) (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order kind r limit)
      seed truth tapes n state) (before : state.cursor < (starInstance P.tools order).stageCount) :
    state.ledger.commitments = [] ∧ state.ledger.executions = [] := by
  revert before
  induction path with
  | initial => intro _before; exact ⟨rfl, rfl⟩
  | @next n state next earlier step ih =>
    intro before
    have oldBefore := lt_of_le_of_lt (step_cursor_bounds (P.input order) C mode accounting tapes step).1 before
    have oldNil := ih oldBefore
    generalize haction : P.starReferenceRule order kind r limit seed state.history = action at step
    cases step with
    | allocate handle tool active valid compatible unused unallocated window resources =>
      have correcting : IsCorrection (P.starReferenceRule order kind r limit seed state.history) := by
        rw [haction]
        trivial
      have terminal := star_retained_correction_cursor P order kind retained r limit seed state.history correcting
      rw [prefix_historyCursor (P.input order) C mode accounting
        (P.starReferenceRule order kind r limit) seed truth tapes earlier] at terminal
      change state.cursor < (starInstance P.tools order).stageCount at before
      omega
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      have correcting : IsCorrection (P.starReferenceRule order kind r limit seed state.history) := by
        rw [haction]
        trivial
      have terminal := star_retained_correction_cursor P order kind retained r limit seed state.history correcting
      rw [prefix_historyCursor (P.input order) C mode accounting
        (P.starReferenceRule order kind r limit) seed truth tapes earlier] at terminal
      change state.cursor < (starInstance P.tools order).stageCount at before
      omega
    | write stage bit live port resources =>
      change (reportedWriteLedger C state stage bit).commitments = [] ∧
        (reportedWriteLedger C state stage bit).executions = []
      simp only [reportedWriteLedger]
      split_ifs <;> exact oldNil
    | review | advance | stop | abandon => exact oldNil

theorem retainedNoEarlyCommitment_of_legal (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    (legal : LegalRule (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r limit (Seed := Unit))) :
    P.RetainedNoEarlyCommitment order kind r limit C accounting := by
  intro sample n
  dsimp only
  intro incomplete
  obtain ⟨clock, _hclock, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r limit) legal sample n
  exact retained_prefix_no_corrections_before_terminal P order kind retained r limit C .uncapped
    accounting sample.1 ((P.input order).truthAt sample.2) (worldTapes (P.input order) sample.2) path
      (prefix_cursor_lt_of_not_allWritten (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind r limit) sample.1 _ _ path incomplete)

theorem late_prefix_other_reviews_zero (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C mode accounting (P.starReferenceRule order .lateRetained r limit)
      seed truth tapes n state) :
    ∀ stage : (starInstance P.tools order).Stage, stage.val ≠ 0 → state.ledger.reviews stage = 0 := by
  induction path with
  | initial => intro stage _nonzero; rfl
  | @next n state next earlier step ih =>
    generalize haction : P.starReferenceRule order .lateRetained r limit seed state.history = action at step
    cases step with
    | review stage live port resources =>
      have hzero : stage.val = 0 := by
        by_contra nonzero
        have hcursor : historyCursor state.history ≠ 0 := by
          rw [prefix_historyCursor (P.input order) C mode accounting
            (P.starReferenceRule order .lateRetained r limit) seed truth tapes earlier, live.2]
          exact nonzero
        exact (lateRule_ne_review_of_cursor_ne_zero P order r limit seed state.history hcursor stage) haction
      intro other nonzero
      have hne : other ≠ stage := by intro heq; subst other; exact nonzero hzero
      simp only [record, reviewLedger, Function.update_of_ne hne]
      exact ih other nonzero
    | write stage bit live port resources =>
      simp only [record, reportedWriteLedger]
      split_ifs <;> exact ih
    | allocate | execute | advance | stop | abandon => exact ih

theorem late_run_other_reviews_zero_of_legal (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order)) (mode : ResourceMode)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (legal : LegalRule (P.input order) C mode accounting
      (P.starReferenceRule order .lateRetained r limit (Seed := Seed)))
    (sample : Seed × (P.input order).World) (n : ℕ)
    (stage : (starInstance P.tools order).Stage) (nonzero : stage.val ≠ 0) :
    (run (P.input order) C mode accounting (P.starReferenceRule order .lateRetained r limit)
      sample n).ledger.reviews stage = 0 := by
  obtain ⟨clock, _hclock, path⟩ := run_has_prefix (P.input order) C mode accounting
    (P.starReferenceRule order .lateRetained r limit) legal sample n
  exact late_prefix_other_reviews_zero P order r limit C mode accounting sample.1 _ _ path stage nonzero

end PStarLR
