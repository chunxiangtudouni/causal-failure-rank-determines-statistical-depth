module

public import PaperProofs.Star.PStar_CurrentPastExecution_009
public import PaperProofs.Star.PStar_TargetGates_013
public import PaperProofs.Star.PStarLR_LateHaltWritten_020

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentAbort014

open Common Common.Native Parameters PStarLR PStarCurrentChoice001
  PStarCurrentSelection002 PStarCurrentToolIdentity008 PStarTargetGates013

/-- With no review quota, every actual current-script abandon is a genuine
written error with no available selected tool and no existing stage allocation.
Malformed words and missing early reports cannot create another failure. -/
theorem current_abandon_selection (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r none)
      seed truth tapes n state) (active : state.halted = false)
    (selected : P.starReferenceRule order .current r none seed state.history = .abandon) :
    ∃ stage : (starInstance P.tools order).Stage, state.cursor = stage.val ∧
      state.ledger.written stage = some (!state.ledger.truth stage) ∧
      P.currentToolChoice order state.history stage = none ∧
      (historyCommitments state.history).find? (fun pair => pair.1.stage == stage) = none := by
  classical
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted (P.input order) C .uncapped accounting
      (P.starReferenceRule order .current r none) seed truth tapes path).trans active
  have historyCursorEq := prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r none) seed truth tapes path
  by_cases current : state.cursor < (starInstance P.tools order).stageCount
  · let stage : (starInstance P.tools order).Stage := ⟨state.cursor, current⟩
    cases written : state.ledger.written stage with
    | none =>
      have testing : P.starReferenceRule order .current r none seed state.history =
          P.testingActionReal order .current r none state.history stage := by
        unfold Parameters.starReferenceRule Parameters.candidateWithTesting
        simp only [historyActive, Bool.false_eq_true, ↓reduceIte, historyCursorEq, current, ↓reduceDIte]
        rw [prefix_historyWritten (P.input order) C .uncapped accounting
          (P.starReferenceRule order .current r none) seed truth tapes path, written]
      have valid : ∀ symbol ∈ historyObservations state.history stage,
          symbol < P.channel.experiment.alphabetSize := by
        intro symbol member
        exact prefix_historyObservation_alphabet (P.input order) C .uncapped accounting
          (P.starReferenceRule order .current r none) seed truth tapes path stage symbol member
      exact (testingActionReal_noquota_ne_abandon P order .current r state.history stage valid
        (testing.symm.trans selected)).elim
    | some bit =>
      obtain ⟨time, reportTime⟩ := prefix_early_written_reported (P.input order) C early .uncapped accounting
        (P.starReferenceRule order .current r none) seed truth tapes path stage
        (by rw [written]; exact Option.some_ne_none _)
      have report : historyReport state.history stage = some (state.ledger.truth stage, state.ledger.writeSerial stage) := by
        rw [prefix_historyReport_early (P.input order) C early .uncapped accounting
          (P.starReferenceRule order .current r none) seed truth tapes path, reportTime]
        rfl
      have action : P.starReferenceRule order .current r none seed state.history =
          if reportedError state.history stage then
            P.repairAction order state.history stage (P.currentToolChoice order state.history stage) (.advance stage)
          else .advance stage := by
        unfold Parameters.starReferenceRule Parameters.candidateWithTesting
        simp only [historyActive, Bool.false_eq_true, ↓reduceIte, historyCursorEq, current, ↓reduceDIte]
        rw [prefix_historyWritten (P.input order) C .uncapped accounting
          (P.starReferenceRule order .current r none) seed truth tapes path, written, report]
      have wrong : reportedError state.history stage = true := by
        by_contra correct
        rw [action, ite_eq_right correct] at selected
        cases selected
      have mismatch := (prefix_reportedError_iff_wrong (P.input order) C early .uncapped accounting
        (P.starReferenceRule order .current r none) seed truth tapes path stage
        (by rw [written]; exact Option.some_ne_none _)).mp wrong
      have valid := prefix_reportedError_genuine (P.input order) C .uncapped accounting
        (P.starReferenceRule order .current r none) seed truth tapes path stage wrong
      have visible := prefix_referenceVisibleHandle_valid (P.input order) C .uncapped accounting
        (P.starReferenceRule order .current r none) seed truth tapes path _ valid
      rw [action, ite_eq_left wrong] at selected
      unfold Parameters.repairAction at selected
      split at selected
      · cases selected
      · cases allocated : (historyCommitments state.history).find? (fun pair => pair.1.stage == stage) with
        | some pair => simp only [allocated] at selected; cases selected
        | none =>
          simp only [allocated, visible] at selected
          cases chosen : P.currentToolChoice order state.history stage with
          | some tool => simp only [chosen] at selected; cases selected
          | none => exact ⟨stage, rfl, mismatch, chosen, allocated⟩
  · have terminal : state.cursor = (starInstance P.tools order).stageCount :=
      Nat.le_antisymm (prefix_cursorInvariant (P.input order) C .uncapped accounting
        (P.starReferenceRule order .current r none) seed truth tapes path).bound (Nat.le_of_not_gt current)
    unfold Parameters.starReferenceRule Parameters.candidateWithTesting at selected
    simp only [historyActive, Bool.false_eq_true, ↓reduceIte, historyCursorEq,
      dite_eq_right current, ite_eq_left terminal] at selected
    cases selected

end PaperProofs.Star.PStarCurrentAbort014
