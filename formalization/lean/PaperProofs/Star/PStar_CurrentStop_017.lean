module

public import PaperProofs.Star.PStar_SingletonsAbort_016

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentStop017

open Common Common.Native Parameters PStarLR PStarCurrentCases005 PStarCurrentPastExecution009

theorem current_stop_terminal (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (accounting : NormalAccounting (starInstance P.tools order))
    {Seed : Type*} (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool)
    (tapes : ReviewTapes (P.input order)) {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r none)
      seed truth tapes n state) (active : state.halted = false)
    (selected : P.starReferenceRule order .current r none seed state.history = .stop) :
    state.cursor = (starInstance P.tools order).stageCount := by
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
      rw [testing] at selected
      rcases testingActionReal_cases P order .current r none state.history stage with
        review | ⟨bit, write⟩ | abandon
      · rw [review] at selected; cases selected
      · rw [write] at selected; cases selected
      · rw [abandon] at selected; cases selected
    | some bit =>
      rcases current_written_action_cases P order r none C accounting seed truth tapes path active current bit written with
        advance | abandon | ⟨handle, tool, allocate⟩ | ⟨handle, tool, execute⟩
      · rw [advance] at selected; cases selected
      · rw [abandon] at selected; cases selected
      · rw [allocate] at selected; cases selected
      · rw [execute] at selected; cases selected
  · exact Nat.le_antisymm (prefix_cursorInvariant (P.input order) C .uncapped accounting
      (P.starReferenceRule order .current r none) seed truth tapes path).bound (Nat.le_of_not_gt current)

/-- A real stop of this current script is physically successful. Earlier
ordinary errors have already been executed inside their actual windows. -/
theorem current_stop_success (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (C : Contract (starInstance P.tools order)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*}
    (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool) (tapes : ReviewTapes (P.input order))
    {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r none)
      seed truth tapes n state) (active : state.halted = false)
    (selected : P.starReferenceRule order .current r none seed state.history = .stop) :
    (stopState state false).ledger.success C := by
  classical
  have terminal := current_stop_terminal P order r C accounting seed truth tapes path active selected
  have complete := prefix_allWritten_of_terminal (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r none) seed truth tapes path terminal
  have corrected := prefix_terminal_errorsExecuted P order r none C early accounting
    seed truth tapes path terminal
  have nextPath : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r none)
      seed truth tapes (n+1) (stopState state false) := by
    apply Prefix.next path
    rw [selected]
    exact Step.stop state active
  apply (prefix_success_iff_physical (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r none) seed truth tapes nextPath).mpr
  refine ⟨?_, rfl, ?_⟩
  · change decide (allWritten state.ledger) = true
    exact decide_eq_true complete
  · intro stage
    apply (finalOutput_correct_iff (stopState state false).ledger stage).mpr
    obtain ⟨bit, written⟩ := Option.ne_none_iff_exists'.mp (complete stage)
    by_cases correct : bit = state.ledger.truth stage
    · exact Or.inl (by change state.ledger.written stage = some (state.ledger.truth stage); rwa [correct] at written)
    · have opposite : bit = !state.ledger.truth stage := by
        cases bit <;> cases ht : state.ledger.truth stage <;> simp_all
      exact Or.inr (corrected stage (written.trans (congrArg some opposite)))

end PaperProofs.Star.PStarCurrentStop017
