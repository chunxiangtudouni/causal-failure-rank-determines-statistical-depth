module

public import PaperProofs.Star.PStar_CurrentCases_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentLegality006

open Common Common.Native Parameters PStarLR PStarCurrentAllocation003 PStarCurrentExecution004 PStarCurrentCases005

/-- All actual Prefixes of the original current Star rule have a legal
next Step. It handles both original execution deadlines and every real
budget/limit; missing public reports or tools cause the original abandon. -/
theorem current_legal_uncapped (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*} :
    LegalRule (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit (Seed := Seed)) := by
  intro seed truth tapes n state path active
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes path).trans active
  have historyCursorEq := prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path
  by_cases current : state.cursor < (starInstance P.tools order).stageCount
  · let stage : (starInstance P.tools order).Stage := ⟨state.cursor, current⟩
    have live : liveStage state stage := ⟨active, rfl⟩
    cases written : state.ledger.written stage with
    | none =>
      have selected : P.starReferenceRule order .current r limit seed state.history =
          P.testingActionReal order .current r limit state.history stage := by
        unfold Parameters.starReferenceRule Parameters.candidateWithTesting
        simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, current]
        rw [prefix_historyWritten (P.input order) C .uncapped accounting
          (P.starReferenceRule order .current r limit) seed truth tapes path, written]
      rw [selected]
      exact testingActionReal_legal_uncapped P order .current r limit C accounting tapes state stage live written
    | some bit =>
      rcases current_written_action_cases P order r limit C accounting seed truth tapes path active current bit written with
        advance | abandon | ⟨handle, tool, allocate⟩ | ⟨handle, tool, execute⟩
      · rw [advance]
        exact ⟨_, Step.advance state stage live (by rw [written]; exact Option.some_ne_none _) (Or.inl rfl)⟩
      · rw [abandon]
        exact ⟨_, Step.abandon state active⟩
      · exact current_selected_allocate_has_step P order r limit C accounting seed truth tapes path active handle tool allocate
      · exact current_selected_execute_has_step P order r limit C accounting seed truth tapes path active handle tool execute
  · have selected : P.starReferenceRule order .current r limit seed state.history =
        if state.cursor = (starInstance P.tools order).stageCount then .stop else .abandon := by
      unfold Parameters.starReferenceRule Parameters.candidateWithTesting
      simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, current]
    rw [selected]
    split_ifs
    · exact ⟨_, Step.stop state active⟩
    · exact ⟨_, Step.abandon state active⟩

noncomputable def currentPolicy (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) {Seed : Type*} [MeasurableSpace Seed] :
    Policy (P.input order) C .uncapped accounting Seed where
  rule := P.starReferenceRule order .current r limit
  measurable_rule := P.measurable_starReferenceRule order .current r limit
  legal := current_legal_uncapped P order r limit C accounting

theorem currentReferenceLegality (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (accounting : NormalAccounting (starInstance P.tools order)) : P.ReferenceLegality order .current r limit C accounting :=
  ⟨currentPolicy P order r limit C accounting, rfl⟩

end PaperProofs.Star.PStarCurrentLegality006
