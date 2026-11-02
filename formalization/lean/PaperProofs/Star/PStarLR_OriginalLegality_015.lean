module

public import PaperProofs.Star.PStarLR_ExecutionLegality_014
public import PaperProofs.Star.PStarLR_TestingLegality_012

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PStarLR

theorem retained_legal_uncapped (P : PaperProofs.Star.Parameters) (order : Order)
    (kind : PortKind) (retained : kind ≠ .current) (r : ℝ) (limit : Option ℕ)
    (C : Contract (starInstance P.tools order)) (terminalAllocation : C.allocation = .terminalBarrier)
    (terminalExecution : C.execution = .terminalBarrier) (accounting : NormalAccounting (starInstance P.tools order))
    {Seed : Type*} : LegalRule (P.input order) C .uncapped accounting
      (P.starReferenceRule order kind r limit (Seed := Seed)) := by
  classical
  intro seed truth tapes n state path active
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted (P.input order) C .uncapped accounting (P.starReferenceRule order kind r limit)
      seed truth tapes path).trans active
  have historyCursorEq := prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order kind r limit) seed truth tapes path
  by_cases current : state.cursor < (starInstance P.tools order).stageCount
  · let stage : (starInstance P.tools order).Stage := ⟨state.cursor, current⟩
    have live : liveStage state stage := ⟨active, rfl⟩
    cases written : state.ledger.written stage with
    | none =>
      have selected : P.starReferenceRule order kind r limit seed state.history =
          P.testingActionReal order kind r limit state.history stage := by
        unfold Parameters.starReferenceRule Parameters.candidateWithTesting
        simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, current]
        rw [prefix_historyWritten (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind r limit) seed truth tapes path, written]
      rw [selected]
      exact testingActionReal_legal_uncapped P order kind r limit C accounting tapes state stage live written
    | some bit =>
      have selected : P.starReferenceRule order kind r limit seed state.history = .advance stage := by
        unfold Parameters.starReferenceRule Parameters.candidateWithTesting
        simp only [historyActive, Bool.false_eq_true, ↓reduceIte, ↓reduceDIte, historyCursorEq, current]
        rw [prefix_historyWritten (P.input order) C .uncapped accounting
          (P.starReferenceRule order kind r limit) seed truth tapes path, written]
        cases kind with
        | current => exact (retained rfl).elim
        | earlyRetained | lateRetained => rfl
      rw [selected]
      exact ⟨_, Step.advance state stage live (by rw [written]; exact Option.some_ne_none _) (Or.inl rfl)⟩
  · have terminal : state.cursor = (starInstance P.tools order).stageCount :=
      Nat.le_antisymm (prefix_cursorInvariant (P.input order) C .uncapped accounting
        (P.starReferenceRule order kind r limit) seed truth tapes path).bound (Nat.le_of_not_gt current)
    have selected := retained_rule_at_barrier P order kind retained r limit seed state.history historyActive
      (historyCursorEq.trans terminal)
    rcases barrierAction_cases P order state.history with stop | abandon | ⟨handle, tool, allocate⟩ | ⟨handle, tool, execute⟩
    · rw [selected, stop]
      exact ⟨_, Step.stop state active⟩
    · rw [selected, abandon]
      exact ⟨_, Step.abandon state active⟩
    · exact retained_selected_allocate_has_step P order kind retained r limit C terminalAllocation accounting
        seed truth tapes path active handle tool (selected.trans allocate)
    · exact retained_selected_execute_has_step P order kind retained r limit C terminalExecution accounting
        seed truth tapes path active handle tool (selected.trans execute)

theorem lateReferenceLegality (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (limit : Option ℕ) (C : Contract (starInstance P.tools order)) (late : C.IsLateRetained)
    (accounting : NormalAccounting (starInstance P.tools order)) :
    P.ReferenceLegality order .lateRetained r limit C accounting := by
  refine ⟨{ rule := P.starReferenceRule order .lateRetained r limit
            measurable_rule := P.measurable_starReferenceRule order .lateRetained r limit
            legal := retained_legal_uncapped P order .lateRetained (by decide) r limit C
              late.2.1 late.2.2 accounting }, rfl⟩

theorem earlyReferenceLegality (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (limit : Option ℕ) (C : Contract (starInstance P.tools order)) (early : C.IsEarlyRetained)
    (accounting : NormalAccounting (starInstance P.tools order)) :
    P.ReferenceLegality order .earlyRetained r limit C accounting := by
  refine ⟨{ rule := P.starReferenceRule order .earlyRetained r limit
            measurable_rule := P.measurable_starReferenceRule order .earlyRetained r limit
            legal := retained_legal_uncapped P order .earlyRetained (by decide) r limit C
              early.2.1 early.2.2 accounting }, rfl⟩

end PStarLR
