module

public import PaperProofs.Star.PStar_CurrentLegality_006
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentImmediate007

open Common Common.Native Parameters PStarLR PStarCurrentLegality006

theorem repairAction_advance_has_execution (P : PaperProofs.Star.Parameters) (order : Order)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (choice : Option (starInstance P.tools order).Tool)
    (selected : P.repairAction order history stage choice (.advance stage) = .advance stage) :
    (historyExecutions history).any (fun pair => pair.1.stage == stage) = true := by
  unfold Parameters.repairAction at selected
  split at selected
  · assumption
  · split at selected
    · cases selected
    · split at selected <;> cases selected

/-- An actual current-script advance past a written error already has its
real execution in the original ledger, even with terminal execution rights. -/
theorem prefix_advance_wrong_has_execution (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (early : C.reporting = .early) (accounting : NormalAccounting (starInstance P.tools order))
    {Seed : Type*} (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool)
    (tapes : ReviewTapes (P.input order)) {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state) (stage : (starInstance P.tools order).Stage)
    (selected : P.starReferenceRule order .current r limit seed state.history = .advance stage)
    (wrong : state.ledger.written stage = some (!state.ledger.truth stage)) :
    ∃ execution ∈ state.ledger.executions,
      execution.handle.stage = stage ∧ execution.atTime < state.clock := by
  classical
  have active : state.halted = false := by
    cases halted : state.halted with
    | false => rfl
    | true =>
      have historyHaltedEq := prefix_historyHalted (P.input order) C .uncapped accounting
        (P.starReferenceRule order .current r limit) seed truth tapes path
      simp only [Parameters.starReferenceRule, Parameters.candidateWithTesting,
        historyHaltedEq, halted, ↓reduceIte] at selected
      cases selected
  obtain ⟨next, step⟩ := current_legal_uncapped P order r limit C accounting
    seed truth tapes n state path active
  rw [selected] at step
  have cursor : state.cursor = stage.val := by
    cases step with
    | advance _ live _ _ => exact live.2
  have current : state.cursor < (starInstance P.tools order).stageCount := by
    rw [cursor]
    exact stage.isLt
  have stageEq : (⟨state.cursor, current⟩ : (starInstance P.tools order).Stage) = stage := Fin.ext cursor
  obtain ⟨time, reportTime⟩ := prefix_early_written_reported (P.input order) C early .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path stage
    (by rw [wrong]; exact Option.some_ne_none _)
  have report : historyReport state.history stage = some (state.ledger.truth stage, state.ledger.writeSerial stage) := by
    rw [prefix_historyReport_early (P.input order) C early .uncapped accounting
      (P.starReferenceRule order .current r limit) seed truth tapes path, reportTime]
    rfl
  have reportedWrong : reportedError state.history stage = true := by
    unfold reportedError
    rw [prefix_historyWritten (P.input order) C .uncapped accounting
      (P.starReferenceRule order .current r limit) seed truth tapes path, wrong, report]
    cases state.ledger.truth stage <;> rfl
  have historyActive : historyHalted state.history = false :=
    (prefix_historyHalted (P.input order) C .uncapped accounting
      (P.starReferenceRule order .current r limit) seed truth tapes path).trans active
  have historyCursorEq := prefix_historyCursor (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path
  unfold Parameters.starReferenceRule Parameters.candidateWithTesting at selected
  simp only [historyActive, Bool.false_eq_true, ↓reduceIte, historyCursorEq, current, ↓reduceDIte,
    stageEq, prefix_historyWritten (P.input order) C .uncapped accounting
      (P.starReferenceRule order .current r limit) seed truth tapes path, wrong,
    report, reportedWrong] at selected
  have executed := repairAction_advance_has_execution P order state.history stage _ selected
  obtain ⟨pair, member, hstage⟩ := List.any_eq_true.mp executed
  rw [prefix_historyExecutions (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) seed truth tapes path] at member
  obtain ⟨execution, actual, rfl⟩ := List.mem_map.mp member
  exact ⟨execution, actual, beq_iff_eq.mp hstage,
    (prefix_deadlineInvariant (P.input order) C .uncapped accounting
      (P.starReferenceRule order .current r limit) seed truth tapes path).execution_clock execution actual⟩

theorem immediateExecution (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (limit : Option ℕ) (C : Contract (starInstance P.tools order)) (early : C.reporting = .early)
    (accounting : NormalAccounting (starInstance P.tools order)) :
    P.ImmediateExecution order r limit C accounting := by
  intro sample n stage
  dsimp only
  intro selected wrong
  obtain ⟨clock, _bound, path⟩ := run_has_prefix (P.input order) C .uncapped accounting
    (P.starReferenceRule order .current r limit) (current_legal_uncapped P order r limit C accounting) sample n
  exact prefix_advance_wrong_has_execution P order r limit C early accounting sample.1 _ _ path stage selected wrong

end PaperProofs.Star.PStarCurrentImmediate007
