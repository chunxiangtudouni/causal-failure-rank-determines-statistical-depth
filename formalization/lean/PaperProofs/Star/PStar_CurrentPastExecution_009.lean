module

public import PaperProofs.Star.PStar_CurrentToolIdentity_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCurrentPastExecution009

open Common Common.Native Parameters PStarLR PStarCurrentImmediate007 PStarCurrentLegality006

def PastErrorsExecuted (P : PaperProofs.Star.Parameters) (order : Order)
    (state : State (starInstance P.tools order)) : Prop :=
  ∀ stage : (starInstance P.tools order).Stage, stage.val < state.cursor →
    state.ledger.written stage = some (!state.ledger.truth stage) →
      ∃ execution ∈ state.ledger.executions, execution.handle.stage = stage

/-- Actual current windows cannot be left with an unexecuted known error.
The invariant includes histories which later fail or abandon. -/
theorem prefix_pastErrorsExecuted (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (early : C.reporting = .early) (accounting : NormalAccounting (starInstance P.tools order))
    {Seed : Type*} (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool)
    (tapes : ReviewTapes (P.input order)) {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state) : PastErrorsExecuted P order state := by
  classical
  induction path with
  | initial => intro stage past; change stage.val < 0 at past; omega
  | @next n state next earlier step ih =>
    generalize haction : P.starReferenceRule order .current r limit seed state.history = action at step
    cases step with
    | review => exact ih
    | write stage bit live port resources =>
      intro other past wrong
      change other.val < state.cursor at past
      have distinct : other ≠ stage := by
        intro equal
        subst other
        have cursor := live.2
        omega
      have frame : (reportedWriteLedger C state stage bit).written other = state.ledger.written other := by
        simp only [reportedWriteLedger]
        split_ifs; simp only [writeLedger, Function.update_of_ne distinct]
      have oldWrong : state.ledger.written other = some (!state.ledger.truth other) := by
        change (reportedWriteLedger C state stage bit).written other =
          some (!(reportedWriteLedger C state stage bit).truth other) at wrong
        rwa [frame, reportedWriteLedger_truth] at wrong
      obtain ⟨execution, member, equalStage⟩ := ih other past oldWrong
      refine ⟨execution, ?_, equalStage⟩
      change execution ∈ (reportedWriteLedger C state stage bit).executions
      simp only [reportedWriteLedger]
      split_ifs; exact member
    | advance stage live written resources =>
      intro other past wrong
      change other.val < state.cursor + 1 at past
      change state.ledger.written other = some (!state.ledger.truth other) at wrong
      by_cases before : other.val < state.cursor
      · exact ih other before wrong
      · have equalStage : other = stage := by
          apply Fin.ext
          have cursor := live.2
          omega
        subst other
        obtain ⟨execution, member, hstage, _time⟩ := prefix_advance_wrong_has_execution
          P order r limit C early accounting seed truth tapes earlier stage haction wrong
        exact ⟨execution, member, hstage⟩
    | allocate => exact ih
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro stage past wrong
      obtain ⟨execution, member, equalStage⟩ := ih stage past wrong
      exact ⟨execution, List.mem_append_left _ member, equalStage⟩
    | stop => exact ih
    | abandon => exact ih

theorem prefix_terminal_errorsExecuted (P : PaperProofs.Star.Parameters) (order : Order)
    (r : ℝ) (limit : Option ℕ) (C : Contract (starInstance P.tools order))
    (early : C.reporting = .early) (accounting : NormalAccounting (starInstance P.tools order))
    {Seed : Type*} (seed : Seed) (truth : (starInstance P.tools order).Stage → Bool)
    (tapes : ReviewTapes (P.input order)) {n : ℕ} {state : State (starInstance P.tools order)}
    (path : Prefix (P.input order) C .uncapped accounting (P.starReferenceRule order .current r limit)
      seed truth tapes n state) (terminal : state.cursor = (starInstance P.tools order).stageCount) :
    ∀ stage : (starInstance P.tools order).Stage,
      state.ledger.written stage = some (!state.ledger.truth stage) →
        ∃ execution ∈ state.ledger.executions, execution.handle.stage = stage := by
  intro stage wrong
  apply prefix_pastErrorsExecuted P order r limit C early accounting seed truth tapes path stage _ wrong
  rw [terminal]
  exact stage.isLt

end PaperProofs.Star.PStarCurrentPastExecution009
