module

public import PaperProofs.Paid.PDLower_BlindCapacity_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native

namespace PDLower

variable {I : Instance}

theorem truthAgrees_update_unwritten (state : State I) (stage : I.Stage) (bit : Bool)
    (unwritten : state.ledger.written stage = none) :
    TruthAgreesOnWritten state (Function.update state.ledger.truth stage bit) := by
  intro other written
  have hne : other ≠ stage := by intro heq; subst other; exact written unwritten
  exact Function.update_of_ne hne _ _

theorem allWrittenWrong_retarget (state : State I) (truth : I.Stage → Bool)
    (agree : TruthAgreesOnWritten state truth) (wrong : AllWrittenWrong state.ledger) :
    AllWrittenWrong (retargetTruth state truth).ledger := by
  intro stage bit written
  change state.ledger.written stage = some bit at written
  have hsame := agree stage (by rw [written]; simp)
  change bit ≠ truth stage
  rw [hsame]
  exact wrong stage bit written

theorem allWrittenWrong_reportedWrite (C : Contract I) (hearly : C.reporting = .early)
    (state : State I) (stage : I.Stage) (bit : Bool)
    (wrong : AllWrittenWrong state.ledger) (hbit : bit ≠ state.ledger.truth stage) :
    AllWrittenWrong (reportedWriteLedger C state stage bit) := by
  intro other otherBit written
  have htruth := reportedWriteLedger_truth C state stage bit
  rw [htruth]
  by_cases heq : other = stage
  · subst other
    have hsame : bit = otherBit := by
      have hw : (reportedWriteLedger C state stage bit).written stage = some bit := by
        simp only [reportedWriteLedger, hearly, ↓reduceIte, writeLedger, Function.update_self]
      exact Option.some.inj (hw.symm.trans written)
    rwa [← hsame]
  · apply wrong other otherBit
    simpa only [reportedWriteLedger, hearly, ↓reduceIte, writeLedger,
      Function.update_of_ne heq] using written

theorem step_allWrittenWrong_of_nonwrite (input : StatisticalInput I) (C : Contract I)
    (mode : ResourceMode) (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {state next : State I} {action : Action I}
    (step : Step input C mode accounting tapes state action next)
    (nonwrite : ∀ stage bit, action ≠ .write stage bit)
    (wrong : AllWrittenWrong state.ledger) : AllWrittenWrong next.ledger := by
  cases step with
  | review | allocate | execute | advance | stop | abandon => exact wrong
  | write stage bit live port resources => exact (nonwrite stage bit rfl).elim

theorem exists_allWrong_prefix (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    {Seed : Type*} (rule : PolicyRule I Seed) (legal : LegalRule input C .native accounting rule)
    (seed : Seed) (tapes : ReviewTapes input) (length : ℕ) :
    ∃ (truth : I.Stage → Bool) (clock : ℕ) (state : State I),
      Prefix input C .native accounting rule seed truth tapes clock state ∧
      AllWrittenWrong state.ledger ∧ (state.halted = true ∨ clock = length) := by
  induction length with
  | zero =>
    refine ⟨fun _ => false, 0, initial (fun _ => false), .initial, ?_, Or.inr rfl⟩
    intro stage bit written
    cases written
  | succ length ih =>
    obtain ⟨truth, clock, state, path, wrong, phase⟩ := ih
    by_cases halted : state.halted = true
    · exact ⟨truth, clock, state, path, wrong, Or.inl halted⟩
    · have active : state.halted = false := Bool.eq_false_iff.mpr halted
      have hclock : clock = length := phase.resolve_left halted
      obtain ⟨next, step⟩ := legal seed truth tapes clock state path active
      by_cases writing : ∃ stage bit, rule seed state.history = .write stage bit
      · obtain ⟨stage, bit, haction⟩ := writing
        have unwritten : state.ledger.written stage = none := by
          have selected := step
          rw [haction] at selected
          cases selected
          assumption
        let truth' := Function.update state.ledger.truth stage (!bit)
        have agrees : TruthAgreesOnWritten state truth' := truthAgrees_update_unwritten state stage (!bit) unwritten
        have path' := prefix_retarget_agree_written input C hearly .native accounting rule seed truth truth' tapes path agrees
        have wrong' := allWrittenWrong_retarget state truth' agrees wrong
        obtain ⟨next', step'⟩ := legal seed truth' tapes clock (retargetTruth state truth') path' active
        have wrongNext : AllWrittenWrong next'.ledger := by
          have selected := step'
          change Step input C .native accounting tapes (retargetTruth state truth')
            (rule seed state.history) next' at selected
          rw [haction] at selected
          cases selected
          apply allWrittenWrong_reportedWrite C hearly (retargetTruth state truth') stage bit wrong'
          change bit ≠ truth' stage
          simp only [truth', Function.update_self]
          cases bit <;> decide
        exact ⟨truth', clock + 1, next', .next path' step', wrongNext, Or.inr (by omega)⟩
      · have nonwrite : ∀ stage bit, rule seed state.history ≠ .write stage bit := by
          intro stage bit heq
          exact writing ⟨stage, bit, heq⟩
        exact ⟨truth, clock + 1, next, .next path step,
          step_allWrittenWrong_of_nonwrite input C .native accounting tapes step nonwrite wrong,
          Or.inr (by omega)⟩

theorem exists_failure_truth (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hshort : I.toolCount < I.stageCount)
    (accounting : NormalAccounting I) {Seed : Type*}
    (rule : PolicyRule I Seed) (legal : LegalRule input C .native accounting rule)
    (seed : Seed) (tapes : ReviewTapes input) :
    ∃ truth : I.Stage → Bool,
      ¬ runSuccess input C .native accounting rule (seed, replayWorld input truth tapes) := by
  obtain ⟨truth, clock, state, path, wrong, phase⟩ :=
    exists_allWrong_prefix input C hearly accounting rule legal seed tapes (nativeActionBound C + 1)
  have halted : state.halted = true := by
    rcases phase with halted | hclock
    · exact halted
    · have hbound := prefix_native_length_le input C accounting rule seed truth tapes path
      omega
  have failure := allWrittenWrong_not_success C state.ledger hshort
    (prefix_ledgerWellFormed input C .native accounting rule seed truth tapes path) wrong
  have hrun := prefix_eq_run input C .native accounting rule seed truth tapes path
  refine ⟨truth, ?_⟩
  rw [runSuccess_iff_success_of_halted input C .native accounting rule
    (seed, replayWorld input truth tapes) clock (by rw [hrun]; exact halted), hrun]
  exact failure

end PDLower
