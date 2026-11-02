module

public import PaperProofs.Paid.PDROC_FirstFailure_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- All physical rights are committed elsewhere; no existing commitment or
execution can repair the wrong ordinary output at this stage. -/
def ExhaustedUnrepairedError (s : State I) (stage : I.Stage) : Prop :=
  s.ledger.written stage = some (!s.ledger.truth stage) ∧
    (∀ execution ∈ s.ledger.executions, execution.handle.stage ≠ stage) ∧
    (∀ commitment ∈ s.ledger.commitments, commitment.handle.stage ≠ stage) ∧
    ∀ tool : I.Tool, ∃ commitment ∈ s.ledger.commitments, commitment.tool = tool

theorem exhaustedUnrepairedError_step (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    {s next : State I} {action : Action I} {stage : I.Stage}
    (hp : ExhaustedUnrepairedError s stage)
    (hs : Step input C .uncapped accounting tapes s action next) : ExhaustedUnrepairedError next stage := by
  rcases hp with ⟨hwritten, hexecution, hcommitment, hall⟩
  cases hs with
  | review => exact ⟨hwritten, hexecution, hcommitment, hall⟩
  | write current bit live port resources =>
    have hne : stage ≠ current := by
      intro heq
      subst current
      rw [hwritten] at port
      contradiction
    have hfields : (reportedWriteLedger C s current bit).written stage = s.ledger.written stage ∧
        (reportedWriteLedger C s current bit).truth = s.ledger.truth ∧
        (reportedWriteLedger C s current bit).executions = s.ledger.executions ∧
        (reportedWriteLedger C s current bit).commitments = s.ledger.commitments := by
      classical
      simp only [reportedWriteLedger]
      split_ifs <;> simp only [writeLedger, Function.update_of_ne hne, and_self]
    exact ⟨by simpa only [record, hfields.1, hfields.2.1] using hwritten,
      by simpa only [record, hfields.2.2.1] using hexecution,
      by simpa only [record, hfields.2.2.2] using hcommitment,
      by simpa only [record, hfields.2.2.2] using hall⟩
  | allocate handle tool active valid compatible unused unallocated window resources =>
    obtain ⟨old, hold, htool⟩ := hall tool
    exact False.elim (unused old hold htool)
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    have hhandle : handle.stage ≠ stage := by
      obtain ⟨old, hold, hhandle, _⟩ := committed
      simpa only [hhandle] using hcommitment old hold
    refine ⟨hwritten, ?_, hcommitment, hall⟩
    intro execution he
    simp only [record, executeLedger, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hexecution execution he
    · exact hhandle
  | advance => exact ⟨hwritten, hexecution, hcommitment, hall⟩
  | stop => exact ⟨hwritten, hexecution, hcommitment, hall⟩
  | abandon => exact ⟨hwritten, hexecution, hcommitment, hall⟩

theorem exhaustedUnrepairedError_not_success (C : Contract I) {s : State I} {stage : I.Stage}
    (hp : ExhaustedUnrepairedError s stage) : ¬ s.ledger.success C := by
  rintro ⟨_, _, _, correct⟩
  rcases correct stage with hcorrect | ⟨execution, he, hstage⟩
  · rw [hp.1] at hcorrect
    cases hx : s.ledger.truth stage <;> simp [hx] at hcorrect
  · exact hp.2.1 execution he hstage

theorem exhaustedUnrepairedError_permanentlyFailed (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (world : input.World) {s : State I} {stage : I.Stage}
    (hp : ExhaustedUnrepairedError s stage) : PermanentlyFailed input C accounting world s := by
  rintro ⟨final, reachable, hhalt, hsuccess⟩
  have hfinal : ExhaustedUnrepairedError final stage := by
    clear hhalt hsuccess
    induction reachable with
    | refl => exact hp
    | tail _ edge ih =>
      obtain ⟨action, hs⟩ := edge
      exact exhaustedUnrepairedError_step input C accounting (worldTapes input world) ih hs
  exact exhaustedUnrepairedError_not_success C hfinal hsuccess

/-- Finite visible detector; all quantifiers range over finite tools/stages
or recorded lists, and no future truth or tape enters the private seed. -/
def exhaustedUnrepairedDetector (history : List (VisibleEvent I)) : Bool :=
  decide (∃ stage : I.Stage, reportedWriteError history stage = some true ∧
    (∀ execution ∈ historyExecutions history, execution.1.stage ≠ stage) ∧
    (∀ commitment ∈ historyCommitments history, commitment.1.stage ≠ stage) ∧
    ∀ tool : I.Tool, tool ∈ historyUsed history)

theorem exhaustedUnrepairedDetector_prefix_iff (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed truth tapes n s) :
    exhaustedUnrepairedDetector s.history = true ↔ ∃ stage, ExhaustedUnrepairedError s stage := by
  simp only [exhaustedUnrepairedDetector, decide_eq_true_eq]
  rw [prefix_historyExecutions input C mode accounting source seed truth tapes hp,
    prefix_historyCommitments input C mode accounting source seed truth tapes hp,
    prefix_historyUsed input C mode accounting source seed truth tapes hp]
  simp only [reportedWriteError_prefix_iff input C hearly mode accounting source seed truth tapes hp,
    List.mem_toFinset, List.mem_map]
  constructor
  · rintro ⟨stage, hw, he, hc, hall⟩
    refine ⟨stage, hw, ?_, ?_, hall⟩
    · intro execution hex
      exact he (execution.handle, execution.tool) ⟨execution, hex, rfl⟩
    · intro commitment hcx
      exact hc (commitment.handle, commitment.tool) ⟨commitment, hcx, rfl⟩
  · rintro ⟨stage, hw, he, hc, hall⟩
    refine ⟨stage, hw, ?_, ?_, hall⟩
    · intro pair hp
      obtain ⟨execution, hex, rfl⟩ := hp
      exact he execution hex
    · intro pair hp
      obtain ⟨commitment, hcx, rfl⟩ := hp
      exact hc commitment hcx

theorem exhaustedUnrepairedDetector_sound (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed truth tapes n s)
    (world : input.World) (hd : exhaustedUnrepairedDetector s.history = true) :
    PermanentlyFailed input C accounting world s := by
  obtain ⟨stage, hstage⟩ := (exhaustedUnrepairedDetector_prefix_iff input C hearly mode accounting source seed truth tapes hp).mp hd
  exact exhaustedUnrepairedError_permanentlyFailed input C accounting world hstage



/-- Proven visible part of permanent failure: missed current-payment
repair windows or every physical right already committed elsewhere. -/
def missedOrExhaustedDetector (history : List (VisibleEvent I)) : Bool :=
  pastUnrepairedDetector history || exhaustedUnrepairedDetector history

theorem missedOrExhaustedDetector_sound (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed truth tapes n s)
    (world : input.World) (hd : missedOrExhaustedDetector s.history = true) :
    PermanentlyFailed input C accounting world s := by
  have hor : pastUnrepairedDetector s.history = true ∨ exhaustedUnrepairedDetector s.history = true := by
    simpa only [missedOrExhaustedDetector, Bool.or_eq_true_eq_eq_true_or_eq_true] using hd
  rcases hor with hpast | hexhausted
  · exact pastUnrepairedDetector_sound input C hpay mode accounting source seed truth tapes hp world hpast
  · exact exhaustedUnrepairedDetector_sound input C hpay.1.1 mode accounting source seed truth tapes hp world hexhausted

theorem missedOrExhaustedStop_preserves_success {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hpay : C.IsCurrentPayment)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : Policy input C mode accounting Seed) (sample : Seed × input.World) :
    runSuccess input C .uncapped accounting
      (detectedStopPolicy input C .uncapped accounting missedOrExhaustedDetector
        (uncappedSourcePolicy input C mode accounting source)).rule sample ↔
      runSuccess input C mode accounting source.rule sample := by
  let relaxed := uncappedSourcePolicy input C mode accounting source
  have hsound : ∀ (sample : Seed × input.World) (n : ℕ),
      missedOrExhaustedDetector (run input C .uncapped accounting relaxed.rule sample n).history = true →
        PermanentlyFailed input C accounting sample.2 (run input C .uncapped accounting relaxed.rule sample n) := by
    intro sample n hd
    obtain ⟨k, _, hp⟩ := run_has_prefix input C .uncapped accounting relaxed.rule relaxed.legal sample n
    exact missedOrExhaustedDetector_sound input C hpay .uncapped accounting relaxed.rule sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp sample.2 hd
  have h := detectedStop_runSuccess_iff_of_sound input C accounting missedOrExhaustedDetector relaxed.rule relaxed.legal hsound sample
  simpa only [relaxed, detectedStopPolicy, runSuccess, uncappedSourcePolicy_run] using h

end PDROC

