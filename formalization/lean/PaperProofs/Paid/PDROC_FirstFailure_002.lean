module

public import PaperProofs.Paid.PDROC_FirstFailure_001
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

variable {I : Instance}

/-- An actual unexecuted wrong ordinary write strictly behind the physical cursor. -/
def PastUnrepairedError (s : State I) (stage : I.Stage) : Prop :=
  stage.val < s.cursor ∧ s.ledger.written stage = some (!s.ledger.truth stage) ∧
    ∀ execution ∈ s.ledger.executions, execution.handle.stage ≠ stage

theorem pastUnrepairedError_step (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.execution = .currentWindow) (accounting : NormalAccounting I)
    (tapes : ReviewTapes input) {s next : State I} {action : Action I} {stage : I.Stage}
    (hp : PastUnrepairedError s stage)
    (hs : Step input C .uncapped accounting tapes s action next) : PastUnrepairedError next stage := by
  rcases hp with ⟨hcursor, hwritten, hexecution⟩
  cases hs with
  | review => exact ⟨hcursor, hwritten, hexecution⟩
  | write current bit live port resources =>
    have hc : s.cursor = current.val := live.2
    have hne : stage ≠ current := by intro heq; rw [← heq] at hc; omega
    have hfields : (reportedWriteLedger C s current bit).written stage = s.ledger.written stage ∧
        (reportedWriteLedger C s current bit).truth = s.ledger.truth ∧
        (reportedWriteLedger C s current bit).executions = s.ledger.executions := by
      classical
      simp only [reportedWriteLedger]
      split_ifs <;> simp only [writeLedger, Function.update_of_ne hne, and_self]
    exact ⟨hcursor, by simpa only [record, hfields.1, hfields.2.1] using hwritten,
      by simpa only [record, hfields.2.2] using hexecution⟩
  | allocate => exact ⟨hcursor, hwritten, hexecution⟩
  | execute handle tool active valid compatible committed unused uncorrected window resources =>
    refine ⟨hcursor, hwritten, ?_⟩
    intro execution he
    simp only [record, executeLedger, List.mem_append, List.mem_singleton] at he
    rcases he with he | rfl
    · exact hexecution execution he
    · have hc := window hcurrent
      intro heq
      simp only at heq
      rw [heq] at hc
      omega
  | advance => exact ⟨Nat.lt_succ_of_lt hcursor, hwritten, hexecution⟩
  | stop => exact ⟨hcursor, hwritten, hexecution⟩
  | abandon => exact ⟨hcursor, hwritten, hexecution⟩

theorem pastUnrepairedError_not_success (C : Contract I) {s : State I} {stage : I.Stage}
    (hp : PastUnrepairedError s stage) : ¬ s.ledger.success C := by
  rintro ⟨_, _, _, correct⟩
  rcases correct stage with hcorrect | ⟨execution, he, hstage⟩
  · rw [hp.2.1] at hcorrect
    cases hx : s.ledger.truth stage <;> simp [hx] at hcorrect
  · exact hp.2.2 execution he hstage

theorem pastUnrepairedError_permanentlyFailed (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.execution = .currentWindow) (accounting : NormalAccounting I)
    (world : input.World) {s : State I} {stage : I.Stage}
    (hp : PastUnrepairedError s stage) : PermanentlyFailed input C accounting world s := by
  rintro ⟨final, reachable, hhalt, hsuccess⟩
  have hfinal : PastUnrepairedError final stage := by
    clear hhalt hsuccess
    induction reachable with
    | refl => exact hp
    | tail _ edge ih =>
      obtain ⟨action, hs⟩ := edge
      exact pastUnrepairedError_step input C hcurrent accounting (worldTapes input world) ih hs
  exact pastUnrepairedError_not_success C hfinal hsuccess

/-- A genuine finite visible detector of missed physical corrections.
It reads only the public cursor, original reports, writes and executions. -/
def pastUnrepairedDetector (history : List (VisibleEvent I)) : Bool :=
  decide (∃ stage : I.Stage, stage.val < historyCursor history ∧
    reportedWriteError history stage = some true ∧
    ∀ execution ∈ historyExecutions history, execution.1.stage ≠ stage)

theorem reportedWriteError_prefix_iff (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed truth tapes n s) (stage : I.Stage) :
    reportedWriteError s.history stage = some true ↔
      s.ledger.written stage = some (!s.ledger.truth stage) := by
  have hw := prefix_historyWrite input C mode accounting source seed truth tapes hp stage
  have hr := prefix_historyReport_early input C hearly mode accounting source seed truth tapes hp stage
  unfold reportedWriteError
  rw [hw, hr]
  cases hwrite : s.ledger.written stage with
  | none => simp
  | some bit =>
    obtain ⟨time, ht⟩ := prefix_early_written_reported input C hearly mode accounting source seed truth tapes hp stage (by simp [hwrite])
    rw [ht]
    cases bit <;> cases hx : s.ledger.truth stage <;> simp

theorem pastUnrepairedDetector_prefix_iff (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed truth tapes n s) :
    pastUnrepairedDetector s.history = true ↔ ∃ stage, PastUnrepairedError s stage := by
  simp only [pastUnrepairedDetector, decide_eq_true_eq]
  rw [prefix_historyCursor input C mode accounting source seed truth tapes hp,
    prefix_historyExecutions input C mode accounting source seed truth tapes hp]
  simp only [reportedWriteError_prefix_iff input C hearly mode accounting source seed truth tapes hp]
  constructor
  · rintro ⟨stage, hc, hw, he⟩
    refine ⟨stage, hc, hw, ?_⟩
    intro execution hex
    exact he (execution.handle, execution.tool) (List.mem_map.mpr ⟨execution, hex, rfl⟩)
  · rintro ⟨stage, hc, hw, he⟩
    refine ⟨stage, hc, hw, ?_⟩
    intro pair hp
    obtain ⟨execution, hex, rfl⟩ := List.mem_map.mp hp
    exact he execution hex

theorem pastUnrepairedDetector_sound (input : StatisticalInput I) (C : Contract I)
    (hpay : C.IsCurrentPayment) (mode : ResourceMode) (accounting : NormalAccounting I)
    {Seed : Type*} (source : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting source seed truth tapes n s)
    (world : input.World) (hd : pastUnrepairedDetector s.history = true) :
    PermanentlyFailed input C accounting world s := by
  obtain ⟨stage, hstage⟩ := (pastUnrepairedDetector_prefix_iff input C hpay.1.1 mode accounting source seed truth tapes hp).mp hd
  exact pastUnrepairedError_permanentlyFailed input C hpay.2 accounting world hstage




/-- A proved visible truncation of every original current-payment policy.
This stops at past missed repairs only; full first-permanent-failure timing
also requires the separate current-stage exhaustion/halting cases. -/
theorem pastUnrepairedStop_preserves_success {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hpay : C.IsCurrentPayment)
    (mode : ResourceMode) (accounting : NormalAccounting I)
    (source : Policy input C mode accounting Seed) (sample : Seed × input.World) :
    runSuccess input C .uncapped accounting
      (detectedStopPolicy input C .uncapped accounting pastUnrepairedDetector
        (uncappedSourcePolicy input C mode accounting source)).rule sample ↔
      runSuccess input C mode accounting source.rule sample := by
  let relaxed := uncappedSourcePolicy input C mode accounting source
  have hsound : ∀ (sample : Seed × input.World) (n : ℕ),
      pastUnrepairedDetector (run input C .uncapped accounting relaxed.rule sample n).history = true →
        PermanentlyFailed input C accounting sample.2 (run input C .uncapped accounting relaxed.rule sample n) := by
    intro sample n hd
    obtain ⟨k, _, hp⟩ := run_has_prefix input C .uncapped accounting relaxed.rule relaxed.legal sample n
    exact pastUnrepairedDetector_sound input C hpay .uncapped accounting relaxed.rule sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp sample.2 hd
  have h := detectedStop_runSuccess_iff_of_sound input C accounting pastUnrepairedDetector relaxed.rule relaxed.legal hsound sample
  simpa only [relaxed, detectedStopPolicy, runSuccess, uncappedSourcePolicy_run] using h

theorem pastUnrepairedStop_allBills_le {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (source : Policy input C mode accounting Seed)
    (sample : Seed × input.World) :
    let stopped := detectedStopPolicy input C .uncapped accounting pastUnrepairedDetector
      (uncappedSourcePolicy input C mode accounting source)
    runObservationBill input C .uncapped accounting stopped.rule sample ≤
        runObservationBill input C mode accounting source.rule sample ∧
      runActualBill input C .uncapped accounting stopped.rule sample ≤
        runActualBill input C mode accounting source.rule sample := by
  constructor
  · have h := detectedStop_runObservationBill_le input C .uncapped accounting pastUnrepairedDetector
      (uncappedSourcePolicy input C mode accounting source).rule sample
    simpa only [detectedStopPolicy, runObservationBill, uncappedSourcePolicy_run] using h
  · have h := detectedStop_runActualBill_le input C .uncapped accounting pastUnrepairedDetector
      (uncappedSourcePolicy input C mode accounting source).rule sample
    simpa only [detectedStopPolicy, runActualBill, uncappedSourcePolicy_run] using h

end PDROC

