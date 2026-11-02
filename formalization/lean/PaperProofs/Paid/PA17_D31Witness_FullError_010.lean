module

public import PaperProofs.Paid.PA17_D31Witness_Completion_009
public import PaperProofs.Common.NativeHeadContinuation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Paid.PA17D31WitnessFullError010

open Common Common.Native MeasureTheory PA17D31Witness001 PA17D31WitnessPath007
open PA17D31WitnessPolicy008 PA17D31WitnessCompletion009

theorem terminal_allReportsWrong_iff (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C mode accounting rule seed truth tapes n s)
    (hcursor : s.cursor = P.certificate.stages) :
    allReportsWrong P s.history ↔ ∀ stage, truth stage = true := by
  have hreport (stage : P.sharedInstance.Stage) :
      (historyReport s.history stage).map Prod.fst = some (truth stage) := by
    have hw : s.ledger.written stage ≠ none := by
      apply prefix_written_before_cursor (P.input fee hfee) C mode accounting
        rule seed truth tapes hp stage
      rw [hcursor]
      exact stage_lt_stages P stage
    obtain ⟨time, ht⟩ := prefix_early_written_reported (P.input fee hfee) C hearly
      mode accounting rule seed truth tapes hp stage hw
    rw [prefix_historyReport_early (P.input fee hfee) C hearly mode accounting
      rule seed truth tapes hp stage, ht]
    change some (s.ledger.truth stage) = some (truth stage)
    rw [prefix_truth (P.input fee hfee) C mode accounting rule seed truth tapes hp]
  unfold allReportsWrong
  constructor
  · intro hwrong stage
    have hs := hwrong stage
    rw [hreport] at hs
    exact Option.some.inj hs
  · intro htruth stage
    rw [hreport, htruth stage]

theorem blindCandidate_execute_terminal (P : Parameters) (seed : Unit)
    (history : List (VisibleEvent P.sharedInstance))
    (handle : MismatchHandle P.sharedInstance) (tool : P.sharedInstance.Tool)
    (ha : blindCandidate P seed history = .execute handle tool) :
    historyCursor history = P.certificate.stages ∧ ¬ allReportsWrong P history := by
  unfold blindCandidate at ha
  split at ha
  · cases ha
  · split at ha
    · dsimp only at ha
      split at ha
      · cases ha
      · split at ha
        · split at ha <;> cases ha
        · cases ha
    · split at ha
      · rename_i hcursor
        split at ha
        · cases ha
        · rename_i hnot
          exact ⟨hcursor, hnot⟩
      · cases ha

theorem blindCandidate_no_execute_of_fullTruth (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : Contract P.sharedInstance) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting P.sharedInstance) {Seed : Type*}
    (rule : PolicyRule P.sharedInstance Seed) (seed : Seed)
    (truth : P.sharedInstance.Stage → Bool) (tapes : ReviewTapes (P.input fee hfee))
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) C mode accounting rule seed truth tapes n s)
    (htruth : ∀ stage, truth stage = true) (rawSeed : Unit)
    (handle : MismatchHandle P.sharedInstance) (tool : P.sharedInstance.Tool) :
    blindCandidate P rawSeed s.history ≠ .execute handle tool := by
  intro ha
  obtain ⟨hc, hnot⟩ := blindCandidate_execute_terminal P rawSeed s.history handle tool ha
  have hcursor : s.cursor = P.certificate.stages := by
    rwa [prefix_historyCursor (P.input fee hfee) C mode accounting rule seed truth tapes hp] at hc
  exact hnot ((terminal_allReportsWrong_iff P fee hfee C hearly mode accounting
    rule seed truth tapes hp hcursor).mpr htruth)

theorem nativePolicy_prefix_executions_nil (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (seed : Unit) (truth : P.sharedInstance.Stage → Bool)
    (tapes : ReviewTapes (P.input fee hfee)) (htruth : ∀ stage, truth stage = true)
    {n : ℕ} {s : State P.sharedInstance}
    (hp : Prefix (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes n s) :
    s.ledger.executions = [] := by
  induction hp with
  | initial => rfl
  | @next n s next earlier hs ih =>
    have hm := nativeRule_nonbinding P fee hfee allocation seed truth tapes earlier
    generalize ha : blindRule P seed s.history = action at hs
    cases hs with
    | execute handle tool =>
      exact (blindCandidate_no_execute_of_fullTruth P fee hfee
        (P.retainedPaymentExampleContract allocation) rfl .native
        (blindCallAccounting P.sharedInstance) (blindRule P) seed truth tapes earlier
        htruth seed handle tool (hm.symm.trans ha)).elim
    | write =>
      classical
      simp only [record, reportedWriteLedger]
      split_ifs <;> exact ih
    | review | allocate | advance | stop | abandon => exact ih

theorem nativePolicy_run_executions_nil (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (sample : Unit × (P.input fee hfee).World)
    (htruth : ∀ stage, (P.input fee hfee).truthAt sample.2 stage = true) (n : ℕ) :
    (run (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule sample n).ledger.executions = [] := by
  obtain ⟨_, _, hp⟩ := run_has_prefix (P.input fee hfee)
    (P.retainedPaymentExampleContract allocation) .native (blindCallAccounting P.sharedInstance)
    (nativePolicy P fee hfee allocation).rule (nativePolicy P fee hfee allocation).legal sample n
  exact nativePolicy_prefix_executions_nil P fee hfee allocation sample.1 _ _ htruth hp

theorem nativePolicy_fullTruth_runRepairCount_zero (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (allocation : Deadline) (sample : Unit × (P.input fee hfee).World)
    (htruth : ∀ stage, (P.input fee hfee).truthAt sample.2 stage = true) :
    runRepairCount (P.input fee hfee) (P.retainedPaymentExampleContract allocation) .native
      (blindCallAccounting P.sharedInstance) (nativePolicy P fee hfee allocation).rule sample = 0 := by
  simp only [runRepairCount, nativePolicy_run_executions_nil P fee hfee allocation sample htruth,
    List.length_nil, Nat.cast_zero, iSup_const]

end PaperProofs.Paid.PA17D31WitnessFullError010
