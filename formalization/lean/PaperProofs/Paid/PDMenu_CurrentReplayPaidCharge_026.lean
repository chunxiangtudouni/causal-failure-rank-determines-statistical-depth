module

public import PaperProofs.Paid.PDMenu_CurrentReplayFacts_024
public import PaperProofs.Paid.PDMenu_CurrentReplayFees_025
public import PaperProofs.Paid.PDMenu_SuffixActualCharge_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance} {Seed : Type*}

theorem step_execution_preserved (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input) {source next : State I} {action : Action I}
    (hs : Step input C mode accounting tapes source action next) (e : Execution I)
    (he : e ∈ source.ledger.executions) : e ∈ next.ledger.executions := by
  cases hs with
  | write =>
    classical
    simp only [record, reportedWriteLedger]
    split_ifs <;> exact he
  | execute => exact List.mem_append_left _ he
  | review | allocate | advance | stop | abandon => exact he

theorem run_execution_preserved (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (start extra : ℕ) (e : Execution I)
    (he : e ∈ (run input C mode accounting rule sample start).ledger.executions) :
    e ∈ (run input C mode accounting rule sample (start + extra)).ledger.executions := by
  induction extra with
  | zero => exact he
  | succ extra ih =>
    by_cases hh : (run input C mode accounting rule sample (start + extra)).halted = true
    · rw [Nat.add_succ, run_succ_of_halted input C mode accounting rule sample (start + extra) hh]
      exact ih
    · have ha := Bool.eq_false_iff.mpr hh
      obtain ⟨n, _, hp⟩ := run_has_prefix input C mode accounting rule hlegal sample (start + extra)
      obtain ⟨next, hs⟩ := hlegal sample.1 _ _ n _ hp ha
      rw [Nat.add_succ, run_succ_of_step input C mode accounting rule sample (start + extra) next ha hs]
      exact step_execution_preserved input C mode accounting _ hs e ih

theorem paidReplay_runActualBill_le (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule first start sample)
    (fee : ℚ) (hfee : ∀ stage tool, input.fees.correction stage tool = fee) :
    let startup := publicStartup (run input C .uncapped accounting rule sample start)
    let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
      runActualBill (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) ≤
      runActualBill input C .uncapped accounting rule sample := by
  let startup := publicStartup (run input C .uncapped accounting rule sample start)
  let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
    (replayedSuffixCandidate first accounting rule startup)
  let targetSample := (sample.1, input.restrictFreshWorld first sample.2)
  let targetAt := fun k => run (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k
  have htargetLegal : LegalRule (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule := paidGuardedRule_legal _ _ rfl _ _ _
  change (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
    (⨆ k, (targetAt k).ledger.actualBill (input.freshSuffix first).fees) ≤ _
  rw [ENNReal.add_iSup]
  apply iSup_le
  intro k
  let clock := replaySourceClock input C .uncapped accounting rule sample first start k
  have hclock : start ≤ clock := replaySourceClock_ge_start input C .uncapped accounting rule sample first start k
  have hview := (paidReplayedSuffix_fullRun input C hC.1.1 hC.1.2 hC.2 .uncapped accounting rule hlegal sample
    first start hentry k).1
  have hsource := run_ledgerWellFormed input C .uncapped accounting rule hlegal sample clock
  have htarget := run_ledgerWellFormed (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
    .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule htargetLegal targetSample k
  have hcorr := correctionBill_le_of_historySuffix input first hview hsource htarget fee hfee
  have hobs := paidReplayedSuffix_prefix_observationBill input C hC.1.1 hC.1.2 hC.2 .uncapped accounting rule hlegal
    sample first start hentry k
  have hsplit := observationBill_eq_prefix_add_increment input
    (run input C .uncapped accounting rule sample start) (run input C .uncapped accounting rule sample clock)
    (fun stage => run_reviews_mono input C .uncapped accounting rule hlegal sample stage hclock)
  calc
    _ ≤ (run input C .uncapped accounting rule sample clock).ledger.actualBill input.fees := by
      unfold Ledger.actualBill
      rw [hsplit, add_assoc]
      rw [hobs]
      exact add_le_add le_rfl (add_le_add le_rfl hcorr)
    _ ≤ _ := prefixBill_le_runActualBill input C .uncapped accounting rule sample clock

theorem paidReplay_runPaidPenaltyCharge_le (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule first start sample)
    (fee : ℚ) (hfee : ∀ stage tool, input.fees.correction stage tool = fee) (penalty : ℝ≥0∞) :
    let startup := publicStartup (run input C .uncapped accounting rule sample start)
    let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
      runPaidPenaltyCharge (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
        (zeroNormalAccounting (I.freshSuffix first)) targetRule penalty (sample.1, input.restrictFreshWorld first sample.2) ≤
      runPaidPenaltyCharge input C accounting rule penalty sample := by
  classical
  let startup := publicStartup (run input C .uncapped accounting rule sample start)
  let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
    (replayedSuffixCandidate first accounting rule startup)
  change _ + runPaidPenaltyCharge _ _ _ targetRule penalty _ ≤ _
  unfold runPaidPenaltyCharge
  rw [← add_assoc]
  apply add_le_add (paidReplay_runActualBill_le input C hC accounting rule hlegal sample first start hentry fee hfee)
  by_cases hs : runSuccess input C .uncapped accounting rule sample
  · have ht : runSuccess (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) :=
      paidReplayedSuffix_runSuccess input C hC.1.1 hC.1.2 hC.2 .uncapped accounting rule hlegal
        sample first start hentry hs
    simp only [hs, ht, ite_true, le_refl]
  · rw [ite_eq_right hs]
    split_ifs <;> simp

theorem paidReplay_withHead_runActualBill_le (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule first start sample)
    (fee : ℚ) (hfee : ∀ stage tool, input.fees.correction stage tool = fee)
    (e : Execution I) (he : e ∈ (run input C .uncapped accounting rule sample start).ledger.executions)
    (hold : e.handle.stage.val < first) :
    let startup := publicStartup (run input C .uncapped accounting rule sample start)
    let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees + ENNReal.ofReal (fee : ℝ) +
      runActualBill (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) ≤
      runActualBill input C .uncapped accounting rule sample := by
  let startup := publicStartup (run input C .uncapped accounting rule sample start)
  let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
    (replayedSuffixCandidate first accounting rule startup)
  let targetSample := (sample.1, input.restrictFreshWorld first sample.2)
  let targetAt := fun k => run (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) targetRule targetSample k
  have htargetLegal : LegalRule (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
      (zeroNormalAccounting (I.freshSuffix first)) targetRule := paidGuardedRule_legal _ _ rfl _ _ _
  change (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees + ENNReal.ofReal (fee : ℝ) +
    (⨆ k, (targetAt k).ledger.actualBill (input.freshSuffix first).fees) ≤ _
  rw [ENNReal.add_iSup]
  apply iSup_le
  intro k
  let clock := replaySourceClock input C .uncapped accounting rule sample first start k
  have hclock : start ≤ clock := replaySourceClock_ge_start input C .uncapped accounting rule sample first start k
  have hview := (paidReplayedSuffix_fullRun input C hC.1.1 hC.1.2 hC.2 .uncapped accounting rule hlegal sample
    first start hentry k).1
  have hsource := run_ledgerWellFormed input C .uncapped accounting rule hlegal sample clock
  have htarget := run_ledgerWellFormed (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
    .uncapped (zeroNormalAccounting (I.freshSuffix first)) targetRule htargetLegal targetSample k
  have heClock : e ∈ (run input C .uncapped accounting rule sample clock).ledger.executions := by
    obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le hclock
    have h := run_execution_preserved input C .uncapped accounting rule hlegal sample start extra e he
    rwa [← heq] at h
  have hcorr := paidHead_add_childCorrectionBill_le input first hview hsource htarget fee hfee e heClock hold
  have hobs := paidReplayedSuffix_prefix_observationBill input C hC.1.1 hC.1.2 hC.2 .uncapped accounting rule hlegal
    sample first start hentry k
  have hsplit := observationBill_eq_prefix_add_increment input
    (run input C .uncapped accounting rule sample start) (run input C .uncapped accounting rule sample clock)
    (fun stage => run_reviews_mono input C .uncapped accounting rule hlegal sample stage hclock)
  calc
    _ ≤ (run input C .uncapped accounting rule sample clock).ledger.actualBill input.fees := by
      unfold Ledger.actualBill
      rw [hsplit]
      rw [hobs]
      calc
        _ = ((run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
            observationIncrement input (run input C .uncapped accounting rule sample start)
              (run input C .uncapped accounting rule sample clock)) +
            (ENNReal.ofReal (fee : ℝ) + (targetAt k).ledger.correctionBill (input.freshSuffix first).fees) := by ac_rfl
        _ ≤ _ := add_le_add le_rfl hcorr
    _ ≤ _ := prefixBill_le_runActualBill input C .uncapped accounting rule sample clock

theorem paidReplay_withHead_runPaidPenaltyCharge_le (input : StatisticalInput I) (C : Contract I)
    (hC : C.IsCurrentPayment) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (first start : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule first start sample)
    (fee : ℚ) (hfee : ∀ stage tool, input.fees.correction stage tool = fee)
    (e : Execution I) (he : e ∈ (run input C .uncapped accounting rule sample start).ledger.executions)
    (hold : e.handle.stage.val < first) (penalty : ℝ≥0∞) :
    let startup := publicStartup (run input C .uncapped accounting rule sample start)
    let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
      (replayedSuffixCandidate first accounting rule startup)
    (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees + ENNReal.ofReal (fee : ℝ) +
      runPaidPenaltyCharge (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first))
        (zeroNormalAccounting (I.freshSuffix first)) targetRule penalty (sample.1, input.restrictFreshWorld first sample.2) ≤
      runPaidPenaltyCharge input C accounting rule penalty sample := by
  classical
  let startup := publicStartup (run input C .uncapped accounting rule sample start)
  let targetRule := paidGuardedRule (I := I.freshSuffix first) startup.availableTools
    (replayedSuffixCandidate first accounting rule startup)
  change _ + runPaidPenaltyCharge _ _ _ targetRule penalty _ ≤ _
  unfold runPaidPenaltyCharge
  rw [← add_assoc]
  apply add_le_add (paidReplay_withHead_runActualBill_le input C hC accounting rule hlegal sample first start hentry fee hfee e he hold)
  by_cases hs : runSuccess input C .uncapped accounting rule sample
  · have ht : runSuccess (input.freshSuffix first) (paidRelaxedContract (I.freshSuffix first)) .uncapped
        (zeroNormalAccounting (I.freshSuffix first)) targetRule (sample.1, input.restrictFreshWorld first sample.2) :=
      paidReplayedSuffix_runSuccess input C hC.1.1 hC.1.2 hC.2 .uncapped accounting rule hlegal
        sample first start hentry hs
    simp only [hs, ht, ite_true, le_refl]
  · rw [ite_eq_right hs]
    split_ifs <;> simp


end PDMenu
