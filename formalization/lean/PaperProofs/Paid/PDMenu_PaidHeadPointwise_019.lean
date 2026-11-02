module

public import PaperProofs.Paid.PDMenu_PaidBranchCharge_018

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

set_option maxHeartbeats 1200000 in
theorem paidHeadThen_wrong_noTool_penaltyCharge_eq {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head)
    (penalty : ℝ≥0∞) :
    runPaidPenaltyCharge input C accounting
      (paidHeadThenRule input head test available (bellmanPostHeadRaw input head none good bad)) penalty sample =
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) + penalty := by
  classical
  let after := bellmanPostHeadRaw input head none good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head none good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 2) = stopState written true :=
    paidHeadThen_run_wrong_noTool input C hearly hcurrent hpayment accounting head hhead test available
      good bad hgood hbad sample n hstop hwrong
  have hhalt : (run input C .uncapped accounting policy.val.rule sample (n + 2)).halted = true := by
    rw [hr]
    rfl
  have habandon : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.abandoned = true := by
    rw [hr]
    rfl
  have hfailure := bellmanRun_not_success_of_abandoned_halt input C .uncapped accounting policy.val.rule
    sample (n + 2) hhalt habandon
  have hbill : runActualBill input C .uncapped accounting policy.val.rule sample =
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) := by
    rw [runActualBill_of_halted input C .uncapped accounting policy.val.rule sample (n + 2) hhalt, hr, hstop]
    have he := (bellmanHeadWrittenState_empty_corrections input C hearly accounting head
      (input.truthAt sample.2) (worldTapes input sample.2 head) n
      (test.rule.decision sample.1 (worldTapes input sample.2 head))).2
    change written.ledger.executions = [] at he
    change written.ledger.observationBill input.fees + written.ledger.correctionBill input.fees = _
    have hzero : written.ledger.correctionBill input.fees = 0 := by
      simp only [Ledger.correctionBill, he, List.map_nil, List.sum_nil]
    rw [hzero, add_zero]
    simpa only [written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly,
      ↓reduceIte, writeLedger, Ledger.observationBill] using
      bellmanHeadReviewState_observationBill input accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n
  change runActualBill input C .uncapped accounting policy.val.rule sample +
    (if runSuccess input C .uncapped accounting policy.val.rule sample then 0 else penalty) = _
  rw [hbill, ite_eq_right hfailure]

theorem paidHeadThen_someTool_penaltyCharge_le {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Seed)
    (bad : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) (available.erase tool) Seed)
    (sample : Seed × input.World) (penalty : ℝ≥0∞) :
    runPaidPenaltyCharge input C accounting
      (paidHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good.val.rule bad.val.rule)) penalty sample ≤
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
        (if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
          runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
            (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule penalty
            (sample.1, referenceSuffixWorld input 1 sample.2)
        else ENNReal.ofReal (input.fees.correction head tool : ℝ) +
          runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule penalty
          (sample.1, referenceSuffixWorld input 1 sample.2)) := by
  classical
  by_cases htop : test.rule.stop sample.1 (worldTapes input sample.2 head) = ⊤
  · simp only [htop, PaperProofs.Statistics.BinaryExperiment.observationCharge_top, top_add, le_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  by_cases hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
  · rw [ite_eq_left hcorrect]
    exact paidHeadThen_correct_penaltyCharge_le input C hearly hcurrent hpayment accounting head hhead test available
      (some tool) good bad.val.rule bad.val.measurable_rule sample n hn.symm hcorrect penalty
  · rw [ite_eq_right hcorrect]
    simpa only [add_assoc] using paidHeadThen_wrong_penaltyCharge_le input C hearly hcurrent hpayment accounting head hhead test available
      tool htool heligible good.val.rule good.val.measurable_rule bad sample n hn.symm hcorrect penalty

theorem paidHeadThen_noTool_penaltyCharge_le {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Seed)
    (bad : PolicyRule (I.freshSuffix 1) Seed) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (penalty : ℝ≥0∞) :
    runPaidPenaltyCharge input C accounting
      (paidHeadThenRule input head test available (bellmanPostHeadRaw input head none good.val.rule bad)) penalty sample ≤
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
        (if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
          runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
            (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule penalty
            (sample.1, referenceSuffixWorld input 1 sample.2)
        else penalty) := by
  classical
  by_cases htop : test.rule.stop sample.1 (worldTapes input sample.2 head) = ⊤
  · simp only [htop, PaperProofs.Statistics.BinaryExperiment.observationCharge_top, top_add, le_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  by_cases hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
  · rw [ite_eq_left hcorrect]
    exact paidHeadThen_correct_penaltyCharge_le input C hearly hcurrent hpayment accounting head hhead test available
      none good bad hbad sample n hn.symm hcorrect penalty
  · rw [ite_eq_right hcorrect]
    exact (paidHeadThen_wrong_noTool_penaltyCharge_eq input C hearly hcurrent hpayment accounting head hhead test available
      good.val.rule bad good.val.measurable_rule hbad sample n hn.symm hcorrect penalty).le


end PDMenu
