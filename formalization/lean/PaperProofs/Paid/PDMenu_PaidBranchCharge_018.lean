module

public import PaperProofs.Paid.PDMenu_CurrentContinuationRun_015
public import PaperProofs.Paid.PDMenu_ActualContinuationCharge_016
public import PaperProofs.Common.NativeBellmanChargeUpper

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

set_option maxHeartbeats 1200000 in
theorem paidHeadThen_correct_penaltyCharge_le {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Seed)
    (bad : PolicyRule (I.freshSuffix 1) Seed) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head)
    (penalty : ℝ≥0∞) :
    runPaidPenaltyCharge input C accounting
      (paidHeadThenRule input head test available (bellmanPostHeadRaw input head repair good.val.rule bad)) penalty sample ≤
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
        runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule penalty
          (sample.1, referenceSuffixWorld input 1 sample.2) := by
  let after := bellmanPostHeadRaw input head repair good.val.rule bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good.val.rule bad good.val.measurable_rule hbad)
  let before := (run input C .uncapped accounting policy.val.rule sample (n + 2)).history
  have hentry := paidHeadThen_correct_firstEntry input C hearly hcurrent hpayment accounting head hhead test available
    repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
  have hobs := bellmanEntry_observations_empty input 1 C accounting policy.val.rule policy.val.legal sample (n + 2) hentry
  have hbase := GuardLift.base_of_firstEntry input 1 C hearly accounting policy.val.rule policy.val.legal
    sample (n + 2) hentry available
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 2) =
      record accounting written (.advance head) [.advanced head] (advanceLedger written head) 1 false :=
    paidHeadThen_run_correct_advance input C hearly hcurrent hpayment accounting head hhead test available
      repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 2)
  have hresolved : ∀ stage : I.Stage, stage.val < 1 →
      historyWritten before stage = some (input.truthAt sample.2 stage) ∨
        ∃ pair ∈ historyExecutions before, pair.1.stage = stage := by
    intro stage hs
    have heq : stage = head := Fin.ext (by omega)
    subst stage
    left
    have hw := prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hp head
    have hfield : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.written head =
        some (input.truthAt sample.2 head) := by
      rw [hr]
      exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
          (congrArg some hcorrect)
    exact hw.trans hfield
  have hcount : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.reviews head =
      test.rule.stop sample.1 (worldTapes input sample.2 head) := by
    rw [hr, hstop]
    exact bellmanHeadWrittenState_reviews_eq input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hfee := bellmanPrefix_observationBill_of_entry input C accounting policy.val.rule policy.val.legal
    head hhead test sample (n + 2) hentry hcount
  have hviews := paidHeadThen_correct_run_view input C hearly hcurrent hpayment accounting head hhead test available
    repair good bad hbad sample n hstop hcorrect
  have hcorr : historyCorrectionCharge input before = 0 := by
    change historyCorrectionCharge input (run input C .uncapped accounting policy.val.rule sample (n + 2)).history = 0
    rw [← prefix_correctionBill_eq_historyCharge input C .uncapped accounting policy.val.rule sample.1 _ _ hp, hr]
    have he := (bellmanHeadWrittenState_empty_corrections input C hearly accounting head
      (input.truthAt sample.2) (worldTapes input sample.2 head) n
      (test.rule.decision sample.1 (worldTapes input sample.2 head))).2
    change written.ledger.executions = [] at he
    simp only [record, advanceLedger, Ledger.correctionBill, he, List.map_nil, List.sum_nil]
  have hbound := runPaidPenaltyCharge_suffixRun_le input 1 C accounting policy.val.rule policy.val.legal
    (paidRelaxedContract (I.freshSuffix 1)) (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule good.val.legal
    sample before (n + 2) hobs hviews hearly hbase.written hresolved penalty
  rw [hfee, hcorr, add_zero] at hbound
  exact hbound

set_option maxHeartbeats 1200000 in
theorem paidHeadThen_wrong_penaltyCharge_le {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good : PolicyRule (I.freshSuffix 1) Seed) (hgood : MeasurableRule good)
    (bad : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) (available.erase tool) Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head)
    (penalty : ℝ≥0∞) :
    runPaidPenaltyCharge input C accounting
      (paidHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad.val.rule)) penalty sample ≤
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
        ENNReal.ofReal (input.fees.correction head tool : ℝ) +
        runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule penalty
          (sample.1, referenceSuffixWorld input 1 sample.2) := by
  let after := bellmanPostHeadRaw input head (some tool) good bad.val.rule
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad.val.rule hgood bad.val.measurable_rule)
  let before := (run input C .uncapped accounting policy.val.rule sample (n + 4)).history
  have hentry := paidHeadThen_wrong_firstEntry input C hearly hcurrent hpayment accounting head hhead test available
    tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
  have hobs := bellmanEntry_observations_empty input 1 C accounting policy.val.rule policy.val.legal sample (n + 4) hentry
  have hbase := GuardLift.base_of_firstEntry input 1 C hearly accounting policy.val.rule policy.val.legal
    sample (n + 4) hentry available
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let executed := bellmanExecuteState accounting allocated head tool
  let handle : MismatchHandle I := ⟨head, written.ledger.writeSerial head⟩
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 4) =
      record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false :=
    paidHeadThen_run_wrong_advance input C hearly hcurrent hpayment accounting head hhead test available
      tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
  have hexec : historyExecutions before = [(handle, tool)] := by
    change historyExecutions (run input C .uncapped accounting policy.val.rule sample (n + 4)).history = _
    rw [hr]
    exact (bellmanRepairedEntry_history_corrections input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)) tool).2
  have hresolved : ∀ stage : I.Stage, stage.val < 1 →
      historyWritten before stage = some (input.truthAt sample.2 stage) ∨
        ∃ pair ∈ historyExecutions before, pair.1.stage = stage := by
    intro stage hs
    have heq : stage = head := Fin.ext (by omega)
    subst stage
    right
    refine ⟨(handle, tool), ?_, rfl⟩
    rw [hexec]
    exact List.mem_singleton_self (handle, tool)
  have hcount : (run input C .uncapped accounting policy.val.rule sample (n + 4)).ledger.reviews head =
      test.rule.stop sample.1 (worldTapes input sample.2 head) := by
    rw [hr, hstop]
    change written.ledger.reviews head = n
    exact bellmanHeadWrittenState_reviews_eq input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hfee := bellmanPrefix_observationBill_of_entry input C accounting policy.val.rule policy.val.legal
    head hhead test sample (n + 4) hentry hcount
  have hviews := paidHeadThen_wrong_run_view input C hearly hcurrent hpayment accounting head hhead test available
    tool htool heligible good hgood bad sample n hstop hwrong
  have hcorr : historyCorrectionCharge input before = ENNReal.ofReal (input.fees.correction head tool : ℝ) := by
    simp only [historyCorrectionCharge, hexec, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
    rfl
  have hbound := runPaidPenaltyCharge_suffixRun_le input 1 C accounting policy.val.rule policy.val.legal
    (paidRelaxedContract (I.freshSuffix 1)) (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule bad.val.legal
    sample before (n + 4) hobs hviews hearly hbase.written hresolved penalty
  rw [hfee, hcorr] at hbound
  exact hbound


end PDMenu
