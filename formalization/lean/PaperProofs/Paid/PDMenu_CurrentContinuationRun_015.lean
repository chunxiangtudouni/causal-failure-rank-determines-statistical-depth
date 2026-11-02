module

public import PaperProofs.Paid.PDMenu_CurrentJoin_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

set_option maxHeartbeats 1200000 in
theorem paidHeadThen_correct_run_view {Seed : Type*} [MeasurableSpace Seed]
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
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head) :
    let rule := paidHeadThenRule input head test available (bellmanPostHeadRaw input head repair good.val.rule bad)
    let before := (run input C .uncapped accounting rule sample (n + 2)).history
    ∀ k : ℕ, ReferenceSuffixView I 1 before
      (run input C .uncapped accounting rule sample (n + 2 + k))
      (run (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule
        (sample.1, referenceSuffixWorld input 1 sample.2) k) := by
  let after := bellmanPostHeadRaw input head repair good.val.rule bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good.val.rule bad good.val.measurable_rule hbad)
  let before := (run input C .uncapped accounting policy.val.rule sample (n + 2)).history
  have hentry := paidHeadThen_correct_firstEntry input C hearly hcurrent hpayment accounting head hhead test available
    repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
  have hbeforeObs := bellmanEntry_observations_empty input 1 C accounting policy.val.rule policy.val.legal
    sample (n + 2) hentry
  have hbase0 := GuardLift.base_of_firstEntry input 1 C hearly accounting policy.val.rule policy.val.legal
    sample (n + 2) hentry available
  obtain ⟨_, _, hpStart⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 2)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hrAdvance : run input C .uncapped accounting policy.val.rule sample (n + 2) =
      record accounting written (.advance head) [.advanced head] (advanceLedger written head) 1 false :=
    paidHeadThen_run_correct_advance input C hearly hcurrent hpayment accounting head hhead test available
      repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
  have hcomms : historyCommitments before = [] := by
    have hq := prefix_historyCommitments input C .uncapped accounting policy.val.rule sample.1 _ _ hpStart
    have hfield : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.commitments = [] := by
      rw [hrAdvance]
      exact (bellmanHeadWrittenState_empty_corrections input C hearly accounting head
        (input.truthAt sample.2) (worldTapes input sample.2 head) n _).1
    rw [hfield, List.map_nil] at hq
    exact hq
  have hused : historyUsed before = ∅ := by simp only [historyUsed, hcomms, List.map_nil, List.toFinset_nil]
  have hbase : GuardLift.Base I 1 before available available := by
    change GuardLift.Base I 1 before available (available \ historyUsed before) at hbase0
    simpa only [hused, Finset.sdiff_empty] using hbase0
  have hbeforeWritten : historyWritten before head ≠ none := by
    have hw := prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hpStart head
    have hfield : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.written head =
        some (test.rule.decision sample.1 (worldTapes input sample.2 head)) := by
      rw [hrAdvance]
      exact bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    have hsome : historyWritten before head = some (test.rule.decision sample.1 (worldTapes input sample.2 head)) :=
      hw.trans hfield
    rw [hsome]
    exact Option.some_ne_none _
  apply suffixRun_view_of_rule_lift_active input 1 C hearly accounting policy.val.rule policy.val.legal
    (paidRelaxedContract (I.freshSuffix 1)) rfl (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule good.val.legal
    sample before (n + 2) hbeforeObs
    (paidHeadThen_correct_initialView input C hearly hcurrent hpayment accounting head hhead test available
      repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect)
  intro k view hactive
  let childSample : Seed × (input.freshSuffix 1).World := (sample.1, referenceSuffixWorld input 1 sample.2)
  obtain ⟨_, _, hpChild⟩ := run_has_prefix (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
    .uncapped (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule good.val.legal childSample k
  have hpost := paidPostHeadRaw_correct_actual_join input C hearly hcurrent hpayment accounting head hhead test available
    repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
      (run (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule childSample k).history
  have hraw : bellmanHeadThenRaw input head test after sample.1
      (run input C .uncapped accounting policy.val.rule sample (n + 2 + k)).history =
      referenceSuffixActionLift I 1 (historyActions before).length
        (good.val.rule sample.1 (run (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule childSample k).history) := by
    rw [view.history]
    have hheadEarlier : head.val < 1 := by omega
    simp only [bellmanHeadThenRaw, historyWritten_referenceSuffixJoin_earlier 1 head hheadEarlier,
      hbeforeWritten, ↓reduceIte]
    exact hpost
  have hallow := paidAllows_of_childPrefix input 1 before available available hbase (paidRelaxedContract (I.freshSuffix 1)) (paidRelaxedContract_rights _)
    (zeroNormalAccounting (I.freshSuffix 1)) good
    sample.1 _ _ hpChild hactive
  change paidGuardedRule available (bellmanHeadThenRaw input head test after) sample.1
    (run input C .uncapped accounting policy.val.rule sample (n + 2 + k)).history = _
  simp only [paidGuardedRule, hraw]
  rw [view.history]
  exact ite_eq_left hallow

set_option maxHeartbeats 1200000 in
theorem paidHeadThen_wrong_run_view {Seed : Type*} [MeasurableSpace Seed]
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
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let rule := paidHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad.val.rule)
    let before := (run input C .uncapped accounting rule sample (n + 4)).history
    ∀ k : ℕ, ReferenceSuffixView I 1 before
      (run input C .uncapped accounting rule sample (n + 4 + k))
      (run (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule
        (sample.1, referenceSuffixWorld input 1 sample.2) k) := by
  let after := bellmanPostHeadRaw input head (some tool) good bad.val.rule
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad.val.rule hgood bad.val.measurable_rule)
  let before := (run input C .uncapped accounting policy.val.rule sample (n + 4)).history
  have hentry := paidHeadThen_wrong_firstEntry input C hearly hcurrent hpayment accounting head hhead test available
    tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
  have hbeforeObs := bellmanEntry_observations_empty input 1 C accounting policy.val.rule policy.val.legal
    sample (n + 4) hentry
  have hbase0 := GuardLift.base_of_firstEntry input 1 C hearly accounting policy.val.rule policy.val.legal
    sample (n + 4) hentry available
  obtain ⟨_, _, hpStart⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 4)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let executed := bellmanExecuteState accounting allocated head tool
  let handle : MismatchHandle I := ⟨head, written.ledger.writeSerial head⟩
  have hrAdvance : run input C .uncapped accounting policy.val.rule sample (n + 4) =
      record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false :=
    paidHeadThen_run_wrong_advance input C hearly hcurrent hpayment accounting head hhead test available
      tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
  have hcomms : historyCommitments before = [(handle, tool)] := by
    change historyCommitments (run input C .uncapped accounting policy.val.rule sample (n + 4)).history = _
    rw [hrAdvance]
    exact (bellmanRepairedEntry_history_corrections input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)) tool).1
  have hused : historyUsed before = {tool} := by
    simp only [historyUsed, hcomms, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      Finset.insert_empty]
  have hbase : GuardLift.Base I 1 before available (available.erase tool) := by
    change GuardLift.Base I 1 before available (available \ historyUsed before) at hbase0
    simpa only [hused, Finset.sdiff_singleton_eq_erase] using hbase0
  have hbeforeWritten : historyWritten before head ≠ none := by
    have hw := prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hpStart head
    have hfield : (run input C .uncapped accounting policy.val.rule sample (n + 4)).ledger.written head =
        some (test.rule.decision sample.1 (worldTapes input sample.2 head)) := by
      rw [hrAdvance]
      change written.ledger.written head = some (test.rule.decision sample.1 (worldTapes input sample.2 head))
      exact bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    have hsome : historyWritten before head = some (test.rule.decision sample.1 (worldTapes input sample.2 head)) :=
      hw.trans hfield
    rw [hsome]
    exact Option.some_ne_none _
  apply suffixRun_view_of_rule_lift_active input 1 C hearly accounting policy.val.rule policy.val.legal
    (paidRelaxedContract (I.freshSuffix 1)) rfl (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule bad.val.legal
    sample before (n + 4) hbeforeObs
    (paidHeadThen_wrong_initialView input C hearly hcurrent hpayment accounting head hhead test available
      tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong)
  intro k view hactive
  let childSample : Seed × (input.freshSuffix 1).World := (sample.1, referenceSuffixWorld input 1 sample.2)
  obtain ⟨_, _, hpChild⟩ := run_has_prefix (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
    .uncapped (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule bad.val.legal childSample k
  have hpost := paidPostHeadRaw_wrong_actual_join input C hearly hcurrent hpayment accounting head hhead test available
    tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
      (run (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule childSample k).history
  have hraw : bellmanHeadThenRaw input head test after sample.1
      (run input C .uncapped accounting policy.val.rule sample (n + 4 + k)).history =
      referenceSuffixActionLift I 1 (historyActions before).length
        (bad.val.rule sample.1 (run (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule childSample k).history) := by
    rw [view.history]
    have hheadEarlier : head.val < 1 := by omega
    simp only [bellmanHeadThenRaw, historyWritten_referenceSuffixJoin_earlier 1 head hheadEarlier,
      hbeforeWritten, ↓reduceIte]
    exact hpost
  have hallow := paidAllows_of_childPrefix input 1 before available (available.erase tool) hbase (paidRelaxedContract (I.freshSuffix 1)) (paidRelaxedContract_rights _)
    (zeroNormalAccounting (I.freshSuffix 1)) bad
    sample.1 _ _ hpChild hactive
  change paidGuardedRule available (bellmanHeadThenRaw input head test after) sample.1
    (run input C .uncapped accounting policy.val.rule sample (n + 4 + k)).history = _
  simp only [paidGuardedRule, hraw]
  rw [view.history]
  exact ite_eq_left hallow


end PDMenu
