module

public import PaperProofs.Paid.PDMenu_CurrentFirstEntry_013
public import PaperProofs.Paid.PDMenu_CurrentSuffixGuard_012
public import PaperProofs.Common.NativeBellmanHistoryLift

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

variable {I : Instance}

theorem paidHeadThen_correct_initialView {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head) :
    let rule := paidHeadThenRule input head test available (bellmanPostHeadRaw input head repair good bad)
    let parent := run input C .uncapped accounting rule sample (n + 2)
    ReferenceSuffixView I 1 parent.history parent
      (initial ((input.freshSuffix 1).truthAt (referenceSuffixWorld input 1 sample.2))) := by
  let after := bellmanPostHeadRaw input head repair good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good bad hgood hbad)
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 2)
  have hr := paidHeadThen_run_correct_advance input C hearly hcurrent hpayment accounting head hhead test available
    repair good bad hgood hbad sample n hstop hcorrect
  apply suffixInitialView_of_prefix input 1 C accounting policy.val.rule sample.1 _ _ hp
  · change (run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 2)).cursor = 1
    rw [hr]
    rfl
  · change (run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 2)).halted = false
    rw [hr]
    rfl

/-- The actual wrong/repaired branch likewise supplies the continuation
initial view after allocate, execute and advance. -/
theorem paidHeadThen_wrong_initialView {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let rule := paidHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad)
    let parent := run input C .uncapped accounting rule sample (n + 4)
    ReferenceSuffixView I 1 parent.history parent
      (initial ((input.freshSuffix 1).truthAt (referenceSuffixWorld input 1 sample.2))) := by
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 4)
  have hr := paidHeadThen_run_wrong_advance input C hearly hcurrent hpayment accounting head hhead test available
    tool htool heligible good bad hgood hbad sample n hstop hwrong
  apply suffixInitialView_of_prefix input 1 C accounting policy.val.rule sample.1 _ _ hp
  · change (run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 4)).cursor = 1
    rw [hr]
    rfl
  · change (run input C .uncapped accounting (paidHeadThenRule input head test available after) sample (n + 4)).halted = false
    rw [hr]
    rfl

theorem paidPostHeadRaw_correct_actual_join {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head)
    (afterHistory : List (VisibleEvent (I.freshSuffix 1))) :
    let rule := paidHeadThenRule input head test available (bellmanPostHeadRaw input head repair good bad)
    let before := (run input C .uncapped accounting rule sample (n + 2)).history
    bellmanPostHeadRaw input head repair good bad sample.1
      (referenceSuffixHistoryJoin I 1 before afterHistory) =
      referenceSuffixActionLift I 1 (historyActions before).length (good sample.1 afterHistory) := by
  let after := bellmanPostHeadRaw input head repair good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 1) = written :=
    paidHeadThen_run_write input C accounting head hhead test available after sample n hstop
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 1)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head
    (input.truthAt sample.2) (worldTapes input sample.2 head) n
    (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : written.ledger.written head = some (written.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n _).trans (congrArg some hcorrect)
  have hreport : ∃ clock, written.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have hjoin := bellmanPostHeadRaw_good_join_of_prefix input C hearly .uncapped accounting policy.val.rule
    sample.1 _ _ hp head hhead repair good bad hc hw hreport afterHistory
  dsimp only
  rw [paidHeadThen_run_correct_advance input C hearly hcurrent hpayment accounting head hhead test available
    repair good bad hgood hbad sample n hstop hcorrect]
  exact hjoin

set_option maxHeartbeats 800000 in
theorem paidPostHeadRaw_wrong_actual_join {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head)
    (afterHistory : List (VisibleEvent (I.freshSuffix 1))) :
    let rule := paidHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad)
    let before := (run input C .uncapped accounting rule sample (n + 4)).history
    bellmanPostHeadRaw input head (some tool) good bad sample.1
      (referenceSuffixHistoryJoin I 1 before afterHistory) =
      referenceSuffixActionLift I 1 (historyActions before).length (bad sample.1 afterHistory) := by
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let executed := bellmanExecuteState accounting allocated head tool
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 3) = executed :=
    paidHeadThen_run_wrong_execute input C hearly hcurrent hpayment accounting head hhead test available
      tool htool heligible good bad hgood hbad sample n hstop hwrong
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 3)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : executed.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head
    (input.truthAt sample.2) (worldTapes input sample.2 head) n
    (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : executed.ledger.written head = some (!executed.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n _).trans (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, executed.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [executed, bellmanExecuteState, executeLedger, allocated, bellmanAllocateState, allocateLedger,
      written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have hjoin := bellmanPostHeadRaw_bad_join_of_prefix input C hearly .uncapped accounting policy.val.rule
    sample.1 _ _ hp head hhead (some tool) good bad hc hw hreport afterHistory
  dsimp only
  rw [paidHeadThen_run_wrong_advance input C hearly hcurrent hpayment accounting head hhead test available
    tool htool heligible good bad hgood hbad sample n hstop hwrong]
  exact hjoin


end PDMenu
