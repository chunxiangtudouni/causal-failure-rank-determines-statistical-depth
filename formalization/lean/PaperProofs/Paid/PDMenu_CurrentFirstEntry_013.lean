module

public import PaperProofs.Paid.PDMenu_CurrentPaymentPhases_009
public import PaperProofs.Common.NativeBellmanContinuationRun

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native

variable {I : Instance}

theorem paidHeadThen_correct_firstEntry {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hpayment : C.execution = .currentWindow)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head) :
    FirstEntryAt input C .uncapped accounting
      (paidHeadThenRule input head test available (bellmanPostHeadRaw input head repair good bad))
      1 (n + 2) sample := by
  let after := bellmanPostHeadRaw input head repair good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good bad hgood hbad)
  have hbefore : (run input C .uncapped accounting policy.val.rule sample (n + 1)).cursor = 0 := by
    exact (congrArg (fun s : State I => s.cursor)
      (paidHeadThen_run_write input C accounting head hhead test available after sample n hstop)).trans
        (bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
          (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)))
  have hafter : (run input C .uncapped accounting policy.val.rule sample (n + 2)).cursor = 1 := by
    exact congrArg (fun s : State I => s.cursor)
      (paidHeadThen_run_correct_advance input C hearly hcurrent hpayment accounting head hhead test available
        repair good bad hgood hbad sample n hstop hcorrect)
  exact bellman_firstEntryAt_of_zero_to_one input C .uncapped accounting policy.val.rule policy.val.legal
    sample (n + 1) hbefore hafter

set_option maxHeartbeats 800000 in
theorem paidHeadThen_wrong_firstEntry {Seed : Type*} [MeasurableSpace Seed]
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
    FirstEntryAt input C .uncapped accounting
      (paidHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad))
      1 (n + 4) sample := by
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  have hbefore : (run input C .uncapped accounting policy.val.rule sample (n + 3)).cursor = 0 := by
    exact (congrArg (fun s : State I => s.cursor)
      (paidHeadThen_run_wrong_execute input C hearly hcurrent hpayment accounting head hhead test available
        tool htool heligible good bad hgood hbad sample n hstop hwrong)).trans
      (bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)))
  have hafter : (run input C .uncapped accounting policy.val.rule sample (n + 4)).cursor = 1 := by
    exact congrArg (fun s : State I => s.cursor)
      (paidHeadThen_run_wrong_advance input C hearly hcurrent hpayment accounting head hhead test available
        tool htool heligible good bad hgood hbad sample n hstop hwrong)
  exact bellman_firstEntryAt_of_zero_to_one input C .uncapped accounting policy.val.rule policy.val.legal
    sample (n + 3) hbefore hafter


end PDMenu
