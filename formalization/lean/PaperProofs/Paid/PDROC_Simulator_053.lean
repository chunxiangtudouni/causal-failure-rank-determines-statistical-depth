module

public import PaperProofs.Paid.PDROC_Simulator_052
public import PaperProofs.Paid.PDROC_InitialEntry_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem source_completedHistory_zeroStages
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (hzero : P.sharedInstance.stageCount = 0) (sample : Seed × (P.input fee hfee).World) :
    completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample =
      some (terminalCursorTail source.rule sample.1 []) := by
  have hc : (run (P.input fee hfee) C.val .uncapped accounting source.rule sample 0).cursor = P.sharedInstance.stageCount :=
    hzero.symm
  have h := terminalCursorTail_eq_completedHistory (P.input fee hfee) C.val C.property .uncapped accounting
    source.rule source.legal sample 0 hc
  change completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample =
    some (terminalCursorTail source.rule sample.1 []) at h
  exact h

/-- With no stages, the actual completed shadow is exactly the original
source's empty-history stop/abandon tail on every sample. This is a full
history identity and uses no expected-bill or nonreturn assumption. -/
theorem simulator_shadowCompletedHistory_zeroStages
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (hzero : P.sharedInstance.stageCount = 0)
    (sample : SimulatorSeed P Seed × (P.input fee hfee).World) :
    P.shadowCompletedHistory fee hfee C accounting (simulatorPolicy P fee hfee C accounting source).rule
      (simulatorData P fee hfee source.rule) sample =
      some (terminalCursorTail source.rule sample.1.1 []) := by
  let input := P.input fee hfee
  have hcSource : (run input C.val .uncapped accounting source.rule (sample.1.1, sample.2) 0).cursor =
      P.sharedInstance.stageCount := hzero.symm
  have hcActual : (run input C.val .uncapped accounting (simulatorRule P fee hfee source.rule) sample 0).cursor =
      P.sharedInstance.stageCount := hzero.symm
  have hcases : source.rule sample.1.1 [] = .stop ∨ source.rule sample.1.1 [] = .abandon :=
    currentPayment_terminalCursor_action_cases input C.val C.property .uncapped accounting source.rule source.legal
      (sample.1.1, sample.2) 0 rfl hcSource
  have hallow : historyHalted (simulatorShadow P fee hfee source.rule sample.1
      (run input C.val .uncapped accounting (simulatorRule P fee hfee source.rule) sample 0).history) = false →
      historyAllowsAction (simulatorShadow P fee hfee source.rule sample.1
        (run input C.val .uncapped accounting (simulatorRule P fee hfee source.rule) sample 0).history)
        (source.rule sample.1.1 (simulatorShadow P fee hfee source.rule sample.1
          (run input C.val .uncapped accounting (simulatorRule P fee hfee source.rule) sample 0).history)) := by
    intro _ha
    change historyAllowsAction [] (source.rule sample.1.1 [])
    rcases hcases with hs | hs <;> simp only [hs, historyAllowsAction]
  have h := simulator_terminalCursor_shadowCompletedHistory P fee hfee C accounting source.rule sample 0 hcActual hallow
  change P.shadowCompletedHistory fee hfee C accounting (simulatorPolicy P fee hfee C accounting source).rule
      (simulatorData P fee hfee source.rule) sample =
      some (terminalCursorTail source.rule sample.1.1 []) at h
  exact h

end PDROC
