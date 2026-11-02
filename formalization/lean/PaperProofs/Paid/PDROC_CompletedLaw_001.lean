module

public import PaperProofs.Paid.PDROC_SourceTerminal_002
public import PaperProofs.Paid.PDROC_Simulator_052
public import PaperProofs.Paid.PDROC_TerminalLaw_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- At every ordinary stage cursor, its exact entry law implies the FULL
completed-history restriction law, including every earlier paid event and
all failed/abandoned terminal histories. Only terminal cursor N remains. -/
theorem simulator_completedCursorLaw_eq_of_entryLaw
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
        (simulatorData P fee hfee source.rule) sample))).restrict
          (completedCursorCell P.sharedInstance Seed stage.val) =
    (((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
      (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample))).restrict
        (completedCursorCell P.sharedInstance Seed stage.val) := by
  exact completedCursorLaw_eq_of_stageExitLaw
    ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)) ((P.input fee hfee).seededWorldLaw ν) stage
    (fun sample => (sample.1.1, P.shadowCompletedHistory fee hfee C accounting
      (simulatorRule P fee hfee source.rule) (simulatorData P fee hfee source.rule) sample))
    ((measurable_fst.comp measurable_fst).prodMk
      (measurable_simulatorShadowCompletedHistory P fee hfee C accounting source.rule source.measurable_rule))
    (fun sample => (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample))
    (measurable_fst.prodMk (measurable_completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule source.measurable_rule))
    (simulatorEventualStageExit P fee hfee C accounting source.rule stage)
    (measurable_simulatorEventualStageExit P fee hfee C accounting source.rule source.measurable_rule stage)
    (sourceEventualStageExitSome P fee hfee C accounting source stage)
    (measurable_sourceEventualStageExitSome P fee hfee C accounting source stage)
    (simulatorEventualStageExit_law_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry)
    (simulator_terminalCapture_ae_of_entryLaw P fee hfee C accounting source ν stage hfinite hentry)
    (sourceEventualStageExit_terminalCapture_ae P fee hfee C accounting source ν stage hfinite)

end PDROC
