module

public import PaperProofs.Paid.PDROC_SimulatorLaw_017
public import PaperProofs.Paid.PDROC_CompletedLaw_001
public import PaperProofs.Paid.PDROC_SimulatorObservation_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Every ordinary terminal cursor has the exact full original completed
joint law. No entry, guard, local ET, or successful-path premise remains. -/
theorem simulator_completedCursorLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : P.sharedInstance.Stage)
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    (((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map (fun sample =>
      (sample.1.1, P.shadowCompletedHistory fee hfee C accounting (simulatorRule P fee hfee source.rule)
        (simulatorData P fee hfee source.rule) sample))).restrict
          (completedCursorCell P.sharedInstance Seed stage.val) =
    (((P.input fee hfee).seededWorldLaw ν).map (fun sample =>
      (sample.1, completedHistory (P.input fee hfee) C.val .uncapped accounting source.rule sample))).restrict
        (completedCursorCell P.sharedInstance Seed stage.val) :=
  simulator_completedCursorLaw_eq_of_entryLaw P fee hfee C accounting source ν stage hfinite
    (simulatorVirtualEntryGate_law P fee hfee C accounting source ν hfinite stage)

/-- Actual total observation-charge domination for the concrete simulator
and the complete original source policy, including every failed path. -/
theorem simulator_observation_le_source (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤) :
    expectedObservationBill (P.input fee hfee) C.val .uncapped accounting
      (simulatorPolicy P fee hfee C accounting source).rule (simulatorSeedLaw P ν) ≤
        expectedObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule ν :=
  simulator_observation_le_of_eventualEntryLaw P fee hfee C accounting source ν hfinite
    (simulatorVirtualEntryGate_law P fee hfee C accounting source ν hfinite)

end PDROC
