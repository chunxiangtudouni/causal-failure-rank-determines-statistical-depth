module

public import PaperProofs.Paid.PDROC_Simulator_018
public import PaperProofs.Paid.PDROC_Termination_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u

/-- The concrete actual boundary simulator returns almost surely for every
source policy and every independent probability seed law. This conclusion
does not assume the source-history law or finite expected simulator fees. -/
theorem simulator_completedHistory_none_zero (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    {Seed : Type u} [MeasurableSpace Seed]
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure (SimulatorSeed P Seed)) [IsProbabilityMeasure ν] :
    (P.input fee hfee).seededWorldLaw ν {sample |
      completedHistory (P.input fee hfee) C.val .uncapped accounting
        (simulatorPolicy P fee hfee C accounting source).rule sample = none} = 0 :=
  boundaryStageRealization_completedHistory_none_zero P fee hfee C accounting ν
    (simulatorPolicy P fee hfee C accounting source) (simulatorData P fee hfee source.rule)
    (simulatorBoundaryStageRealization P fee hfee C accounting source.rule ν)

end PDROC
