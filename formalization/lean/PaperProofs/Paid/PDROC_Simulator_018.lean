module

public import PaperProofs.Paid.PDROC_Simulator_017
public import PaperProofs.Paid.PDROC_EndpointFinite_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- The exact original D06 boundary-stage realization holds for the actual
concrete simulator. Finite stopping is concluded simultaneously for every
record level, without a finite-ET or source-law premise. -/
theorem simulatorBoundaryStageRealization (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : PolicyRule P.sharedInstance Seed) (ν : Measure (SimulatorSeed P Seed)) [IsProbabilityMeasure ν] :
    P.BoundaryStageRealization fee hfee C accounting ν (simulatorRule P fee hfee source)
      (simulatorData P fee hfee source) := by
  filter_upwards [allEndpoints_finite_seededWorld P fee hfee ν] with sample hs
  exact simulator_boundaryStage_pointwise P fee hfee C accounting source sample.1 sample.2 hs

end PDROC
