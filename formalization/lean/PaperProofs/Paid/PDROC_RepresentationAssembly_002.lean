module

public import PaperProofs.Paid.PDROC_RepresentationAssembly_001
public import PaperProofs.Paid.PDROC_SimulatorCells_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Concrete cells are now discharged; only the two remaining global
history/observation obligations are explicit in this assembly interface. -/
theorem simulatorBoundaryRepresentation_of_history_observation
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hf : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hlaw : P.SourceHistoryLaw fee hfee fee hfee C accounting ν (simulatorSeedLaw P ν)
      source.rule (simulatorPolicy P fee hfee C accounting source).rule (simulatorData P fee hfee source.rule))
    (hobs : expectedObservationBill (P.input fee hfee) C.val .uncapped accounting
        (simulatorPolicy P fee hfee C accounting source).rule (simulatorSeedLaw P ν) ≤
      expectedObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule ν) :
    P.BoundaryRepresentation fee hfee C accounting ν (simulatorSeedLaw P ν) source
      (simulatorPolicy P fee hfee C accounting source) (simulatorData P fee hfee source.rule) :=
  simulatorBoundaryRepresentation_of_history_cells_observation P fee hfee C accounting source ν hf hlaw
    (simulatorBoundaryRecordCells P fee hfee C accounting source ν) hobs

end PDROC
