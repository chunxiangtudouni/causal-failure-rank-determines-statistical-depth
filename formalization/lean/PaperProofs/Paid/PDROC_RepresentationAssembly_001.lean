module

public import PaperProofs.Paid.PDROC_SimulatorRecords_005
public import PaperProofs.Paid.PDROC_SimulatorReturns_001
public import PaperProofs.Paid.PDROC_Simulator_025
public import PaperProofs.Paid.PDROC_Simulator_010
public import PaperProofs.Paid.PDROC_MarkedFees_002
public import PaperProofs.Paid.PDROC_MarkedRisk_002
public import PaperProofs.Paid.PDROC_BillAssembly_001
public import PaperProofs.Paid.PDROC_FirstFailureFinite_001
public import PaperProofs.Paid.PDROC_Records_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

/-- Assembly only: the three remaining mathematical obligations remain
explicit. All other ORIGINAL representation fields follow from the actual
native simulator theorems, including full correction-fee law and risk. -/
theorem simulatorBoundaryRepresentation_of_history_cells_observation
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed)
    (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hf : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hlaw : P.SourceHistoryLaw fee hfee fee hfee C accounting ν (simulatorSeedLaw P ν)
      source.rule (simulatorPolicy P fee hfee C accounting source).rule (simulatorData P fee hfee source.rule))
    (hcells : P.BoundaryRecordCells fee hfee C accounting (simulatorSeedLaw P ν)
      (simulatorPolicy P fee hfee C accounting source).rule (simulatorData P fee hfee source.rule))
    (hobs : expectedObservationBill (P.input fee hfee) C.val .uncapped accounting
        (simulatorPolicy P fee hfee C accounting source).rule (simulatorSeedLaw P ν) ≤
      expectedObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule ν) :
    P.BoundaryRepresentation fee hfee C accounting ν (simulatorSeedLaw P ν) source
      (simulatorPolicy P fee hfee C accounting source) (simulatorData P fee hfee source.rule) := by
  have hm := simulatorData_measurable P fee hfee source.rule source.measurable_rule
  have hsource := paid_finiteExpectedBill_completedHistory P fee hfee C.val .uncapped accounting source ν hf
  have hactual := simulator_completedHistory_none_zero P fee hfee C accounting source (simulatorSeedLaw P ν)
  have hmarks := Filter.Eventually.of_forall
    (f := ae ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)))
    (simulator_markedCompletedHistory P fee hfee C accounting source)
  exact ⟨hm, simulatorData_shadowCausal P fee hfee source.rule,
    simulatorSourceRecordAlignment P fee hfee C accounting source.rule (simulatorSeedLaw P ν), hlaw,
    simulatorBoundaryStageRealization P fee hfee C accounting source.rule (simulatorSeedLaw P ν), hcells,
    hsource, hactual, hmarks, hobs,
    actualCorrectionBillLaw_eq_of_sourceHistoryLaw P fee hfee C accounting ν (simulatorSeedLaw P ν)
      source (simulatorPolicy P fee hfee C accounting source) (simulatorData P fee hfee source.rule)
      hm hlaw hsource hactual hmarks,
    risk_eq_of_sourceHistoryLaw P fee hfee C accounting ν (simulatorSeedLaw P ν)
      source (simulatorPolicy P fee hfee C accounting source) (simulatorData P fee hfee source.rule)
      hm hlaw hmarks⟩

/-- Original full-seed/universe/penalty D06 assembly. A proof of every
finite-cost native simulator's complete BoundaryRepresentation suffices;
no finite-ET or MAP restriction is introduced in the original comparator. -/
theorem recordRepresentationClaims_of_nativeRepresentation
    (P : PaperProofs.Paid.Parameters)
    (hrep : ∀ (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract)
      (accounting : NormalAccounting P.sharedInstance) (Seed : Type u) (ms : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := ms
      ∀ (ν : Measure Seed) (hν : IsProbabilityMeasure ν),
        letI : IsProbabilityMeasure ν := hν
        ∀ source : Policy (P.input fee hfee) C.val .uncapped accounting Seed,
          expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤ →
          P.BoundaryRepresentation fee hfee C accounting ν (simulatorSeedLaw P ν) source
            (simulatorPolicy P fee hfee C accounting source) (simulatorData P fee hfee source.rule)) :
    P.RecordRepresentationClaims.{u} := by
  refine ⟨auxiliaryPosteriorLevels P, ?_⟩
  intro fee hfee C accounting mode Seed ms ν hν original hf
  let : MeasurableSpace Seed := ms
  let : IsProbabilityMeasure ν := hν
  obtain ⟨stopped, hdom, hbill, _, hpenalty⟩ :=
    finiteCost_firstFailureNormalization P fee hfee C mode accounting original ν hf
  have hsfinite := ne_top_of_le_ne_top hf hbill
  have hb := hrep fee hfee C accounting Seed ms ν hν stopped hsfinite
  refine ⟨stopped, hdom, SimulatorSeed P Seed, inferInstance, simulatorSeedLaw P ν,
    inferInstance, simulatorPolicy P fee hfee C accounting stopped, simulatorData P fee hfee stopped.rule,
    hb, ?_⟩
  intro penalty
  exact (paidPenaltyObjective_le_of_actual_components P fee hfee C accounting stopped ν
    (simulatorPolicy P fee hfee C accounting stopped) (simulatorSeedLaw P ν)
    hb.2.2.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.2.1 hb.2.2.2.2.2.2.2.2.2.2.2 penalty).trans
    (hpenalty penalty)

end PDROC
