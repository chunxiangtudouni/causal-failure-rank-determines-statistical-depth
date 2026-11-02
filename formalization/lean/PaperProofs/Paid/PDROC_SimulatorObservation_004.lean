module

public import PaperProofs.Paid.PDROC_SimulatorObservation_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem simulator_stageObservation_le_of_entryLaw (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (stage : P.sharedInstance.Stage)
    (hentry : ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    (∫⁻ sample, runStageObservationBill (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source.rule) stage sample ∂(P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)) ≤
      ∫⁻ sample, runStageObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule stage sample
        ∂(P.input fee hfee).seededWorldLaw ν := by
  let μ := (P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)
  let η := sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage
  let joint : SimulatorSeed P Seed × (P.input fee hfee).World →
      ((Seed × EntryHistory P.sharedInstance) × P.binarySymmetric.experiment.Tape) ×
        (Bool × (Bool × P.experiment.Tape)) :=
    simulatorEntryAuxEndpoint P fee hfee C accounting source.rule stage
  let model := simulatorOptionalEndpointCharge P fee hfee source.rule stage
  have hj : Measurable joint := measurable_simulatorEntryAuxEndpoint P fee hfee C accounting
    source.rule source.measurable_rule stage
  have hm : Measurable model := measurable_simulatorOptionalEndpointCharge P fee hfee source.rule source.measurable_rule stage
  have hlaw : μ.map joint = (η.prod (auxiliaryTapeLaw P)).prod (simulatorEndpointLaw P fee hfee stage) :=
    simulatorEntryAuxEndpoint_jointLaw_of_entryLaw P fee hfee C accounting source ν stage hentry
  have hae : (fun sample => runStageObservationBill (P.input fee hfee) C.val .uncapped accounting
      (simulatorRule P fee hfee source.rule) stage sample) =ᵐ[μ] (fun sample => model (joint sample)) := by
    filter_upwards [allEndpoints_finite_seededWorld P fee hfee (simulatorSeedLaw P ν)] with sample hs
    exact simulator_runStageBill_eq_optionalEndpointCharge P fee hfee C accounting source.rule source.measurable_rule stage sample hs
  calc
    _ = ∫⁻ sample, model (joint sample) ∂μ := lintegral_congr_ae hae
    _ = ∫⁻ pair, model pair ∂μ.map joint := (lintegral_map hm hj).symm
    _ = ∫⁻ pair, model pair ∂(η.prod (auxiliaryTapeLaw P)).prod (simulatorEndpointLaw P fee hfee stage) := by rw [hlaw]
    _ = ∫⁻ pair, simulatorRecordWritingMean P (simulatorOptionalHistoryRecord P fee hfee source.rule stage pair)
        ∂η.prod (auxiliaryTapeLaw P) :=
      simulatorOptionalEndpointCharge_integral P fee hfee source.rule source.measurable_rule stage η
    _ ≤ P.binarySymmetric.experiment.bayesObservationCharge η
        (sourceEventualEntryTest P fee hfee source.rule source.measurable_rule stage) :=
      simulatorOptionalWritingMean_le_eventualCharge P fee hfee C accounting source ν stage hfinite
    _ = _ := sourceEventualEntryTest_bayesCharge_eq_stageBill P fee hfee C accounting source ν stage

/-- The original full actual observation bill is dominated by the original
source observation bill. The sole intermediate global premise is equality
of eventual old-seed/virtual-entry laws, without normalization of any gate. -/
theorem simulator_observation_le_of_eventualEntryLaw (P : PaperProofs.Paid.Parameters)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (source : Policy (P.input fee hfee) C.val .uncapped accounting Seed) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (hfinite : expectedBill (P.input fee hfee) C.val .uncapped accounting source.rule ν ≠ ⊤)
    (hentry : ∀ stage, ((P.input fee hfee).seededWorldLaw (simulatorSeedLaw P ν)).map
      (simulatorVirtualEntryGate P fee hfee C accounting source.rule stage) =
        sourceEventualEntrySeedLaw P fee hfee C accounting source ν stage) :
    expectedObservationBill (P.input fee hfee) C.val .uncapped accounting
      (simulatorPolicy P fee hfee C accounting source).rule (simulatorSeedLaw P ν) ≤
      expectedObservationBill (P.input fee hfee) C.val .uncapped accounting source.rule ν := by
  rw [expectedObservationBill_eq_sum_stage (P.input fee hfee) C.val .uncapped accounting
      (simulatorPolicy P fee hfee C accounting source).rule (simulatorPolicy P fee hfee C accounting source).legal
      (simulatorPolicy P fee hfee C accounting source).measurable_rule (simulatorSeedLaw P ν),
    expectedObservationBill_eq_sum_stage (P.input fee hfee) C.val .uncapped accounting source.rule
      source.legal source.measurable_rule ν]
  apply Finset.sum_le_sum
  intro stage _
  exact simulator_stageObservation_le_of_entryLaw P fee hfee C accounting source ν hfinite stage (hentry stage)

end PDROC

