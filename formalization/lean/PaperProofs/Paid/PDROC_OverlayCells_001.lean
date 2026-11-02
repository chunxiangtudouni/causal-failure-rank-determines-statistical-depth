module

public import PaperProofs.Paid.PDROC_OverlayKernel_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

noncomputable def overlayEndpointLaw (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) : Measure (OverlayStageCoins × (Bool × P.experiment.Tape)) :=
  (overlayPaidStageCoinsLaw P fee hfee).prod ((P.input fee hfee).stageLaw stage)

instance overlayEndpointLaw_probability (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) : IsProbabilityMeasure (overlayEndpointLaw P fee hfee stage) := by
  unfold overlayEndpointLaw
  exact @Measure.prod.instIsProbabilityMeasure OverlayStageCoins ((P.input fee hfee).StageSample stage) _ _ _ _
    (overlayPaidStageCoinsLaw_probability P fee hfee) (StatisticalInput.stageLaw_probability (P.input fee hfee) stage)

theorem overlayEndpointLaw_measure_of_conditional_constant
    (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (A : Set (OverlayStageCoins × (Bool × P.experiment.Tape))) (hA : MeasurableSet A) (value : ℝ≥0∞)
    (hvalue : ∀ truth, overlayRowConditionalLaw P fee hfee truth
      ((fun pair => (pair.1, (truth, pair.2))) ⁻¹' A) = value) :
    overlayEndpointLaw P fee hfee stage A = value := by
  rw [← lintegral_indicator_one hA]
  apply lintegral_overlayRowWorldLaw_of_conditional_constant P fee hfee stage
    (overlayPaidStageCoinsLaw P fee hfee) _ (measurable_const.indicator hA) value
  intro truth
  change (∫⁻ pair : OverlayStageCoins × P.experiment.Tape,
    A.indicator (fun _ => (1 : ℝ≥0∞)) (pair.1, (truth, pair.2)) ∂overlayRowConditionalLaw P fee hfee truth) = value
  have heq : (fun pair : OverlayStageCoins × P.experiment.Tape =>
      A.indicator (fun _ => (1 : ℝ≥0∞)) (pair.1, (truth, pair.2))) =
      ((fun pair : OverlayStageCoins × P.experiment.Tape => (pair.1, (truth, pair.2))) ⁻¹' A).indicator (fun _ => 1) := by
    funext pair
    rfl
  rw [heq]
  have hp : Measurable (fun pair : OverlayStageCoins × P.experiment.Tape => (pair.1, (truth, pair.2))) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  exact (lintegral_indicator_const (hA.preimage hp) (1 : ℝ≥0∞)).trans
    ((one_mul _).trans (hvalue truth))

noncomputable def overlayEndpointCharge (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) (sample : OverlayStageCoins × (Bool × P.experiment.Tape)) : ℝ≥0∞ :=
  P.experiment.observationCharge ((P.overlayRecordTest fee hfee record).rule.stop (sample.1.1 record) sample.2.2)

noncomputable def overlayEndpointActualError (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : Set (OverlayStageCoins × (Bool × P.experiment.Tape)) :=
  {sample | (P.overlayRecordTest fee hfee record).rule.decision (sample.1.1 record) sample.2.2 ≠ sample.2.1}

noncomputable def overlayEndpointVirtualError (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : Set (OverlayStageCoins × (Bool × P.experiment.Tape)) :=
  overlayEndpointActualError P fee hfee record ∪ {sample | sample.1.2 record = true}

def overlayEndpointTestSample (P : Parameters) (record : AuxiliaryRecord)
    (sample : OverlayStageCoins × (Bool × P.experiment.Tape)) : (Bool × Bool) × P.experiment.Tape :=
  (sample.1.1 record, sample.2.2)

theorem measurable_overlayEndpointTestSample (P : Parameters) (record : AuxiliaryRecord) :
    Measurable (overlayEndpointTestSample P record) := by
  unfold overlayEndpointTestSample
  fun_prop

theorem measurable_overlayEndpointCharge (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (record : AuxiliaryRecord) :
    Measurable (overlayEndpointCharge P fee hfee record) :=
  (measurable_of_countable P.experiment.observationCharge).comp
    ((P.overlayRecordTest fee hfee record).measurable_stop.comp
      (measurable_overlayEndpointTestSample P record))

theorem measurableSet_overlayEndpointActualError (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : MeasurableSet (overlayEndpointActualError P fee hfee record) :=
  (measurableSet_eq_fun
    ((P.overlayRecordTest fee hfee record).measurable_decision.comp
      (measurable_overlayEndpointTestSample P record)) (measurable_fst.comp measurable_snd)).compl

theorem measurableSet_overlayEndpointVirtualError (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (record : AuxiliaryRecord) : MeasurableSet (overlayEndpointVirtualError P fee hfee record) :=
  (measurableSet_overlayEndpointActualError P fee hfee record).union
    ((measurableSet_singleton true).preimage ((measurable_pi_apply record).comp
      (measurable_snd.comp measurable_fst)))

theorem overlayEndpointLaw_actual_error (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    overlayEndpointLaw P fee hfee stage (overlayEndpointActualError P fee hfee record) =
      ENNReal.ofReal (P.overlayRecordTarget fee record) := by
  apply overlayEndpointLaw_measure_of_conditional_constant P fee hfee stage _
    (measurableSet_overlayEndpointActualError P fee hfee record)
  intro truth
  have hA : MeasurableSet (overlayLocalErrorEvent P fee hfee record truth ×ˢ (Set.univ : Set Bool)) :=
    (measurableSet_overlayLocalErrorEvent P fee hfee record truth).prod MeasurableSet.univ
  have heq : ((fun pair : OverlayStageCoins × P.experiment.Tape => (pair.1, (truth, pair.2))) ⁻¹'
      overlayEndpointActualError P fee hfee record) =
      (overlayRowExperimentSample P record) ⁻¹' (overlayLocalErrorEvent P fee hfee record truth ×ˢ Set.univ) := by
    ext pair
    simp [overlayEndpointActualError, overlayRowExperimentSample, overlayLocalErrorEvent]
  rw [heq, ← Measure.map_apply (measurable_overlayRowExperimentSample P record) hA,
    overlayRowConditionalLaw_experiment, overlayLocalExperimentLaw,
    Measure.prod_prod, measure_univ, mul_one, overlayLocal_actual_probability]

theorem overlayEndpointLaw_virtual_error (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    overlayEndpointLaw P fee hfee stage (overlayEndpointVirtualError P fee hfee record) =
      ENNReal.ofReal (P.recordDecisionError record) := by
  apply overlayEndpointLaw_measure_of_conditional_constant P fee hfee stage _
    (measurableSet_overlayEndpointVirtualError P fee hfee record)
  intro truth
  have hA := measurableSet_overlayKernelVirtualEvent _ (measurableSet_overlayLocalErrorEvent P fee hfee record truth)
  have heq : ((fun pair : OverlayStageCoins × P.experiment.Tape => (pair.1, (truth, pair.2))) ⁻¹'
      overlayEndpointVirtualError P fee hfee record) =
      (overlayRowExperimentSample P record) ⁻¹'
        overlayKernelVirtualEvent (overlayLocalErrorEvent P fee hfee record truth) := by
    ext pair
    simp only [Set.mem_preimage, overlayEndpointVirtualError, overlayEndpointActualError,
      overlayRowExperimentSample, overlayKernelVirtualEvent, overlayLocalErrorEvent,
      Set.mem_union, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, Set.mem_compl_iff,
      Set.mem_singleton_iff, and_true]
    tauto
  rw [heq, ← Measure.map_apply (measurable_overlayRowExperimentSample P record) hA,
    overlayRowConditionalLaw_experiment, overlayLocal_virtual_probability]

theorem overlayEndpointLaw_charge (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    (∫⁻ sample, overlayEndpointCharge P fee hfee record sample ∂overlayEndpointLaw P fee hfee stage) =
      P.binarySymmetric.rocPrice (P.overlayRecordTarget fee record) := by
  apply lintegral_overlayRowWorldLaw_of_conditional_constant P fee hfee stage
    (overlayPaidStageCoinsLaw P fee hfee) _ (measurable_overlayEndpointCharge P fee hfee record)
  intro truth
  let charge := fun sample : (((Bool × Bool) × P.experiment.Tape) × Bool) =>
    P.experiment.observationCharge ((P.overlayRecordTest fee hfee record).rule.stop sample.1.1 sample.1.2)
  have hc : Measurable charge :=
    ((measurable_of_countable P.experiment.observationCharge).comp
      (P.overlayRecordTest fee hfee record).measurable_stop).comp measurable_fst
  change (∫⁻ pair, charge (overlayRowExperimentSample P record pair) ∂overlayRowConditionalLaw P fee hfee truth) = _
  rw [← lintegral_map hc (measurable_overlayRowExperimentSample P record), overlayRowConditionalLaw_experiment]
  exact overlayLocal_expectedCharge P fee hfee record truth

end PDROC
