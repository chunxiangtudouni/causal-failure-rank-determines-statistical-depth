module

public import PaperProofs.Paid.PDROC_SimulatorCells_001
public import PaperProofs.Paid.PDROC_RecordCells_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

noncomputable def simulatorEndpointLaw (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) : Measure (Bool × (Bool × P.experiment.Tape)) :=
  fairGuessLaw.prod ((P.input fee hfee).stageLaw stage)

instance simulatorEndpointLaw_probability (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) : IsProbabilityMeasure (simulatorEndpointLaw P fee hfee stage) := by
  unfold simulatorEndpointLaw
  exact @Measure.prod.instIsProbabilityMeasure Bool ((P.input fee hfee).StageSample stage) _ _
    fairGuessLaw ((P.input fee hfee).stageLaw stage) fairGuessLaw_probability
    (StatisticalInput.stageLaw_probability (P.input fee hfee) stage)

theorem lintegral_simulatorEndpointLaw_of_conditional_constant
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (f : Bool × (Bool × P.experiment.Tape) → ℝ≥0∞) (hf : Measurable f) (value : ℝ≥0∞)
    (hvalue : ∀ truth, (∫⁻ pair, f (pair.1, (truth, pair.2))
      ∂P.binarySymmetric.experiment.conditionalLaw fairGuessLaw truth) = value) :
    (∫⁻ pair, f pair ∂simulatorEndpointLaw P fee hfee stage) = value := by
  have hfixed (truth : Bool) :
      (∫⁻ pair, f pair ∂fairGuessLaw.prod ((Measure.dirac truth).prod (P.experiment.tapeLaw truth))) = value := by
    have ht : Measurable (fun tape : P.experiment.Tape => (truth, tape)) :=
      measurable_const.prodMk measurable_id
    have hmap := Measure.map_prod_map fairGuessLaw (P.experiment.tapeLaw truth) measurable_id ht
    rw [Measure.map_id] at hmap
    rw [Measure.dirac_prod, hmap, lintegral_map hf (measurable_id.prodMap ht)]
    exact hvalue truth
  change (∫⁻ pair, f pair ∂fairGuessLaw.prod
    (P.experiment.priorMass true • (Measure.dirac true).prod (P.experiment.tapeLaw true) +
      P.experiment.priorMass false • (Measure.dirac false).prod (P.experiment.tapeLaw false))) = value
  rw [Measure.prod_add, Measure.prod_smul_right, Measure.prod_smul_right,
    lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure, hfixed, hfixed]
  change P.experiment.priorMass true * value + P.experiment.priorMass false * value = value
  rw [← add_mul]
  have hsum : P.experiment.priorMass true + P.experiment.priorMass false = 1 := by
    simpa only [Fintype.sum_bool] using P.experiment.priorMass_sum
  rw [hsum, one_mul]

theorem simulatorEndpointLaw_measure_of_conditional_constant
    (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (stage : P.sharedInstance.Stage)
    (A : Set (Bool × (Bool × P.experiment.Tape))) (hA : MeasurableSet A) (value : ℝ≥0∞)
    (hvalue : ∀ truth, P.binarySymmetric.experiment.conditionalLaw fairGuessLaw truth
      ((fun pair => (pair.1, (truth, pair.2))) ⁻¹' A) = value) :
    simulatorEndpointLaw P fee hfee stage A = value := by
  rw [← lintegral_indicator_one hA]
  apply lintegral_simulatorEndpointLaw_of_conditional_constant P fee hfee stage _ (measurable_const.indicator hA) value
  intro truth
  change (∫⁻ pair : Bool × P.experiment.Tape, A.indicator (fun _ => (1 : ℝ≥0∞))
    (pair.1, (truth, pair.2)) ∂P.experiment.conditionalLaw fairGuessLaw truth) = value
  have heq : (fun pair : Bool × P.experiment.Tape => A.indicator (fun _ => (1 : ℝ≥0∞))
      (pair.1, (truth, pair.2))) =
      ((fun pair : Bool × P.experiment.Tape => (pair.1, (truth, pair.2))) ⁻¹' A).indicator (fun _ => 1) := by
    funext pair
    rfl
  rw [heq]
  have hp : Measurable (fun pair : Bool × P.experiment.Tape => (pair.1, (truth, pair.2))) :=
    measurable_fst.prodMk (measurable_const.prodMk measurable_snd)
  exact (lintegral_indicator_const (hA.preimage hp) (1 : ℝ≥0∞)).trans
    ((one_mul _).trans (hvalue truth))

noncomputable def simulatorEndpointCharge (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord)
    (sample : Bool × (Bool × P.experiment.Tape)) : ℝ≥0∞ :=
  P.binarySymmetric.experiment.observationCharge
    ((P.binarySymmetric.rocEndpointTest record.level).rule.stop sample.1 sample.2.2)

noncomputable def simulatorEndpointError (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) :
    Set (Bool × (Bool × P.experiment.Tape)) :=
  {sample | flippedRecordDecision P record (sample.1, sample.2.2) ≠ sample.2.1}

noncomputable def simulatorEndpointPosterior (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) :
    Set (Bool × (Bool × P.experiment.Tape)) :=
  {sample | recordVirtualTruth P record sample.2.1 (sample.1, sample.2.2) ≠ record.orientation}

theorem measurable_simulatorEndpointCharge (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) :
    Measurable (simulatorEndpointCharge P record) := by
  exact ((measurable_of_countable P.binarySymmetric.experiment.observationCharge).comp
    (P.binarySymmetric.rocEndpointTest record.level).measurable_stop).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))

theorem measurableSet_simulatorEndpointError (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) :
    MeasurableSet (simulatorEndpointError P record) := by
  have hg : Measurable (fun sample : Bool × (Bool × P.experiment.Tape) =>
      (flippedRecordDecision P record (sample.1, sample.2.2), sample.2.1)) := by
    apply Measurable.prodMk
    · exact (measurable_of_countable (fun guess : Bool => Bool.xor
        (record.decision.getD record.orientation) (endpointCoordinateFlip record.orientation guess))).comp
        (((P.binarySymmetric.rocEndpointTest record.level).measurable_decision).comp
          (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
    · exact measurable_fst.comp measurable_snd
  have hs : MeasurableSet {pair : Bool × Bool | pair.1 ≠ pair.2} :=
    (Set.to_countable _).measurableSet
  exact hs.preimage hg

theorem measurableSet_simulatorEndpointPosterior (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) :
    MeasurableSet (simulatorEndpointPosterior P record) := by
  have hg : Measurable (fun sample : Bool × (Bool × P.experiment.Tape) =>
      (recordEndpointGuess P record (sample.1, sample.2.2), sample.2.1)) :=
    (((P.binarySymmetric.rocEndpointTest record.level).measurable_decision).comp
      (measurable_fst.prodMk (measurable_snd.comp measurable_snd))).prodMk
      (measurable_fst.comp measurable_snd)
  have hm := (measurable_of_countable (fun pair : Bool × Bool =>
    reportedVirtualTruth record.orientation pair.1 pair.2)).comp hg
  change Measurable (fun sample : Bool × (Bool × P.experiment.Tape) =>
    recordVirtualTruth P record sample.2.1 (sample.1, sample.2.2)) at hm
  exact (hm (measurableSet_singleton record.orientation)).compl

theorem simulatorEndpointLaw_charge (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    (∫⁻ sample, simulatorEndpointCharge P record sample ∂simulatorEndpointLaw P fee hfee stage) =
      ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ) := by
  apply lintegral_simulatorEndpointLaw_of_conditional_constant P fee hfee stage _ (measurable_simulatorEndpointCharge P record)
  intro truth
  exact recordEndpoint_expectedCharge P record truth

theorem simulatorEndpointLaw_error (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    simulatorEndpointLaw P fee hfee stage (simulatorEndpointError P record) = ENNReal.ofReal (P.recordDecisionError record) := by
  apply simulatorEndpointLaw_measure_of_conditional_constant P fee hfee stage _ (measurableSet_simulatorEndpointError P record)
  intro truth
  exact flippedRecordDecision_error_probability P record truth

theorem simulatorEndpointLaw_posterior (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (stage : P.sharedInstance.Stage) (record : AuxiliaryRecord) :
    simulatorEndpointLaw P fee hfee stage (simulatorEndpointPosterior P record) = ENNReal.ofReal (P.recordPosteriorError record) := by
  apply simulatorEndpointLaw_measure_of_conditional_constant P fee hfee stage _ (measurableSet_simulatorEndpointPosterior P record)
  intro truth
  exact recordVirtualTruth_error_probability P record truth

end PDROC


