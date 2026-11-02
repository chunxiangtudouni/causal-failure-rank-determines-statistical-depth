module

public import PaperProofs.Paid.PDROC_RecordCoupling_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

noncomputable def flippedRecordDecision (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord)
    (sample : Bool × P.binarySymmetric.experiment.Tape) : Bool :=
  Bool.xor (record.decision.getD record.orientation)
    (endpointCoordinateFlip record.orientation (recordEndpointGuess P record sample))

theorem flippedRecordDecision_error_probability (P : PaperProofs.Paid.Parameters)
    (record : AuxiliaryRecord) (actualTruth : Bool) :
    P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth
      {sample | flippedRecordDecision P record sample ≠ actualTruth} =
      ENNReal.ofReal (P.recordDecisionError record) := by
  let d := record.decision.getD record.orientation
  have hset : {sample | flippedRecordDecision P record sample ≠ actualTruth} =
      {sample | recordVirtualTruth P record actualTruth sample = !d} := by
    ext sample
    change (Bool.xor d (endpointCoordinateFlip record.orientation (recordEndpointGuess P record sample)) ≠ actualTruth) ↔ _
    rw [flippedWrite_error_iff]
    change (d ≠ recordVirtualTruth P record actualTruth sample) ↔
      (recordVirtualTruth P record actualTruth sample = (!d))
    cases d <;> cases recordVirtualTruth P record actualTruth sample <;> decide
  rw [hset, recordVirtualTruth_singleton_probability]
  congr 1
  by_cases hd : d = record.orientation
  · change _ = if d = record.orientation then P.recordPosteriorError record else 1 - P.recordPosteriorError record
    rw [ite_eq_left hd, hd]
    exact auxiliaryRecord_posteriorMass_opposite P record
  · have hnot : (!d) = record.orientation := by
      cases hdval : d <;> cases hori : record.orientation <;> simp_all
    change _ = if d = record.orientation then P.recordPosteriorError record else 1 - P.recordPosteriorError record
    rw [ite_eq_right hd, hnot]
    exact auxiliaryRecord_posteriorMass_oriented P record

universe u

theorem lintegral_source_rectangle {Source Ω : Type*} [MeasurableSpace Source] [MeasurableSpace Ω]
    (ρ : Measure Source) [IsProbabilityMeasure ρ] (μ : Measure Ω) [IsProbabilityMeasure μ]
    (B : Set Source) (hB : MeasurableSet B) (f : Ω → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ pair, (B ×ˢ Set.univ).indicator (fun pair : Source × Ω => f pair.2) pair ∂(ρ.prod μ)) =
      (∫⁻ sample, f sample ∂μ) * ρ B := by
  have hm : Measurable (fun pair : Source × Ω =>
      (B ×ˢ Set.univ).indicator (fun pair : Source × Ω => f pair.2) pair) :=
    (hf.comp measurable_snd).indicator (hB.prod MeasurableSet.univ)
  rw [lintegral_prod _ hm.aemeasurable]
  have hinner (source : Source) :
      (∫⁻ sample, (B ×ˢ Set.univ).indicator (fun pair : Source × Ω => f pair.2) (source, sample) ∂μ) =
        B.indicator (fun _ => ∫⁻ sample, f sample ∂μ) source := by
    by_cases hs : source ∈ B <;> simp [Set.indicator, hs]
  simp_rw [hinner]
  rw [lintegral_indicator hB]
  simp

/-- The exact D06 observation-fee cell on a source gate, conditionally on
either real truth. The gate can include the preselected auxiliary record;
the fresh endpoint coin and real tape remain integrated, including at m=0. -/
theorem recordCell_observationCharge (P : PaperProofs.Paid.Parameters)
    {Source : Type u} [MeasurableSpace Source] (ρ : Measure Source) [IsProbabilityMeasure ρ]
    (B : Set Source) (hB : MeasurableSet B) (record : AuxiliaryRecord) (actualTruth : Bool) :
    (∫⁻ pair, (B ×ˢ Set.univ).indicator
      (fun pair : Source × (Bool × P.binarySymmetric.experiment.Tape) =>
        P.binarySymmetric.experiment.observationCharge
          ((P.binarySymmetric.rocEndpointTest record.level).rule.stop pair.2.1 pair.2.2)) pair
        ∂(ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth))) =
      ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ) * ρ B := by
  have hf : Measurable (fun sample : Bool × P.binarySymmetric.experiment.Tape =>
      P.binarySymmetric.experiment.observationCharge
        ((P.binarySymmetric.rocEndpointTest record.level).rule.stop sample.1 sample.2)) :=
    (measurable_of_countable P.binarySymmetric.experiment.observationCharge).comp
      (P.binarySymmetric.rocEndpointTest record.level).measurable_stop
  exact (lintegral_source_rectangle ρ _ B hB _ hf).trans
    (congrArg (fun charge => charge * ρ B) (recordEndpoint_expectedCharge P record actualTruth))

theorem recordCell_actualError (P : PaperProofs.Paid.Parameters)
    {Source : Type u} [MeasurableSpace Source] (ρ : Measure Source) [IsProbabilityMeasure ρ]
    (B : Set Source) (_hB : MeasurableSet B) (record : AuxiliaryRecord) (actualTruth : Bool) :
    (ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth))
      ((B ×ˢ Set.univ) ∩ {pair : Source × (Bool × P.binarySymmetric.experiment.Tape) |
        flippedRecordDecision P record pair.2 ≠ actualTruth}) =
      ENNReal.ofReal (P.recordDecisionError record) * ρ B := by
  have hset : (B ×ˢ Set.univ) ∩ {pair : Source × (Bool × P.binarySymmetric.experiment.Tape) |
      flippedRecordDecision P record pair.2 ≠ actualTruth} =
      B ×ˢ {sample | flippedRecordDecision P record sample ≠ actualTruth} := by ext pair; simp
  rw [hset, Measure.prod_prod, flippedRecordDecision_error_probability, mul_comm]

theorem recordCell_virtualPosterior (P : PaperProofs.Paid.Parameters)
    {Source : Type u} [MeasurableSpace Source] (ρ : Measure Source) [IsProbabilityMeasure ρ]
    (B : Set Source) (_hB : MeasurableSet B) (record : AuxiliaryRecord) (actualTruth : Bool) :
    (ρ.prod (P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth))
      ((B ×ˢ Set.univ) ∩ {pair : Source × (Bool × P.binarySymmetric.experiment.Tape) |
        recordVirtualTruth P record actualTruth pair.2 ≠ record.orientation}) =
      ENNReal.ofReal (P.recordPosteriorError record) * ρ B := by
  have hset : (B ×ˢ Set.univ) ∩ {pair : Source × (Bool × P.binarySymmetric.experiment.Tape) |
      recordVirtualTruth P record actualTruth pair.2 ≠ record.orientation} =
      B ×ˢ {sample | recordVirtualTruth P record actualTruth sample ≠ record.orientation} := by ext pair; simp
  rw [hset, Measure.prod_prod, recordVirtualTruth_error_probability, mul_comm]

end PDROC
