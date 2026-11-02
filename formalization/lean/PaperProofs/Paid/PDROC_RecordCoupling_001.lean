module
public import PaperProofs.Paid.PDROC_Records_001
public import PaperProofs.Statistics.PDROC_Mixture_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

/-- Coordinate flip is selected after the real endpoint guess, from that
causal guess and the already selected record orientation. It has no truth argument. -/
def endpointCoordinateFlip (orientation guess : Bool) : Bool := Bool.xor orientation guess

/-- Virtual truth is reconstructed only after the real truth report. -/
def reportedVirtualTruth (orientation guess actualTruth : Bool) : Bool :=
  Bool.xor (endpointCoordinateFlip orientation guess) actualTruth

theorem virtualTruth_error_eq_endpoint_error (orientation guess actualTruth : Bool) :
    (reportedVirtualTruth orientation guess actualTruth ≠ orientation) ↔ (guess ≠ actualTruth) := by
  cases orientation <;> cases guess <;> cases actualTruth <;> decide

/-- The original virtual write and its physically flipped real write have
exactly the same error on every path, including failure paths. -/
theorem flippedWrite_error_iff (decision orientation guess actualTruth : Bool) :
    (Bool.xor decision (endpointCoordinateFlip orientation guess) ≠ actualTruth) ↔
      (decision ≠ reportedVirtualTruth orientation guess actualTruth) := by
  cases decision <;> cases orientation <;> cases guess <;> cases actualTruth <;> decide

theorem auxiliaryRecord_posteriorMass_opposite (P : PaperProofs.Paid.Parameters)
    (record : AuxiliaryRecord) :
    P.binarySymmetric.wordPosteriorMass (!record.orientation)
      ⟨record.observations.length, fun k => record.observations[k.val]⟩ = P.recordPosteriorError record := by
  let word : P.binarySymmetric.experiment.StoppedWord :=
    ⟨record.observations.length, fun k => record.observations[k.val]⟩
  have hu := P.binarySymmetric.experiment.wordProbability_pos false word
  have hv := P.binarySymmetric.experiment.wordProbability_pos true word
  have he := P.binarySymmetric.wordEvidence_pos word
  have hlog : Real.log (P.binarySymmetric.experiment.wordProbability true word /
      P.binarySymmetric.experiment.wordProbability false word) = P.binarySymmetric.h * (record.score : ℝ) := by
    have h := P.binarySymmetric.experiment.log_wordLikelihood true word
    rw [P.binarySymmetric.experiment.wordLikelihood_eq_div, wordLogLikelihood_eq_signed,
      auxiliaryRecord_wordSignedScore] at h
    exact h
  have hpost := auxiliaryPosteriorLevels P record
  change min (P.binarySymmetric.wordPosteriorMass false word)
    (P.binarySymmetric.wordPosteriorMass true word) = _ at hpost
  by_cases hs : 0 ≤ record.score
  · have hr : 0 ≤ (record.score : ℝ) := by exact_mod_cast hs
    have hll : 0 ≤ Real.log (P.binarySymmetric.experiment.wordProbability true word /
        P.binarySymmetric.experiment.wordProbability false word) := by
      rw [hlog]
      exact mul_nonneg P.binarySymmetric.h_pos.le hr
    have hord := (Real.log_nonneg_iff (div_pos hv hu)).mp hll
    have huv := (one_le_div hu).mp hord
    have hmass : P.binarySymmetric.wordPosteriorMass false word ≤
        P.binarySymmetric.wordPosteriorMass true word := by
      exact (div_le_div_iff_of_pos_right he).mpr huv
    rw [min_eq_left hmass] at hpost
    simpa only [AuxiliaryRecord.orientation, hs, decide_true, Bool.not_true] using hpost
  · have hr : (record.score : ℝ) ≤ 0 := by exact_mod_cast (lt_of_not_ge hs).le
    have hll : Real.log (P.binarySymmetric.experiment.wordProbability true word /
        P.binarySymmetric.experiment.wordProbability false word) ≤ 0 := by
      rw [hlog]
      exact mul_nonpos_of_nonneg_of_nonpos P.binarySymmetric.h_pos.le hr
    have hord := (Real.log_nonpos_iff (div_pos hv hu).le).mp hll
    have hvu := (div_le_one hu).mp hord
    have hmass : P.binarySymmetric.wordPosteriorMass true word ≤
        P.binarySymmetric.wordPosteriorMass false word := by
      exact (div_le_div_iff_of_pos_right he).mpr hvu
    rw [min_eq_right hmass] at hpost
    simpa only [AuxiliaryRecord.orientation, hs, decide_false, Bool.not_false] using hpost

theorem auxiliaryRecord_posteriorMass_oriented (P : PaperProofs.Paid.Parameters)
    (record : AuxiliaryRecord) :
    P.binarySymmetric.wordPosteriorMass record.orientation
      ⟨record.observations.length, fun k => record.observations[k.val]⟩ = 1 - P.recordPosteriorError record := by
  have hs := P.binarySymmetric.wordPosteriorMass_sum
    ⟨record.observations.length, fun k => record.observations[k.val]⟩
  have ho := auxiliaryRecord_posteriorMass_opposite P record
  cases hb : record.orientation <;> simp only [hb, Bool.not_false, Bool.not_true] at ho ⊢ <;> linarith

noncomputable def recordEndpointGuess (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord)
    (sample : Bool × P.binarySymmetric.experiment.Tape) : Bool :=
  (P.binarySymmetric.rocEndpointTest record.level).rule.decision sample.1 sample.2

noncomputable def recordVirtualTruth (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord) (actualTruth : Bool)
    (sample : Bool × P.binarySymmetric.experiment.Tape) : Bool :=
  reportedVirtualTruth record.orientation (recordEndpointGuess P record sample) actualTruth

theorem measurable_recordVirtualTruth (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord)
    (actualTruth : Bool) : Measurable (recordVirtualTruth P record actualTruth) :=
  (measurable_of_countable (fun guess => reportedVirtualTruth record.orientation guess actualTruth)).comp
    (P.binarySymmetric.rocEndpointTest record.level).measurable_decision

/-- Each real truth gives exactly the same virtual posterior, by the two
conditional errors of the actual endpoint test; no future truth is sampled into a seed. -/
theorem recordVirtualTruth_error_probability (P : PaperProofs.Paid.Parameters) (record : AuxiliaryRecord)
    (actualTruth : Bool) :
    P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth
      {sample | recordVirtualTruth P record actualTruth sample ≠ record.orientation} =
      ENNReal.ofReal (P.recordPosteriorError record) := by
  have hset : {sample | recordVirtualTruth P record actualTruth sample ≠ record.orientation} =
      {sample | recordEndpointGuess P record sample ≠ actualTruth} := by
    ext sample
    exact virtualTruth_error_eq_endpoint_error _ _ _
  rw [hset]
  exact rocEndpointTest_conditionalError P.binarySymmetric record.level actualTruth

theorem recordVirtualTruth_singleton_probability (P : PaperProofs.Paid.Parameters)
    (record : AuxiliaryRecord) (actualTruth virtualTruth : Bool) :
    P.binarySymmetric.experiment.conditionalLaw fairGuessLaw actualTruth
      {sample | recordVirtualTruth P record actualTruth sample = virtualTruth} =
      ENNReal.ofReal (P.binarySymmetric.wordPosteriorMass virtualTruth
        ⟨record.observations.length, fun k => record.observations[k.val]⟩) := by
  by_cases ht : virtualTruth = record.orientation
  · subst virtualTruth
    rw [auxiliaryRecord_posteriorMass_oriented]
    have hs : {sample | recordVirtualTruth P record actualTruth sample = record.orientation} =
        {sample | recordVirtualTruth P record actualTruth sample ≠ record.orientation}ᶜ := by
      ext sample
      simp
    have hme : MeasurableSet {sample | recordVirtualTruth P record actualTruth sample ≠ record.orientation} :=
      ((measurable_recordVirtualTruth P record actualTruth) (measurableSet_singleton record.orientation)).compl
    rw [hs, measure_compl hme (measure_ne_top _ _), measure_univ, recordVirtualTruth_error_probability]
    rw [ENNReal.ofReal_sub 1 (P.recordPosteriorError_pos record).le]
    norm_num
  · have hv : virtualTruth = !record.orientation := by
      cases virtualTruth <;> cases hb : record.orientation <;> simp_all
    rw [hv, auxiliaryRecord_posteriorMass_opposite]
    have hs : {sample | recordVirtualTruth P record actualTruth sample = !record.orientation} =
        {sample | recordVirtualTruth P record actualTruth sample ≠ record.orientation} := by
      ext sample
      cases hv : recordVirtualTruth P record actualTruth sample <;> cases hb : record.orientation <;> simp
    rw [hs, recordVirtualTruth_error_probability]

theorem recordEndpoint_expectedCharge (P : PaperProofs.Paid.Parameters)
    (record : AuxiliaryRecord) (actualTruth : Bool) :
    P.binarySymmetric.experiment.expectedObservationCharge fairGuessLaw
      (P.binarySymmetric.rocEndpointTest record.level) actualTruth =
      ENNReal.ofReal (P.binarySymmetric.endpointCharge record.level : ℝ) :=
  rocEndpointTest_expectedCharge P.binarySymmetric record.level actualTruth

end PDROC


