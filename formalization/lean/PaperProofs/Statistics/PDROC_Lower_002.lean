module
public import PaperProofs.Statistics.PDROC_Lower_001

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Statistics.BinarySymmetric
namespace PDROC
universe u
section
variable {Seed : Type u} [MeasurableSpace Seed]

instance bayesStoppedLaw_probability (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) : IsProbabilityMeasure (P.bayesStoppedLaw ν test) := by
  constructor
  simpa only [Parameters.bayesStoppedLaw, Measure.add_apply, Measure.smul_apply, measure_univ,
    smul_eq_mul, mul_one, one_div] using ENNReal.inv_two_add_inv_two

def decisionErrorSet (P : Parameters) (test : P.experiment.AdmissibleRule Seed) (x : Bool) :
    Set (Seed × P.experiment.StoppedWord) := {record | P.experiment.decodedStoppedDecision test record ≠ x}

theorem decisionErrorSet_measurable (P : Parameters) (test : P.experiment.AdmissibleRule Seed) (x : Bool) :
    MeasurableSet (decisionErrorSet P test x) :=
  ((P.experiment.measurable_decodedStoppedDecision test) (measurableSet_singleton x)).compl

theorem transcriptLaw_decisionErrorSet (P : Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (x : Bool)
    (hf : P.experiment.expectedSamples ν test x ≠ ⊤) :
    P.experiment.transcriptLaw ν test x (decisionErrorSet P test x) = P.experiment.conditionalError ν test x := by
  rw [← P.experiment.decisionLaw_error, ← P.experiment.transcriptLaw_decodedDecision ν test x hf,
    Measure.map_apply (P.experiment.measurable_decodedStoppedDecision test) (measurableSet_singleton (!x))]
  congr 1
  ext record
  cases x <;> cases hd : P.experiment.decodedStoppedDecision test record <;>
    simp [decisionErrorSet, hd]

theorem posteriorMass_le_one (P : Parameters) (x : Bool) (word : P.experiment.StoppedWord) :
    P.wordPosteriorMass x word ≤ 1 := by
  have hs := P.wordPosteriorMass_sum word
  have hf := P.wordPosteriorMass_pos false word
  have ht := P.wordPosteriorMass_pos true word
  cases x <;> linarith

theorem posteriorMass_integrable (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) (x : Bool) :
    Integrable (fun record : Seed × P.experiment.StoppedWord => P.wordPosteriorMass x record.2)
      (P.bayesStoppedLaw ν test) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_of_countable (P.wordPosteriorMass x)).comp measurable_snd).aestronglyMeasurable
  exact ae_of_all _ fun record => by
    change ‖P.wordPosteriorMass x record.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (P.wordPosteriorMass_pos x record.2)]
    exact posteriorMass_le_one P x record.2

noncomputable def decisionPosteriorError (P : Parameters) (test : P.experiment.AdmissibleRule Seed)
    (record : Seed × P.experiment.StoppedWord) : ℝ :=
  ∑ x : Bool, (decisionErrorSet P test x).indicator
    (fun record => P.wordPosteriorMass x record.2) record

theorem integral_posteriorMass_error (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed)
    (hf : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) (x : Bool) :
    (∫ record, (decisionErrorSet P test x).indicator
      (fun record => P.wordPosteriorMass x record.2) record ∂(P.bayesStoppedLaw ν test)) =
      (1 / 2 : ℝ) * (P.experiment.conditionalError ν test x).toReal := by
  have hm : Measurable (fun record : Seed × P.experiment.StoppedWord =>
      ENNReal.ofReal (P.wordPosteriorMass x record.2)) :=
    (measurable_of_countable (fun word => ENNReal.ofReal (P.wordPosteriorMass x word))).comp measurable_snd
  have ht : ∀ᵐ record ∂(P.bayesStoppedLaw ν test), ENNReal.ofReal (P.wordPosteriorMass x record.2) < ⊤ :=
    ae_of_all _ fun _ => ENNReal.ofReal_lt_top
  have h := integral_withDensity_eq_integral_toReal_smul hm ht
    ((decisionErrorSet P test x).indicator (1 : (Seed × P.experiment.StoppedWord) → ℝ))
  rw [P.bayesStoppedLaw_posterior_withDensity ν test hf x, integral_smul_measure,
    integral_indicator_one (decisionErrorSet_measurable P test x), measureReal_def,
    transcriptLaw_decisionErrorSet P ν test x (hf x)] at h
  have hid : (fun record : Seed × P.experiment.StoppedWord =>
      (ENNReal.ofReal (P.wordPosteriorMass x record.2)).toReal •
        (decisionErrorSet P test x).indicator (1 : (Seed × P.experiment.StoppedWord) → ℝ) record) =
      (decisionErrorSet P test x).indicator (fun record => P.wordPosteriorMass x record.2) := by
    funext record
    by_cases hr : record ∈ decisionErrorSet P test x <;>
      simp [hr, ENNReal.toReal_ofReal (P.wordPosteriorMass_pos x record.2).le]
  rw [hid] at h
  simpa only [ENNReal.toReal_div, ENNReal.toReal_one, ENNReal.toReal_ofNat, smul_eq_mul] using h.symm

theorem decisionPosteriorError_integrable (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) :
    Integrable (decisionPosteriorError P test) (P.bayesStoppedLaw ν test) := by
  unfold decisionPosteriorError
  exact integrable_finsetSum _ fun x _ =>
    (posteriorMass_integrable P ν test x).indicator (decisionErrorSet_measurable P test x)

theorem integral_decisionPosteriorError (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed)
    (hf : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) :
    (∫ record, decisionPosteriorError P test record ∂(P.bayesStoppedLaw ν test)) =
      (P.experiment.bayesError ν test).toReal := by
  unfold decisionPosteriorError
  rw [integral_finsetSum _ (fun x _ =>
    (posteriorMass_integrable P ν test x).indicator (decisionErrorSet_measurable P test x))]
  simp_rw [integral_posteriorMass_error P ν test hf]
  unfold PaperProofs.Statistics.BinaryExperiment.bayesError
  rw [ENNReal.toReal_sum (f := fun x : Bool => P.experiment.priorMass x * P.experiment.conditionalError ν test x)
    (fun x hx => ENNReal.sum_ne_top.mp (P.roc_bayesError_ne_top ν test) x hx)]
  simp only [P.priorMass_eq_half, ENNReal.toReal_mul, ENNReal.toReal_div,
    ENNReal.toReal_one, ENNReal.toReal_ofNat]
/-- A non-MAP output may have error anywhere between the two posterior
masses. Both sides are pointwise statements on the actual stopped record. -/
theorem posteriorError_bounds_decision (P : Parameters) (test : P.experiment.AdmissibleRule Seed)
    (record : Seed × P.experiment.StoppedWord) :
    P.wordPosteriorError record.2 ≤ decisionPosteriorError P test record ∧
      P.wordPosteriorError record.2 ≤ 1 - decisionPosteriorError P test record := by
  have hs := P.wordPosteriorMass_sum record.2
  unfold decisionPosteriorError
  rw [Fintype.sum_bool]
  cases hd : P.experiment.decodedStoppedDecision test record <;>
    simp only [decisionErrorSet, Set.indicator_apply, Set.mem_ofPred_eq, hd,
      Bool.false_eq_true, Bool.true_eq_false, ne_eq, not_false_eq_true, not_true_eq_false,
      ↓reduceIte, add_zero, zero_add]
  · constructor
    · exact min_le_right _ _
    · unfold Parameters.wordPosteriorError
      linarith only [min_le_left (P.wordPosteriorMass false record.2) (P.wordPosteriorMass true record.2), hs]
  · constructor
    · exact min_le_left _ _
    · unfold Parameters.wordPosteriorError
      linarith only [min_le_right (P.wordPosteriorMass false record.2) (P.wordPosteriorMass true record.2), hs]

theorem posteriorError_integrable (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed) :
    Integrable (fun record : Seed × P.experiment.StoppedWord => P.wordPosteriorError record.2)
      (P.bayesStoppedLaw ν test) := by
  apply (integrable_const (1 : ℝ)).mono'
    ((measurable_of_countable P.wordPosteriorError).comp measurable_snd).aestronglyMeasurable
  exact ae_of_all _ fun record => by
    change ‖P.wordPosteriorError record.2‖ ≤ 1
    rw [Real.norm_eq_abs, abs_of_pos (P.wordPosteriorError_pos record.2)]
    linarith [P.wordPosteriorError_le_half record.2]

/-- The mean actual posterior Bayes error is at most the error of either
orientation of any causal randomized decision; no MAP restriction is used. -/
theorem integral_posteriorError_le_adjusted (P : Parameters) (ν : Measure Seed) [IsProbabilityMeasure ν]
    (test : P.experiment.AdmissibleRule Seed)
    (hf : ∀ x, P.experiment.expectedSamples ν test x ≠ ⊤) :
    (∫ record : Seed × P.experiment.StoppedWord, P.wordPosteriorError record.2
      ∂(P.bayesStoppedLaw ν test)) ≤ P.adjustedBayesError ν test := by
  have hi := posteriorError_integrable P ν test
  have he := decisionPosteriorError_integrable P ν test
  have herr : (∫ record, decisionPosteriorError P test record ∂(P.bayesStoppedLaw ν test)) =
      (P.experiment.bayesError ν test).toReal := integral_decisionPosteriorError P ν test hf
  unfold Parameters.adjustedBayesError Parameters.rocBayesError
  dsimp only
  apply le_min
  · rw [← herr]
    exact integral_mono_ae hi he (ae_of_all _ fun record => (posteriorError_bounds_decision P test record).1)
  · have h := integral_mono_ae hi ((integrable_const (1 : ℝ)).sub he)
      (ae_of_all _ fun record => (posteriorError_bounds_decision P test record).2)
    simp only [Pi.sub_apply] at h
    rw [integral_sub (integrable_const (1 : ℝ)) he, integral_const, measureReal_def,
      measure_univ, ENNReal.toReal_one, one_smul, herr] at h
    exact h

end
end PDROC




