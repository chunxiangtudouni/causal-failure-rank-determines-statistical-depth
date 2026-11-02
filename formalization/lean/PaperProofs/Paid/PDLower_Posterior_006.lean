module

public import PaperProofs.Paid.PDLower_Posterior_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem lintegral_finiteTranscriptLaw (E : BinaryExperiment) (ν : Measure Seed)
    (test : E.AdmissibleRule Seed) (x : Bool)
    (f : Seed × E.StoppedWord → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ record, f record ∂finiteTranscriptLaw E ν test x) =
      ∫⁻ sample, {sample | test.rule.stop sample.1 sample.2 ≠ ⊤}.indicator
        (fun sample => f (E.stoppedTranscript test sample)) sample ∂E.conditionalLaw ν x := by
  rw [finiteTranscriptLaw, lintegral_map hf (E.measurable_stoppedTranscript test)]
  exact (lintegral_indicator ((test.measurable_stop (measurableSet_singleton (⊤ : ℕ∞))).compl)
    (fun sample => f (E.stoppedTranscript test sample))).symm

theorem lintegral_finiteBayesStoppedLaw (P : BinarySymmetric.Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed)
    (f : Seed × P.experiment.StoppedWord → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ record, f record ∂finiteBayesStoppedLaw P ν test) =
      ∑ x : Bool, (1 / 2 : ℝ≥0∞) *
        ∫⁻ sample, {sample | test.rule.stop sample.1 sample.2 ≠ ⊤}.indicator
          (fun sample => f (P.experiment.stoppedTranscript test sample)) sample ∂P.experiment.conditionalLaw ν x := by
  rw [finiteBayesStoppedLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure,
    lintegral_finiteTranscriptLaw P.experiment ν test false f hf,
    lintegral_finiteTranscriptLaw P.experiment ν test true f hf, Fintype.sum_bool]
  simp only [smul_eq_mul]
  exact add_comm _ _

theorem finitePosterior_error_measure_lower (P : BinarySymmetric.Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed)
    (decision : Seed × P.experiment.StoppedWord → Bool) (hd : Measurable decision)
    (B : Set (Seed × P.experiment.StoppedWord)) (hB : MeasurableSet B) :
    (∫⁻ record, B.indicator (fun record => ENNReal.ofReal (P.wordPosteriorError record.2)) record
      ∂finiteBayesStoppedLaw P ν test) ≤
      ∑ x : Bool, (1 / 2 : ℝ≥0∞) *
        (P.experiment.conditionalLaw ν x)
          {sample | test.rule.stop sample.1 sample.2 ≠ ⊤ ∧
            P.experiment.stoppedTranscript test sample ∈ B ∧
            decision (P.experiment.stoppedTranscript test sample) ≠ x} := by
  have h := finitePosterior_error_lower P ν test decision hd B hB
  apply h.trans_eq
  apply Finset.sum_congr rfl
  intro x _
  congr 1
  have herr : MeasurableSet (B ∩ {record | decision record ≠ x}) :=
    hB.inter ((hd (measurableSet_singleton x)).compl)
  rw [finiteTranscriptLaw, Measure.map_apply (P.experiment.measurable_stoppedTranscript test) herr,
    Measure.restrict_apply (herr.preimage (P.experiment.measurable_stoppedTranscript test))]
  congr 1
  ext sample
  simp only [Set.mem_inter_iff, Set.mem_preimage, Set.mem_ofPred_eq]
  tauto

end PDLower
