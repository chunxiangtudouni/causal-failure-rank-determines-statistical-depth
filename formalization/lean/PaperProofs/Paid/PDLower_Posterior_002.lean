module

public import PaperProofs.Paid.PDLower_Posterior_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Statistics

namespace PDLower

universe u
variable {Seed : Type u} [MeasurableSpace Seed]

theorem finitePosterior_mass_integral (P : BinarySymmetric.Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed) (x : Bool)
    (B : Set (Seed × P.experiment.StoppedWord)) (hB : MeasurableSet B) :
    (∫⁻ record, B.indicator (fun record => ENNReal.ofReal (P.wordPosteriorMass x record.2)) record
      ∂finiteBayesStoppedLaw P ν test) =
      (1 / 2 : ℝ≥0∞) * finiteTranscriptLaw P.experiment ν test x B := by
  rw [lintegral_indicator hB]
  rw [← withDensity_apply _ hB, finiteBayesStoppedLaw_posterior_withDensity, Measure.smul_apply, smul_eq_mul]

/-- The finite stopped sublaw supports posterior comparison for ANY
measurable non-MAP record decision and ANY measurable record gate. No
finite ET or a.s. return is assumed; infinity has no false empty-word atom. -/
theorem finitePosterior_error_lower (P : BinarySymmetric.Parameters) (ν : Measure Seed)
    (test : P.experiment.AdmissibleRule Seed)
    (decision : Seed × P.experiment.StoppedWord → Bool) (hd : Measurable decision)
    (B : Set (Seed × P.experiment.StoppedWord)) (hB : MeasurableSet B) :
    (∫⁻ record, B.indicator (fun record => ENNReal.ofReal (P.wordPosteriorError record.2)) record
      ∂finiteBayesStoppedLaw P ν test) ≤
      ∑ x : Bool, (1 / 2 : ℝ≥0∞) * finiteTranscriptLaw P.experiment ν test x
        (B ∩ {record | decision record ≠ x}) := by
  let f := fun (x : Bool) (record : Seed × P.experiment.StoppedWord) =>
    (B ∩ {record | decision record ≠ x}).indicator
      (fun record => ENNReal.ofReal (P.wordPosteriorMass x record.2)) record
  have hmeas (x : Bool) : Measurable (f x) :=
    ((measurable_of_countable (fun word => ENNReal.ofReal (P.wordPosteriorMass x word))).comp measurable_snd).indicator
      (hB.inter ((hd (measurableSet_singleton x)).compl))
  calc
    _ ≤ ∫⁻ record, (∑ x : Bool, f x record) ∂finiteBayesStoppedLaw P ν test := by
      apply lintegral_mono
      intro record
      change B.indicator (fun record => ENNReal.ofReal (P.wordPosteriorError record.2)) record ≤
        ∑ x : Bool, f x record
      by_cases hb : record ∈ B
      · rw [Set.indicator_of_mem hb, Fintype.sum_bool]
        change ENNReal.ofReal (P.wordPosteriorError record.2) ≤
          (B ∩ {record | decision record ≠ true}).indicator
            (fun record => ENNReal.ofReal (P.wordPosteriorMass true record.2)) record +
          (B ∩ {record | decision record ≠ false}).indicator
            (fun record => ENNReal.ofReal (P.wordPosteriorMass false record.2)) record
        cases hx : decision record with
        | false =>
          have ht : record ∈ B ∩ {record | decision record ≠ true} := ⟨hb, by simp [hx]⟩
          have hf : record ∉ B ∩ {record | decision record ≠ false} := by rintro ⟨_, hn⟩; exact hn hx
          rw [Set.indicator_of_mem ht, Set.indicator_of_notMem hf, add_zero]
          exact ENNReal.ofReal_le_ofReal (min_le_right _ _)
        | true =>
          have ht : record ∉ B ∩ {record | decision record ≠ true} := by rintro ⟨_, hn⟩; exact hn hx
          have hf : record ∈ B ∩ {record | decision record ≠ false} := ⟨hb, by simp [hx]⟩
          rw [Set.indicator_of_notMem ht, Set.indicator_of_mem hf, zero_add]
          exact ENNReal.ofReal_le_ofReal (min_le_left _ _)
      · rw [Set.indicator_of_notMem hb]
        exact bot_le
    _ = ∑ x : Bool, ∫⁻ record, f x record ∂finiteBayesStoppedLaw P ν test :=
      lintegral_finsetSum _ (fun x _ => hmeas x)
    _ = _ := by
      apply Finset.sum_congr rfl
      intro x _
      exact finitePosterior_mass_integral P ν test x _ (hB.inter ((hd (measurableSet_singleton x)).compl))

end PDLower
