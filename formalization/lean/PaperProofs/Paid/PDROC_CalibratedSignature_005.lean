module

public import PaperProofs.Statistics.BSCRoc

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

open MeasureTheory
open PaperProofs.Statistics.BinarySymmetric.Parameters
open scoped ENNReal

namespace PDROC.CalibratedSignature

variable {A B X : Type*} [MeasurableSpace A] [MeasurableSpace B] [MeasurableSpace X]

theorem measurable_initialSelector (f : Bool → A × B → X) (hf : ∀ branch, Measurable (f branch)) :
    Measurable (fun sample : (Bool × A) × B => f sample.1.1 (sample.1.2, sample.2)) := by
  have joint : Measurable (fun sample : Bool × (A × B) => f sample.1 sample.2) :=
    measurable_from_prod_countable_right hf
  exact joint.comp ((measurable_fst.comp measurable_fst).prodMk
    ((measurable_snd.comp measurable_fst).prodMk measurable_snd))

/-- One independent initial Bernoulli choice selects a whole measurable
branch. No stage is resampled and no branch-dependent observation is exposed
to the selector. The target space need not be countable. -/
theorem initialSelector_map (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (weight : Set.Icc (0 : ℝ) 1)
    (f : Bool → A × B → X) (hf : ∀ branch, Measurable (f branch)) :
    (((rocCoinLaw weight).prod μ).prod ν).map
        (fun sample => f sample.1.1 (sample.1.2, sample.2)) =
      ENNReal.ofReal weight.val • (μ.prod ν).map (f true) +
        ENNReal.ofReal (1 - weight.val) • (μ.prod ν).map (f false) := by
  have measurable := measurable_initialSelector f hf
  have branchLaw (branch : Bool) :
      (((Measure.dirac branch).prod μ).prod ν).map
          (fun sample => f sample.1.1 (sample.1.2, sample.2)) =
        (μ.prod ν).map (f branch) := by
    have product := Measure.map_prod_map μ ν
      (show Measurable (Prod.mk branch : A → Bool × A) from measurable_const.prodMk measurable_id)
      measurable_id
    simp only [Measure.map_id] at product
    rw [Measure.dirac_prod, product, Measure.map_map measurable (by fun_prop)]
    rfl
  have splitLaw : ((rocCoinLaw weight).prod μ).prod ν =
      ENNReal.ofReal weight.val • (((Measure.dirac true).prod μ).prod ν) +
        ENNReal.ofReal (1 - weight.val) • (((Measure.dirac false).prod μ).prod ν) := by
    simp only [rocCoinLaw, Measure.add_prod, Measure.prod_smul_left]
  rw [splitLaw, Measure.map_add _ _ measurable,
    Measure.map_smul _ measurable.aemeasurable, Measure.map_smul _ measurable.aemeasurable,
    branchLaw true, branchLaw false]

/-- The same single-selector identity for arbitrary measurable nonnegative
extended charges, including infinity on failed or nonreturning branches. -/
theorem lintegral_initialSelector (μ : Measure A) (ν : Measure B)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (weight : Set.Icc (0 : ℝ) 1)
    (f : Bool → A × B → ℝ≥0∞) (hf : ∀ branch, Measurable (f branch)) :
    (∫⁻ sample, f sample.1.1 (sample.1.2, sample.2) ∂((rocCoinLaw weight).prod μ).prod ν) =
      ENNReal.ofReal weight.val * (∫⁻ sample, f true sample ∂μ.prod ν) +
        ENNReal.ofReal (1 - weight.val) * (∫⁻ sample, f false sample ∂μ.prod ν) := by
  have laws := initialSelector_map μ ν weight f hf
  have integrals := congrArg (fun law : Measure ℝ≥0∞ => ∫⁻ value, value ∂law) laws
  simp only [lintegral_add_measure, lintegral_smul_measure, smul_eq_mul] at integrals
  rw [lintegral_map (f := fun value : ℝ≥0∞ => value) measurable_id (measurable_initialSelector f hf),
    lintegral_map (f := fun value : ℝ≥0∞ => value) measurable_id (hf true),
    lintegral_map (f := fun value : ℝ≥0∞ => value) measurable_id (hf false)] at integrals
  exact integrals

end PDROC.CalibratedSignature
