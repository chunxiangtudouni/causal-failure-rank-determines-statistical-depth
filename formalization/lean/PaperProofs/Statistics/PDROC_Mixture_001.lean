module

public import PaperProofs.Statistics.BSCRoc

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Statistics
open PaperProofs.Statistics.BinarySymmetric
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

theorem hittingTestOnBool_conditionalError (P : Parameters) (m : ℕ) (x : Bool) :
    P.experiment.conditionalError fairGuessLaw (P.hittingTestOnBool m) x =
      P.experiment.conditionalError (Measure.dirac ()) (P.symmetricHittingTest m) x := by
  let event : Set P.experiment.Tape := {tape | (P.symmetricHittingTest m).rule.decision () tape ≠ x}
  have hB : {s : Bool × P.experiment.Tape | (P.hittingTestOnBool m).rule.decision s.1 s.2 ≠ x} =
      Set.univ ×ˢ event := by ext s; simp [event, hittingTestOnBool]
  have hU : {s : Unit × P.experiment.Tape | (P.symmetricHittingTest m).rule.decision s.1 s.2 ≠ x} =
      Set.univ ×ˢ event := by ext ⟨s, tape⟩; cases s; simp [event]
  simp only [BinaryExperiment.conditionalError, BinaryExperiment.conditionalLaw, hB, hU,
    Measure.prod_prod, measure_univ, one_mul]

theorem hittingTestOnBool_expectedCharge (P : Parameters) (m : ℕ) (x : Bool) :
    P.experiment.expectedObservationCharge fairGuessLaw (P.hittingTestOnBool m) x =
      P.experiment.expectedObservationCharge (Measure.dirac ()) (P.symmetricHittingTest m) x := by
  unfold BinaryExperiment.expectedObservationCharge BinaryExperiment.conditionalLaw
  have hB : Measurable (fun s : Bool × P.experiment.Tape =>
      P.experiment.observationCharge ((P.hittingTestOnBool m).rule.stop s.1 s.2)) :=
    (measurable_of_countable P.experiment.observationCharge).comp (P.hittingTestOnBool m).measurable_stop
  have hU : Measurable (fun s : Unit × P.experiment.Tape =>
      P.experiment.observationCharge ((P.symmetricHittingTest m).rule.stop s.1 s.2)) :=
    (measurable_of_countable P.experiment.observationCharge).comp (P.symmetricHittingTest m).measurable_stop
  rw [lintegral_prod _ hB.aemeasurable, lintegral_prod _ hU.aemeasurable]
  change (∫⁻ _ : Bool, ∫⁻ tape, P.experiment.observationCharge
      ((P.symmetricHittingTest m).rule.stop () tape) ∂P.experiment.tapeLaw x ∂fairGuessLaw) = _
  rw [lintegral_const, lintegral_dirac]
  simp only [measure_univ, mul_one]

theorem rocEndpointTest_conditionalError (P : Parameters) (m : ℕ) (x : Bool) :
    P.experiment.conditionalError fairGuessLaw (P.rocEndpointTest m) x =
      ENNReal.ofReal (P.endpointError m : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simpa only [P.rocEndpointTest_zero, P.endpointError_zero, Rat.cast_div, Rat.cast_one,
      Rat.cast_ofNat] using P.fairGuess_conditionalError x
  · rw [rocEndpointTest, ite_eq_right hm, hittingTestOnBool_conditionalError]
    exact P.symmetricHitting_conditionalError_eq m (Nat.one_le_iff_ne_zero.mpr hm) x

theorem rocEndpointTest_expectedCharge (P : Parameters) (m : ℕ) (x : Bool) :
    P.experiment.expectedObservationCharge fairGuessLaw (P.rocEndpointTest m) x =
      ENNReal.ofReal (P.endpointCharge m : ℝ) := by
  by_cases hm : m = 0
  · subst m
    simpa only [P.rocEndpointTest_zero, P.endpointCharge_zero, Rat.cast_zero,
      ENNReal.ofReal_zero] using P.fairGuess_expectedCharge x
  · rw [rocEndpointTest, ite_eq_right hm, hittingTestOnBool_expectedCharge]
    exact P.symmetricHitting_expectedCharge_eq m (Nat.one_le_iff_ne_zero.mpr hm) x

theorem lintegral_initialMixture (P : Parameters) (weight : Set.Icc (0 : ℝ) 1) (x : Bool)
    (f : (Bool × Bool) × P.experiment.Tape → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ s, f s ∂P.experiment.conditionalLaw (adjacentMixtureSeedLaw weight) x) =
      ENNReal.ofReal weight.val * (∫⁻ s, f ((true, s.1), s.2) ∂P.experiment.conditionalLaw fairGuessLaw x) +
      ENNReal.ofReal (1 - weight.val) * (∫⁻ s, f ((false, s.1), s.2) ∂P.experiment.conditionalLaw fairGuessLaw x) := by
  unfold BinaryExperiment.conditionalLaw adjacentMixtureSeedLaw
  rw [lintegral_prod _ hf.aemeasurable]
  rw [lintegral_prod _ hf.lintegral_prod_right'.aemeasurable]
  simp only [rocCoinLaw, lintegral_add_measure, lintegral_smul_measure, lintegral_dirac,
    smul_eq_mul]
  congr 2
  · exact (lintegral_prod _ (hf.comp ((measurable_const.prodMk measurable_fst).prodMk
      measurable_snd)).aemeasurable).symm
  · exact (lintegral_prod _ (hf.comp ((measurable_const.prodMk measurable_fst).prodMk
      measurable_snd)).aemeasurable).symm



theorem adjacentMixture_conditionalError_mix (P : Parameters)
    (weight : Set.Icc (0 : ℝ) 1) (m : ℕ) (x : Bool) :
    P.experiment.conditionalError (adjacentMixtureSeedLaw weight) (P.adjacentMixtureTest m) x =
      ENNReal.ofReal weight.val * P.experiment.conditionalError fairGuessLaw (P.rocEndpointTest m) x +
      ENNReal.ofReal (1 - weight.val) * P.experiment.conditionalError fairGuessLaw (P.rocEndpointTest (m + 1)) x := by
  let A : Set ((Bool × Bool) × P.experiment.Tape) :=
    {s | (P.adjacentMixtureTest m).rule.decision s.1 s.2 ≠ x}
  have hA : MeasurableSet A := by
    exact ((P.adjacentMixtureTest m).measurable_decision (measurableSet_singleton x)).compl
  let f : (Bool × Bool) × P.experiment.Tape → ℝ≥0∞ := A.indicator 1
  have hf : Measurable f := measurable_const.indicator hA
  have hT : (fun s : Bool × P.experiment.Tape => f ((true, s.1), s.2)) =
      {s : Bool × P.experiment.Tape | (P.rocEndpointTest m).rule.decision s.1 s.2 ≠ x}.indicator 1 := by
    funext s
    simp [f, A, Set.indicator, adjacentMixtureTest]
  have hF : (fun s : Bool × P.experiment.Tape => f ((false, s.1), s.2)) =
      {s : Bool × P.experiment.Tape | (P.rocEndpointTest (m + 1)).rule.decision s.1 s.2 ≠ x}.indicator 1 := by
    funext s
    simp [f, A, Set.indicator, adjacentMixtureTest]
  have hEm : MeasurableSet {s : Bool × P.experiment.Tape | (P.rocEndpointTest m).rule.decision s.1 s.2 ≠ x} :=
    ((P.rocEndpointTest m).measurable_decision (measurableSet_singleton x)).compl
  have hEn : MeasurableSet {s : Bool × P.experiment.Tape | (P.rocEndpointTest (m + 1)).rule.decision s.1 s.2 ≠ x} :=
    ((P.rocEndpointTest (m + 1)).measurable_decision (measurableSet_singleton x)).compl
  have h := lintegral_initialMixture P weight x f hf
  rw [hT, hF] at h
  rw [lintegral_indicator_one hA,
    lintegral_indicator_one hEm, lintegral_indicator_one hEn] at h
  exact h

theorem adjacentMixture_expectedCharge_mix (P : Parameters)
    (weight : Set.Icc (0 : ℝ) 1) (m : ℕ) (x : Bool) :
    P.experiment.expectedObservationCharge (adjacentMixtureSeedLaw weight) (P.adjacentMixtureTest m) x =
      ENNReal.ofReal weight.val * P.experiment.expectedObservationCharge fairGuessLaw (P.rocEndpointTest m) x +
      ENNReal.ofReal (1 - weight.val) * P.experiment.expectedObservationCharge fairGuessLaw (P.rocEndpointTest (m + 1)) x := by
  have hf : Measurable (fun s : (Bool × Bool) × P.experiment.Tape =>
      P.experiment.observationCharge ((P.adjacentMixtureTest m).rule.stop s.1 s.2)) :=
    (measurable_of_countable P.experiment.observationCharge).comp (P.adjacentMixtureTest m).measurable_stop
  simpa only [BinaryExperiment.expectedObservationCharge, adjacentMixtureTest, ↓reduceIte, Bool.false_eq_true] using
    lintegral_initialMixture P weight x _ hf

theorem adjacentMixtureAttains (P : Parameters) : P.RocAdjacentMixtureAttains := by
  intro p hp hhalf
  dsimp only
  constructor
  · intro x
    rw [adjacentMixture_conditionalError_mix, rocEndpointTest_conditionalError,
      rocEndpointTest_conditionalError]
    rw [← ENNReal.ofReal_mul (P.rocInitialWeight p hp hhalf).property.1,
      ← ENNReal.ofReal_mul (sub_nonneg.mpr (P.rocInitialWeight p hp hhalf).property.2),
      ← ENNReal.ofReal_add]
    · congr 1
      exact P.rocWeight_error_interpolation _ p
    · exact mul_nonneg (P.rocInitialWeight p hp hhalf).property.1 (by exact_mod_cast (P.endpointError_pos _).le)
    · exact mul_nonneg (sub_nonneg.mpr (P.rocInitialWeight p hp hhalf).property.2) (by exact_mod_cast (P.endpointError_pos _).le)
  · intro x
    rw [adjacentMixture_expectedCharge_mix, rocEndpointTest_expectedCharge,
      rocEndpointTest_expectedCharge, P.rocPrice_of_pos p hp hhalf]
    rw [← ENNReal.ofReal_mul (P.rocInitialWeight p hp hhalf).property.1,
      ← ENNReal.ofReal_mul (sub_nonneg.mpr (P.rocInitialWeight p hp hhalf).property.2),
      ← ENNReal.ofReal_add]
    · rfl
    · exact mul_nonneg (P.rocInitialWeight p hp hhalf).property.1 (by exact_mod_cast P.endpointCharge_nonneg _)
    · exact mul_nonneg (sub_nonneg.mpr (P.rocInitialWeight p hp hhalf).property.2) (by exact_mod_cast P.endpointCharge_nonneg _)

end PDROC


