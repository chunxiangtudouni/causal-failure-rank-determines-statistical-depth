module

public import PaperProofs.Statistics.LocalTest
public import Mathlib.Probability.ProbabilityMassFunction.Integrals
public import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

/-!
The finite full-support formula `D_ix` is the actual Mathlib measure KL.
The proof computes the Radon-Nikodym derivative from its integral on each
positive singleton; no stopped-information theorem is used or assumed.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperProofs.Statistics.BinaryExperiment

theorem channelLaw_singleton (E : BinaryExperiment) (x : Bool) (y : Fin E.alphabetSize) :
    E.channelLaw x {y} = ENNReal.ofReal (E.channelReal x y) := by
  change (E.channelPMF x).toMeasure {y} = _
  rw [PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton y)]
  rfl

theorem channelLaw_singleton_pos (E : BinaryExperiment) (x : Bool) (y : Fin E.alphabetSize) :
    0 < E.channelLaw x {y} := by
  rw [E.channelLaw_singleton]
  exact ENNReal.ofReal_pos.mpr (E.channelReal_pos x y)

theorem channelLaw_absolutelyContinuous (E : BinaryExperiment) (x x' : Bool) :
    E.channelLaw x ≪ E.channelLaw x' := by
  intro s hs
  have hempty : s = ∅ := by
    apply Set.eq_empty_iff_forall_notMem.mpr
    intro y hy
    have hle : E.channelLaw x' {y} ≤ 0 := by
      rw [← hs]
      exact measure_mono (Set.singleton_subset_iff.mpr hy)
    exact (not_le_of_gt (E.channelLaw_singleton_pos x' y)) hle
  simp [hempty]

theorem channelLaw_rnDeriv (E : BinaryExperiment) (x x' : Bool) (y : Fin E.alphabetSize) :
    (E.channelLaw x).rnDeriv (E.channelLaw x') y =
      E.channelLaw x {y} / E.channelLaw x' {y} := by
  have h := Measure.setLIntegral_rnDeriv
    (E.channelLaw_absolutelyContinuous x x') ({y} : Set (Fin E.alphabetSize))
  rw [lintegral_singleton] at h
  apply (ENNReal.eq_div_iff (ne_of_gt (E.channelLaw_singleton_pos x' y))
    (by rw [E.channelLaw_singleton]; exact ENNReal.ofReal_ne_top)).mpr
  simpa [mul_comm] using h

theorem channelLaw_llr (E : BinaryExperiment) (x x' : Bool) (y : Fin E.alphabetSize) :
    llr (E.channelLaw x) (E.channelLaw x') y =
      Real.log (E.channelReal x y / E.channelReal x' y) := by
  rw [llr, E.channelLaw_rnDeriv, ENNReal.toReal_div,
    E.channelLaw_singleton, E.channelLaw_singleton,
    ENNReal.toReal_ofReal (E.channelReal_pos x y).le,
    ENNReal.toReal_ofReal (E.channelReal_pos x' y).le]

theorem channelLaw_integral_llr (E : BinaryExperiment) (x : Bool) :
    ∫ y, llr (E.channelLaw x) (E.channelLaw (!x)) y ∂(E.channelLaw x) =
      E.divergence x := by
  change ∫ y, llr (E.channelLaw x) (E.channelLaw (!x)) y ∂(E.channelPMF x).toMeasure = _
  rw [PMF.integral_eq_sum]
  unfold divergence
  apply Finset.sum_congr rfl
  intro y _
  rw [E.channelLaw_llr]
  change (ENNReal.ofReal (E.channelReal x y)).toReal * _ = _
  rw [ENNReal.toReal_ofReal (E.channelReal_pos x y).le]

theorem channelLaw_klDiv (E : BinaryExperiment) (x : Bool) :
    InformationTheory.klDiv (E.channelLaw x) (E.channelLaw (!x)) =
      ENNReal.ofReal (E.divergence x) := by
  rw [InformationTheory.klDiv_of_ac_of_integrable
    (E.channelLaw_absolutelyContinuous x (!x)) Integrable.of_finite]
  simp [E.channelLaw_integral_llr]

/-- Closes the encoding obligation declared in LocalTest, without new assumptions. -/
theorem channelDivergenceAgreement (E : BinaryExperiment) : E.ChannelDivergenceAgreement :=
  E.channelLaw_klDiv

end PaperProofs.Statistics.BinaryExperiment
