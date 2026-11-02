module

public import PaperProofs.Statistics.BSCRoc
public import PaperProofs.Statistics.BSCStoppedPosterior
public import Mathlib.Analysis.Convex.Slope

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Statistics.BinarySymmetric

namespace PDROC

/-- A secant to a convex function lies below it outside the secant interval. -/
theorem convex_secant_extension_le {f : ℝ → ℝ} {s : Set ℝ}
    (hf : ConvexOn ℝ s f) {a b q : ℝ} (ha : a ∈ s) (hb : b ∈ s)
    (hq : q ∈ s) (hab : a < b) (hout : q ≤ a ∨ b ≤ q) :
    (q - a) / (b - a) * f b + (1 - (q - a) / (b - a)) * f a ≤ f q := by
  have hgap : 0 < b - a := sub_pos.mpr hab
  have hid : (q - a) / (b - a) * f b + (1 - (q - a) / (b - a)) * f a =
      ((q - a) * f b + (b - q) * f a) / (b - a) := by
    field_simp
    ring
  rw [hid]
  apply (div_le_iff₀ hgap).mpr
  rcases hout with hqlo | hqhi
  · rcases hqlo.eq_or_lt with hqa | hqa
    · subst q
      simp [mul_comm]
    · have hsl := hf.slope_mono_adjacent hq hb hqa hab
      have hgqa : 0 < a - q := sub_pos.mpr hqa
      have hmul := (div_le_div_iff₀ hgqa hgap).mp hsl
      nlinarith only [hmul]
  · rcases hqhi.eq_or_lt with hbq | hbq
    · subst q
      simp [mul_comm]
    · have hsl := hf.slope_mono_adjacent ha hq hab hbq
      have hgqb : 0 < q - b := sub_pos.mpr hbq
      have hmul := (div_le_div_iff₀ hgap hgqb).mp hsl
      nlinarith only [hmul]

/-- Every actual discrete endpoint is above every adjacent endpoint secant. -/
theorem rocChord_le_endpointCharge (P : Parameters) (m n : ℕ) :
    P.rocChord m (P.endpointError n : ℝ) ≤ (P.endpointCharge n : ℝ) := by
  have hmem (k : ℕ) : (P.endpointError k : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    constructor
    · exact_mod_cast P.endpointError_pos k
    · have hh := (Rat.cast_le (K := ℝ)).mpr (P.endpointError_le_half k)
      norm_num at hh
      exact hh
  have hab : (P.endpointError (m + 1) : ℝ) < (P.endpointError m : ℝ) := by
    exact_mod_cast P.endpointError_succ_lt m
  have hout : (P.endpointError n : ℝ) ≤ (P.endpointError (m + 1) : ℝ) ∨
      (P.endpointError m : ℝ) ≤ (P.endpointError n : ℝ) := by
    by_cases hnm : n ≤ m
    · right
      exact_mod_cast P.endpointError_strictAnti.antitone hnm
    · left
      exact_mod_cast P.endpointError_strictAnti.antitone (by omega : m + 1 ≤ n)
  have h := convex_secant_extension_le phiReal_convexOn (hmem (m + 1)) (hmem m)
    (hmem n) hab hout
  have hscaled := mul_le_mul_of_nonneg_left h P.a_pos.le
  unfold Parameters.rocChord Parameters.rocWeight
  rw [P.endpointCharge_eq_information m, P.endpointCharge_eq_information (m + 1),
    P.endpointCharge_eq_information n]
  nlinarith only [hscaled]

/-- The extension of each adjacent secant is decreasing. -/
theorem rocChord_antitone (P : Parameters) (m : ℕ) : Antitone (P.rocChord m) := by
  have herror : (P.endpointError (m + 1) : ℝ) < (P.endpointError m : ℝ) := by
    exact_mod_cast P.endpointError_succ_lt m
  have hmem (k : ℕ) : (P.endpointError k : ℝ) ∈ Set.Ioc (0 : ℝ) (1 / 2) := by
    constructor
    · exact_mod_cast P.endpointError_pos k
    · have hh := (Rat.cast_le (K := ℝ)).mpr (P.endpointError_le_half k)
      norm_num at hh
      exact hh
  have hphi := phiReal_strictAntiOn (hmem (m + 1)) (hmem m) herror
  have hcost : (P.endpointCharge m : ℝ) ≤ (P.endpointCharge (m + 1) : ℝ) := by
    rw [P.endpointCharge_eq_information m, P.endpointCharge_eq_information (m + 1)]
    exact mul_le_mul_of_nonneg_left hphi.le P.a_pos.le
  intro p q hpq
  have hw : P.rocWeight m p ≤ P.rocWeight m q :=
    (div_le_div_iff_of_pos_right (P.endpoint_gap_pos m)).mpr (by linarith)
  unfold Parameters.rocChord
  nlinarith [mul_nonneg (sub_nonneg.mpr hw) (sub_nonneg.mpr hcost)]

/-- Integer likelihood score of the actual finite observation word. -/
def wordSignedScore (P : Parameters) (word : P.experiment.StoppedWord) : ℤ :=
  ∑ k : Fin word.1, if (word.2 k).val = 1 then 1 else -1

theorem wordLogLikelihood_eq_signed (P : Parameters) (word : P.experiment.StoppedWord) :
    P.experiment.wordLogLikelihood true word = P.h * (wordSignedScore P word : ℝ) := by
  unfold PaperProofs.Statistics.BinaryExperiment.wordLogLikelihood wordSignedScore
  change (∑ k : Fin word.1, Real.log (P.experiment.channelReal true (word.2 k) /
    P.experiment.channelReal false (word.2 k))) = _
  rw [show (∑ k : Fin word.1, Real.log (P.experiment.channelReal true (word.2 k) /
    P.experiment.channelReal false (word.2 k))) =
      ∑ k : Fin word.1, P.h * (if (word.2 k).val = 1 then 1 else -1 : ℤ) from
    Finset.sum_congr rfl (fun k _ => P.logIncrement_eq_signed (word.2 k))]
  push_cast
  rw [Finset.mul_sum]

/-- Posterior odds of the minimum of two positive masses are the absolute
log likelihood ratio; no MAP decision premise enters this identity. -/
theorem log_odds_min_likelihoods (u v : ℝ) (hu : 0 < u) (hv : 0 < v) :
    Real.log ((1 - min (u / (u + v)) (v / (u + v))) /
      min (u / (u + v)) (v / (u + v))) = |Real.log (v / u)| := by
  have hs : 0 < u + v := add_pos hu hv
  by_cases huv : u ≤ v
  · rw [min_eq_left ((div_le_div_iff_of_pos_right hs).mpr huv)]
    have hr : (1 - u / (u + v)) / (u / (u + v)) = v / u := by field_simp; ring
    rw [hr, abs_of_nonneg (Real.log_nonneg ((one_le_div hu).mpr huv))]
  · have hvu : v ≤ u := (lt_of_not_ge huv).le
    rw [min_eq_right ((div_le_div_iff_of_pos_right hs).mpr hvu)]
    have hr : (1 - v / (u + v)) / (v / (u + v)) = u / v := by field_simp; ring
    rw [hr, abs_of_nonpos (Real.log_nonpos (div_pos hv hu).le ((div_le_one hu).mpr hvu)),
      Real.log_div hu.ne' hv.ne', Real.log_div hv.ne' hu.ne']
    ring

/-- Every real stopped-word posterior belongs to the original BSC endpoint
lattice, at its actual absolute integer score, including score zero. -/
theorem wordPosteriorError_eq_endpoint (P : Parameters) (word : P.experiment.StoppedWord) :
    P.wordPosteriorError word = (P.endpointError (wordSignedScore P word).natAbs : ℝ) := by
  have hlog : Real.log ((1 - P.wordPosteriorError word) / P.wordPosteriorError word) =
      ((wordSignedScore P word).natAbs : ℝ) * P.h := by
    have h := log_odds_min_likelihoods _ _ (P.experiment.wordProbability_pos false word)
      (P.experiment.wordProbability_pos true word)
    change Real.log ((1 - P.wordPosteriorError word) / P.wordPosteriorError word) = _ at h
    have hllr : Real.log (P.experiment.wordProbability true word / P.experiment.wordProbability false word) =
        P.experiment.wordLogLikelihood true word := by
      have hh := P.experiment.log_wordLikelihood true word
      rw [P.experiment.wordLikelihood_eq_div] at hh
      exact hh
    rw [hllr, wordLogLikelihood_eq_signed, abs_mul, abs_of_pos P.h_pos,
      ← Int.cast_abs, ← Nat.cast_natAbs] at h
    simpa only [mul_comm] using h
  have hp := P.wordPosteriorError_pos word
  have hph := P.wordPosteriorError_le_half word
  have he : 0 < (P.endpointError (wordSignedScore P word).natAbs : ℝ) := by
    exact_mod_cast P.endpointError_pos (wordSignedScore P word).natAbs
  have heh : (P.endpointError (wordSignedScore P word).natAbs : ℝ) ≤ 1 / 2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (P.endpointError_le_half (wordSignedScore P word).natAbs)
    norm_num at hh
    exact hh
  have hpp : 0 < 1 - P.wordPosteriorError word := by linarith
  have hepp : 0 < 1 - (P.endpointError (wordSignedScore P word).natAbs : ℝ) := by linarith
  have hlogeq := hlog.trans (P.endpointThreshold (wordSignedScore P word).natAbs).symm
  have hratio := Real.log_injOn_pos (show (1 - P.wordPosteriorError word) / P.wordPosteriorError word ∈ Set.Ioi 0 by exact div_pos hpp hp)
    (show (1 - (P.endpointError (wordSignedScore P word).natAbs : ℝ)) /
      (P.endpointError (wordSignedScore P word).natAbs : ℝ) ∈ Set.Ioi 0 by exact div_pos hepp he) hlogeq
  have hcross := (div_eq_div_iff hp.ne' he.ne').mp hratio
  nlinarith only [hcross]

/-- The fixed adjacent secant is below the actual finite-word information
charge. This is the discrete improvement over the ordinary Jensen bound. -/
theorem rocChord_le_wordInformation (P : Parameters) (m : ℕ) (word : P.experiment.StoppedWord) :
    P.rocChord m (P.wordPosteriorError word) ≤ P.a * phiReal (P.wordPosteriorError word) := by
  rw [wordPosteriorError_eq_endpoint]
  rw [← P.endpointCharge_eq_information]
  exact rocChord_le_endpointCharge P m _

end PDROC





