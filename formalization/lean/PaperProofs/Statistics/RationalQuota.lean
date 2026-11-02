module

public import PaperProofs.Statistics.SPRTOverflow

/-!
The original rational certificate. Mathlib's `tvDist` is the
full L1 distance on probabilities; the paper's TV is half L1. The rational
finite-channel quantity below uses the paper's normalization explicitly.

Pinsker route comparison: binary data processing would require a new scalar
second-derivative argument. The selected route uses official finite Gibbs,
exponential tilting, and Hoeffding's bounded-observable MGF bound, optimized
at t = 4 * the difference of the observable means.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace PaperProofs.Statistics.BinaryExperiment

theorem boundedObservable_pinsker (E : BinaryExperiment) (x : Bool)
    (h : Fin E.alphabetSize → ℝ) (hbounded : ∀ y, h y ∈ Set.Icc 0 1) :
    2 * ((∫ y, h y ∂(E.channelLaw x)) - (∫ y, h y ∂(E.channelLaw (!x)))) ^ 2 ≤ E.divergence x := by
  let μ := E.channelLaw x
  let ν := E.channelLaw (!x)
  let gap := (∫ y, h y ∂μ) - (∫ y, h y ∂ν)
  let t := 4 * gap
  let f := fun y => t * (h y - ∫ z, h z ∂ν)
  have hfμ : Integrable f μ := Integrable.of_finite
  have hfν : Integrable (fun y => Real.exp (f y)) ν := Integrable.of_finite
  let : IsProbabilityMeasure (ν.tilted f) := isProbabilityMeasure_tilted hfν
  have hAC : μ ≪ ν := E.channelLaw_absolutelyContinuous x (!x)
  have hACTilt : μ ≪ ν.tilted f := hAC.trans (absolutelyContinuous_tilted hfν)
  have hGibbs := InformationTheory.integral_llr_add_sub_measure_univ_nonneg hACTilt
    (Integrable.of_finite : Integrable (llr μ (ν.tilted f)) μ)
  simp only [probReal_univ, add_sub_cancel_right] at hGibbs
  rw [integral_llr_tilted_right hAC hfμ hfν (Integrable.of_finite : Integrable (llr μ ν) μ)] at hGibbs
  have hmean : ∫ y, f y ∂μ = t * gap := by
    unfold f gap
    rw [integral_const_mul, integral_sub (Integrable.of_finite : Integrable h μ) (integrable_const _)]
    simp only [integral_const, probReal_univ, one_smul]
  rw [hmean] at hGibbs
  have hsubG := hasSubgaussianMGF_of_mem_Icc (μ := ν)
    (measurable_of_countable h).aemeasurable (ae_of_all _ hbounded)
  have hlogmgf := hsubG.cgf_le t
  norm_num at hlogmgf
  change Real.log (∫ y, Real.exp (f y) ∂ν) ≤ _ at hlogmgf
  have hD : ∫ y, llr μ ν y ∂μ = E.divergence x := E.channelLaw_integral_llr x
  rw [hD] at hGibbs
  change 2 * gap ^ 2 ≤ E.divergence x
  dsimp [t] at hGibbs hlogmgf
  nlinarith

def channelTVIndicator (E : BinaryExperiment) (y : Fin E.alphabetSize) : ℚ :=
  if 0 ≤ E.channel false y - E.channel true y then 1 else 0

/-- The usual probability TV = half the finite L1 distance, with rational arithmetic. -/
def channelTV (E : BinaryExperiment) : ℚ :=
  (∑ y : Fin E.alphabetSize, |E.channel false y - E.channel true y|) / 2

theorem channelTV_pos (E : BinaryExperiment) : 0 < E.channelTV := by
  apply div_pos _ (by norm_num : (0 : ℚ) < 2)
  obtain ⟨y, hy⟩ := Function.ne_iff.mp E.channel_distinct
  exact Finset.sum_pos' (fun _ _ => abs_nonneg _) ⟨y, Finset.mem_univ y, abs_pos.mpr (sub_ne_zero.mpr hy)⟩

theorem channelTV_eq_indicator_difference (E : BinaryExperiment) :
    E.channelTV = (∑ y : Fin E.alphabetSize, E.channel false y * E.channelTVIndicator y) -
      (∑ y : Fin E.alphabetSize, E.channel true y * E.channelTVIndicator y) := by
  have hpoint (y : Fin E.alphabetSize) : |E.channel false y - E.channel true y| =
      2 * ((E.channel false y - E.channel true y) * E.channelTVIndicator y) -
        (E.channel false y - E.channel true y) := by
    unfold channelTVIndicator
    split_ifs with hy
    · rw [abs_of_nonneg hy]
      ring
    · rw [abs_of_neg (lt_of_not_ge hy)]
      ring
  have hsum : (∑ y : Fin E.alphabetSize, (E.channel false y - E.channel true y)) = 0 := by
    rw [Finset.sum_sub_distrib, E.channel_sum false, E.channel_sum true, sub_self]
  have hdist : (∑ y : Fin E.alphabetSize, (E.channel false y - E.channel true y) * E.channelTVIndicator y) =
      (∑ y : Fin E.alphabetSize, E.channel false y * E.channelTVIndicator y) -
        (∑ y : Fin E.alphabetSize, E.channel true y * E.channelTVIndicator y) := by
    simp_rw [sub_mul, Finset.sum_sub_distrib]
  have habs : (∑ y : Fin E.alphabetSize, |E.channel false y - E.channel true y|) =
      2 * (∑ y : Fin E.alphabetSize, (E.channel false y - E.channel true y) * E.channelTVIndicator y) -
        (∑ y : Fin E.alphabetSize, (E.channel false y - E.channel true y)) := by
    calc
      _ = ∑ y : Fin E.alphabetSize, (2 * ((E.channel false y - E.channel true y) * E.channelTVIndicator y) -
          (E.channel false y - E.channel true y)) := Finset.sum_congr rfl (fun y _ => hpoint y)
      _ = _ := by rw [Finset.sum_sub_distrib, Finset.mul_sum]
  unfold channelTV
  rw [habs, hsum, sub_zero, hdist]
  ring

theorem integral_channelTVIndicator (E : BinaryExperiment) (x : Bool) :
    (∫ y, (E.channelTVIndicator y : ℝ) ∂(E.channelLaw x)) =
      ((∑ y : Fin E.alphabetSize, E.channel x y * E.channelTVIndicator y : ℚ) : ℝ) := by
  change (∫ y, (E.channelTVIndicator y : ℝ) ∂(E.channelPMF x).toMeasure) = _
  rw [PMF.integral_eq_sum]
  push_cast
  apply Finset.sum_congr rfl
  intro y _
  change (ENNReal.ofReal (E.channelReal x y)).toReal * _ = _
  rw [ENNReal.toReal_ofReal (E.channelReal_pos x y).le]
  rfl

theorem channelTV_eq_integral_difference (E : BinaryExperiment) :
    (E.channelTV : ℝ) = (∫ y, (E.channelTVIndicator y : ℝ) ∂(E.channelLaw false)) -
      (∫ y, (E.channelTVIndicator y : ℝ) ∂(E.channelLaw true)) := by
  rw [E.integral_channelTVIndicator false, E.integral_channelTVIndicator true]
  have h := congrArg (fun q : ℚ => (q : ℝ)) E.channelTV_eq_indicator_difference
  simpa only [Rat.cast_sub] using h

def channelDriftLower (E : BinaryExperiment) : ℚ := 2 * E.channelTV ^ 2

theorem channelDriftLower_pos (E : BinaryExperiment) : 0 < E.channelDriftLower :=
  mul_pos (by norm_num) (sq_pos_of_pos E.channelTV_pos)

/-- Exact finite full-support Pinsker with the paper's normalization and constant 2. -/
theorem channelDriftLower_le_divergence (E : BinaryExperiment) (x : Bool) :
    (E.channelDriftLower : ℝ) ≤ E.divergence x := by
  have hb (y : Fin E.alphabetSize) : (E.channelTVIndicator y : ℝ) ∈ Set.Icc 0 1 := by
    unfold channelTVIndicator
    split_ifs <;> norm_num
  have h := E.boundedObservable_pinsker x (fun y => (E.channelTVIndicator y : ℝ)) hb
  have hTV := E.channelTV_eq_integral_difference
  change ((2 * E.channelTV ^ 2 : ℚ) : ℝ) ≤ E.divergence x
  cases x with
  | false =>
    simp only [Bool.not_false] at h
    rw [← hTV] at h
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow] using h
  | true =>
    simp only [Bool.not_true] at h
    have hgap : (∫ y, (E.channelTVIndicator y : ℝ) ∂(E.channelLaw true)) -
        (∫ y, (E.channelTVIndicator y : ℝ) ∂(E.channelLaw false)) = -(E.channelTV : ℝ) := by linarith
    rw [hgap, neg_sq] at h
    simpa only [Rat.cast_mul, Rat.cast_ofNat, Rat.cast_pow] using h

theorem channelDriftLower_le_minDivergence (E : BinaryExperiment) :
    (E.channelDriftLower : ℝ) ≤ E.channelMinDivergence :=
  le_min (E.channelDriftLower_le_divergence false) (E.channelDriftLower_le_divergence true)

def ratioIntegerBound (ratio : ℚ) : ℕ :=
  Nat.clog 2 ⌈max ratio (1 / ratio)⌉₊

theorem ratioIntegerBound_comparisons (ratio : ℚ) :
    ratio ≤ (2 : ℚ) ^ ratioIntegerBound ratio ∧
      1 / ratio ≤ (2 : ℚ) ^ ratioIntegerBound ratio := by
  have hpow : max ratio (1 / ratio) ≤ (2 : ℚ) ^ ratioIntegerBound ratio := by
    calc
      _ ≤ (⌈max ratio (1 / ratio)⌉₊ : ℚ) := Nat.le_ceil _
      _ ≤ _ := by exact_mod_cast Nat.le_pow_clog (by norm_num : 1 < 2) ⌈max ratio (1 / ratio)⌉₊
  exact ⟨(le_max_left _ _).trans hpow, (le_max_right _ _).trans hpow⟩

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  simpa only [show (2 : ℝ) - 1 = 1 by norm_num] using Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)

theorem log_le_integer_of_le_two_pow (z : ℝ) (hz : 0 < z) (exponent : ℕ)
    (hpow : z ≤ (2 : ℝ) ^ exponent) : Real.log z ≤ exponent := by
  have h := Real.log_le_log hz hpow
  rw [Real.log_pow] at h
  exact h.trans (by nlinarith [log_two_le_one, (Nat.cast_nonneg exponent : (0 : ℝ) ≤ exponent)])

theorem abs_log_le_ratioIntegerBound (ratio : ℚ) (hratio : 0 < ratio) :
    |Real.log (ratio : ℝ)| ≤ ratioIntegerBound ratio := by
  have hr : (0 : ℝ) < ratio := by exact_mod_cast hratio
  obtain ⟨hq, hi⟩ := ratioIntegerBound_comparisons ratio
  have hqR : (ratio : ℝ) ≤ (2 : ℝ) ^ ratioIntegerBound ratio := by exact_mod_cast hq
  have hiR : 1 / (ratio : ℝ) ≤ (2 : ℝ) ^ ratioIntegerBound ratio := by
    have h := (Rat.cast_le (K := ℝ)).mpr hi
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using h
  have hupper := log_le_integer_of_le_two_pow (ratio : ℝ) hr _ hqR
  have hlower := log_le_integer_of_le_two_pow (1 / (ratio : ℝ)) (one_div_pos.mpr hr) _ hiR
  rw [Real.log_div (by norm_num : (1 : ℝ) ≠ 0) (ne_of_gt hr), Real.log_one, zero_sub] at hlower
  exact abs_le.mpr ⟨by linarith, hupper⟩

def channelIntegerMax (E : BinaryExperiment) : ℕ :=
  Finset.univ.sup (fun y : Fin E.alphabetSize => ratioIntegerBound (E.channel true y / E.channel false y))

def priorIntegerMax (E : BinaryExperiment) : ℕ :=
  ratioIntegerBound (E.prior true / E.prior false)

theorem channelIncrementMax_le_integer (E : BinaryExperiment) : E.channelIncrementMax ≤ E.channelIntegerMax := by
  unfold channelIncrementMax
  apply Finset.sup'_le
  intro y _hy
  have h := abs_log_le_ratioIntegerBound (E.channel true y / E.channel false y)
    (div_pos (E.channel_pos true y) (E.channel_pos false y))
  have hNat : ratioIntegerBound (E.channel true y / E.channel false y) ≤ E.channelIntegerMax :=
    Finset.le_sup (f := fun z : Fin E.alphabetSize => ratioIntegerBound (E.channel true z / E.channel false z))
      (Finset.mem_univ y)
  have h' : |E.channelLogIncrement true y| ≤ ratioIntegerBound (E.channel true y / E.channel false y) := by
    simpa only [channelLogIncrement, Bool.not_true, channelReal, Rat.cast_div] using h
  exact h'.trans (by exact_mod_cast hNat)

theorem priorLogOddsMax_le_integer (E : BinaryExperiment) : E.priorLogOddsMax ≤ E.priorIntegerMax := by
  have h := abs_log_le_ratioIntegerBound (E.prior true / E.prior false)
    (div_pos (E.prior_pos' true) (E.prior_pos' false))
  simpa only [priorLogOddsMax, priorIntegerMax, priorReal, Rat.cast_div] using h

/-- Exactly the original rational Qhat formula, given its verified integer E_delta. -/
def rationalQuota (E : BinaryExperiment) (exponent : ℕ) : ℕ :=
  ⌈max (2 * ((exponent : ℚ) + E.priorIntegerMax) / E.channelDriftLower)
    (8 * (E.channelIntegerMax : ℚ) ^ 2 * exponent / E.channelDriftLower ^ 2)⌉₊

theorem rationalQuota_drift_lower (E : BinaryExperiment) (exponent : ℕ) :
    2 * ((exponent : ℝ) + E.priorIntegerMax) / (E.channelDriftLower : ℝ) ≤ (E.rationalQuota exponent : ℝ) := by
  have h : (2 * ((exponent : ℚ) + E.priorIntegerMax) / E.channelDriftLower) ≤ (E.rationalQuota exponent : ℚ) :=
    (le_max_left _ _).trans (Nat.le_ceil _)
  have hR := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_add, Rat.cast_natCast, Rat.cast_ofNat] using hR

theorem rationalQuota_tail_lower (E : BinaryExperiment) (exponent : ℕ) :
    8 * (E.channelIntegerMax : ℝ) ^ 2 * exponent / (E.channelDriftLower : ℝ) ^ 2 ≤ (E.rationalQuota exponent : ℝ) := by
  have h : (8 * (E.channelIntegerMax : ℚ) ^ 2 * exponent / E.channelDriftLower ^ 2) ≤ (E.rationalQuota exponent : ℚ) :=
    (le_max_right _ _).trans (Nat.le_ceil _)
  have hR := (Rat.cast_le (K := ℝ)).mpr h
  simpa only [Rat.cast_div, Rat.cast_mul, Rat.cast_pow, Rat.cast_natCast, Rat.cast_ofNat] using hR

theorem dyadicQuota_log_bounds (delta : ℝ) (hdelta : 0 < delta) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hqualifies : DyadicQualifies (2 * N * referenceQuotaConstant N) delta exponent) :
    Real.log ((referenceQuotaConstant N : ℝ) / delta) ≤ exponent ∧
      Real.log ((2 * N : ℝ) / delta) ≤ exponent := by
  have hNreal : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from hN)
  have hC := referenceQuotaConstant_real_pos N
  have hCsix := referenceQuotaConstant_real_ge_six N
  have hqual : (2 * N : ℝ) * (referenceQuotaConstant N : ℝ) ≤ (2 : ℝ) ^ exponent * delta := by
    simpa only [DyadicQualifies, Rat.cast_mul, Rat.cast_natCast, Rat.cast_ofNat] using hqualifies
  have hratio : ((2 * N : ℝ) * (referenceQuotaConstant N : ℝ)) / delta ≤ (2 : ℝ) ^ exponent :=
    (div_le_iff₀ hdelta).mpr hqual
  constructor
  · apply log_le_integer_of_le_two_pow _ (div_pos hC hdelta)
    exact (div_le_div_of_nonneg_right (by nlinarith : (referenceQuotaConstant N : ℝ) ≤ (2 * N : ℝ) *
      (referenceQuotaConstant N : ℝ)) hdelta.le).trans hratio
  · apply log_le_integer_of_le_two_pow _ (div_pos (by positivity : (0 : ℝ) < 2 * N) hdelta)
    exact (div_le_div_of_nonneg_right (by nlinarith : (2 * N : ℝ) ≤ (2 * N : ℝ) *
      (referenceQuotaConstant N : ℝ)) hdelta.le).trans hratio

theorem rationalQuota_dominates_analytic (E : BinaryExperiment) (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hqualifies : DyadicQualifies (2 * N * referenceQuotaConstant N) delta exponent) :
    E.analyticQuota delta N ≤ E.rationalQuota exponent := by
  have hdLower : (0 : ℝ) < (E.channelDriftLower : ℝ) := by exact_mod_cast E.channelDriftLower_pos
  have hd := E.channelMinDivergence_pos
  have hdle := E.channelDriftLower_le_minDivergence
  have hM := E.channelIncrementMax_le_integer
  have hL := E.priorLogOddsMax_le_integer
  have hlogs := dyadicQuota_log_bounds delta hdelta N hN exponent hqualifies
  have hMnonneg := E.channelIncrementMax_nonneg
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hlogtail : 0 ≤ Real.log ((2 * N : ℝ) / delta) := by
    apply Real.log_nonneg
    apply (le_div_iff₀ hdelta).mpr
    have hNR : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N from hN)
    linarith
  have hMsq : E.channelIncrementMax ^ 2 ≤ (E.channelIntegerMax : ℝ) ^ 2 := by nlinarith
  have hDsq : (E.channelDriftLower : ℝ) ^ 2 ≤ E.channelMinDivergence ^ 2 := by nlinarith
  apply Nat.ceil_le.mpr
  apply max_le
  · calc
      _ ≤ 2 * ((exponent : ℝ) + E.priorIntegerMax) / E.channelMinDivergence :=
        div_le_div_of_nonneg_right (by linarith [hlogs.1]) hd.le
      _ ≤ 2 * ((exponent : ℝ) + E.priorIntegerMax) / (E.channelDriftLower : ℝ) :=
        div_le_div_of_nonneg_left (by positivity) hdLower hdle
      _ ≤ _ := E.rationalQuota_drift_lower exponent
  · have hnum : 8 * E.channelIncrementMax ^ 2 * Real.log ((2 * N : ℝ) / delta) ≤
        8 * (E.channelIntegerMax : ℝ) ^ 2 * exponent := by
      have h1 := mul_le_mul_of_nonneg_right hMsq hlogtail
      have h2 := mul_le_mul_of_nonneg_left hlogs.2 (sq_nonneg (E.channelIntegerMax : ℝ))
      nlinarith
    calc
      _ = (8 * E.channelIncrementMax ^ 2 * Real.log ((2 * N : ℝ) / delta)) / E.channelMinDivergence ^ 2 := by ring
      _ ≤ (8 * (E.channelIntegerMax : ℝ) ^ 2 * exponent) / E.channelMinDivergence ^ 2 :=
        div_le_div_of_nonneg_right hnum (sq_nonneg _)
      _ ≤ (8 * (E.channelIntegerMax : ℝ) ^ 2 * exponent) / (E.channelDriftLower : ℝ) ^ 2 :=
        div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hdLower) hDsq
      _ ≤ _ := E.rationalQuota_tail_lower exponent

/-- The paper's exact minimum over e≥1, computed by rational ceilings,
integer comparisons, and natural-number ceil-log. -/
def quotaExponent (risk : ℚ) (N : ℕ) : ℕ :=
  max 1 (Nat.clog 2 ⌈(2 * N * referenceQuotaConstant N) / risk⌉₊)

theorem quotaExponent_le_iff (risk : ℚ) (hrisk : 0 < risk) (N exponent : ℕ) :
    quotaExponent risk N ≤ exponent ↔
      1 ≤ exponent ∧ DyadicQualifies (2 * N * referenceQuotaConstant N) (risk : ℝ) exponent := by
  rw [quotaExponent, max_le_iff, Nat.clog_le_iff_le_pow (by norm_num), Nat.ceil_le]
  rw [div_le_iff₀ hrisk]
  constructor
  · rintro ⟨hone, h⟩
    refine ⟨hone, ?_⟩
    change ((2 * N * referenceQuotaConstant N : ℚ) : ℝ) ≤ (2 : ℝ) ^ exponent * (risk : ℝ)
    exact_mod_cast h
  · rintro ⟨hone, h⟩
    refine ⟨hone, ?_⟩
    change ((2 * N * referenceQuotaConstant N : ℚ) : ℝ) ≤ (2 : ℝ) ^ exponent * (risk : ℝ) at h
    exact_mod_cast h

theorem quotaExponent_minimal (risk : ℚ) (hrisk : 0 < risk) (N : ℕ) :
    IsMinimalDyadicExponent (2 * N * referenceQuotaConstant N) (risk : ℝ) (quotaExponent risk N) := by
  have h := (quotaExponent_le_iff risk hrisk N (quotaExponent risk N)).mp le_rfl
  refine ⟨h.1, h.2, ?_⟩
  intro smaller hpos hsmall hqual
  have hle := (quotaExponent_le_iff risk hrisk N smaller).mpr ⟨hpos, hqual⟩
  exact (not_le_of_gt hsmall) hle

theorem minimalDyadicExponent_unique (C : ℚ) (risk : ℝ) (left right : ℕ)
    (hleft : IsMinimalDyadicExponent C risk left) (hright : IsMinimalDyadicExponent C risk right) : left = right := by
  apply le_antisymm
  · by_contra h
    exact hleft.2.2 right hright.1 (Nat.lt_of_not_ge h) hright.2.1
  · by_contra h
    exact hright.2.2 left hleft.1 (Nat.lt_of_not_ge h) hleft.2.1

theorem quotaExponent_eq_original (risk : ℚ) (hrisk : 0 < risk) (N exponent : ℕ)
    (hminimal : IsMinimalDyadicExponent (2 * N * referenceQuotaConstant N) (risk : ℝ) exponent) :
    quotaExponent risk N = exponent :=
  minimalDyadicExponent_unique _ _ _ _ (quotaExponent_minimal risk hrisk N) hminimal

theorem rationalQuota_overflow_le (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hpquarter : p ≤ 1 / 4)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hqualifies : DyadicQualifies (2 * N * referenceQuotaConstant N) delta exponent)
    (hfloor : delta / (referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) (x : Bool) :
    E.tapeLaw x {tape | (E.rationalQuota exponent : ℕ∞) < E.posteriorThresholdStop p tape} ≤
      ENNReal.ofReal (delta / (2 * N)) := by
  have hquota := E.rationalQuota_dominates_analytic delta hdelta hsmall N hN exponent hqualifies
  apply (measure_mono (show {tape | (E.rationalQuota exponent : ℕ∞) < E.posteriorThresholdStop p tape} ⊆
      {tape | (E.analyticQuota delta N : ℕ∞) < E.posteriorThresholdStop p tape} from ?_)).trans
    (E.posteriorSPRT_overflow_le p hp hpquarter delta hdelta hsmall N hN hfloor x)
  intro tape htape
  have hquotaENat : (E.analyticQuota delta N : ℕ∞) ≤ (E.rationalQuota exponent : ℕ∞) := by exact_mod_cast hquota
  exact lt_of_le_of_lt hquotaENat htape

theorem rationalQuota_conditional_overflow_le (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hpquarter : p ≤ 1 / 4)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hqualifies : DyadicQualifies (2 * N * referenceQuotaConstant N) delta exponent)
    (hfloor : delta / (referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) (x : Bool) :
    E.conditionalLaw (Measure.dirac ()) x {sample |
      (E.rationalQuota exponent : ℕ∞) < (E.posteriorSPRT p).rule.stop sample.1 sample.2} ≤
      ENNReal.ofReal (delta / (2 * N)) := by
  have hquota := E.rationalQuota_dominates_analytic delta hdelta hsmall N hN exponent hqualifies
  apply (measure_mono (show {sample : Unit × E.Tape |
        (E.rationalQuota exponent : ℕ∞) < (E.posteriorSPRT p).rule.stop sample.1 sample.2} ⊆
      {sample | (E.analyticQuota delta N : ℕ∞) < (E.posteriorSPRT p).rule.stop sample.1 sample.2} from ?_)).trans
    (E.posteriorSPRT_conditional_overflow_le p hp hpquarter delta hdelta hsmall N hN hfloor x)
  intro sample hsample
  have hquotaENat : (E.analyticQuota delta N : ℕ∞) ≤ (E.rationalQuota exponent : ℕ∞) := by exact_mod_cast hquota
  exact lt_of_le_of_lt hquotaENat hsample

/-- Choose the conservative rational reference risk in the same original
dyadic bin. Its true target floor is R/C_N. Apply overflow with delta=R,
then R≤delta; the quota remains Qhat(E_delta) without any cap enlargement. -/
theorem exists_referenceRisk_originalQuota_overflow (E : BinaryExperiment) (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N) (exponent : ℕ)
    (hminimal : IsMinimalDyadicExponent (2 * N * referenceQuotaConstant N) delta exponent) :
    ∃ referenceRisk : ℚ, 0 < referenceRisk ∧ referenceRisk ≤ 1 / 2 ∧
      delta / 2 ≤ (referenceRisk : ℝ) ∧ (referenceRisk : ℝ) ≤ delta ∧
      quotaExponent referenceRisk N = exponent ∧
      ∀ (events : List ReferenceBudgetEvent) (_hlen : events.length ≤ N) (current target : ℚ),
        referenceBudgetPath (referenceRisk / 2) events = some current →
        ∀ kind : ReferenceBudgetCase, referenceBudgetTarget kind current = some target → ∀ x : Bool,
          E.conditionalLaw (Measure.dirac ()) x {sample |
            (E.rationalQuota exponent : ℕ∞) < (E.posteriorSPRT target).rule.stop sample.1 sample.2} ≤
              ENNReal.ofReal (delta / (2 * N)) := by
  obtain ⟨risk, hrisk, hriskSmall, hhalf, hriskDelta, hsame, _hpathTargets⟩ :=
    exists_referenceRisk_same_exponent_targets delta hdelta hsmall N hN exponent hminimal
  refine ⟨risk, hrisk, hriskSmall, hhalf, hriskDelta, quotaExponent_eq_original risk hrisk N exponent hsame, ?_⟩
  intro events hlen current target hpath kind htarget x
  have hinit : ReferenceBudgetValid (risk / 2) := ⟨by linarith, by linarith⟩
  have hcurrent := (referenceBudgetPath_valid_floor events (risk / 2) current hinit hpath).1
  have ht := referenceBudgetTarget_valid_floor kind current target hcurrent htarget
  have hf := referenceBudgetPath_original_target_floor_real risk hrisk hriskSmall events N hlen current target hpath kind htarget
  have hf' : (risk : ℝ) / (referenceQuotaConstant N : ℝ) ≤ (target : ℝ) := by
    simpa only [referenceQuotaConstant, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat] using hf
  have hriskR : (0 : ℝ) < risk := by exact_mod_cast hrisk
  have hriskSmallR : (risk : ℝ) ≤ 1 / 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr hriskSmall
    norm_num at h
    exact h
  have hoverflow := E.rationalQuota_conditional_overflow_le target ht.1 ht.2.1 (risk : ℝ) hriskR hriskSmallR N hN exponent
    hsame.2.1 hf' x
  exact hoverflow.trans (ENNReal.ofReal_le_ofReal (div_le_div_of_nonneg_right hriskDelta (by positivity)))

end PaperProofs.Statistics.BinaryExperiment
