module

public import PaperProofs.Statistics.PosteriorSPRT
public import PaperProofs.Statistics.ReferenceBudgets
public import Mathlib.Probability.Moments.SubGaussian

/-!
Single-stage overflow for the exact analytic quota in frozen
price-proofs.tex:231--258. The constants 2 and 8 and the finite-channel
maximum M are unchanged. Native history extraction and the later rational
Pinsker certificate are separate obligations. The single-stage bounds below
use the real iid channel law and the actual first-exit stopping function.
-/

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory ProbabilityTheory

namespace PaperProofs.Statistics.BinaryExperiment

noncomputable def channelLogIncrement (E : BinaryExperiment) (x : Bool) (y : Fin E.alphabetSize) : ℝ :=
  Real.log (E.channelReal x y / E.channelReal (!x) y)

noncomputable def channelMinDivergence (E : BinaryExperiment) : ℝ :=
  min (E.divergence false) (E.divergence true)

noncomputable def channelIncrementMax (E : BinaryExperiment) : ℝ :=
  Finset.univ.sup' (by exact ⟨E.completionSymbol, Finset.mem_univ _⟩)
    (fun y : Fin E.alphabetSize => |E.channelLogIncrement true y|)

noncomputable def priorLogOddsMax (E : BinaryExperiment) : ℝ :=
  |Real.log (E.priorReal true / E.priorReal false)|

noncomputable def analyticQuota (E : BinaryExperiment) (delta : ℝ) (N : ℕ) : ℕ :=
  ⌈max (2 * (Real.log ((referenceQuotaConstant N : ℝ) / delta) + E.priorLogOddsMax) /
      E.channelMinDivergence)
    ((8 * E.channelIncrementMax ^ 2 / E.channelMinDivergence ^ 2) * Real.log ((2 * N : ℝ) / delta))⌉₊

theorem channelMinDivergence_pos (E : BinaryExperiment) : 0 < E.channelMinDivergence :=
  lt_min (E.divergence_pos false) (E.divergence_pos true)

theorem channelMinDivergence_le (E : BinaryExperiment) (x : Bool) : E.channelMinDivergence ≤ E.divergence x := by
  cases x
  · exact min_le_left _ _
  · exact min_le_right _ _

theorem channelLogIncrement_false (E : BinaryExperiment) (y : Fin E.alphabetSize) :
    E.channelLogIncrement false y = -E.channelLogIncrement true y := by
  simp only [channelLogIncrement, Bool.not_false, Bool.not_true,
    Real.log_div (ne_of_gt (E.channelReal_pos false y)) (ne_of_gt (E.channelReal_pos true y)),
    Real.log_div (ne_of_gt (E.channelReal_pos true y)) (ne_of_gt (E.channelReal_pos false y))]
  ring

theorem channelLogIncrement_abs_le (E : BinaryExperiment) (x : Bool) (y : Fin E.alphabetSize) :
    |E.channelLogIncrement x y| ≤ E.channelIncrementMax := by
  have h : |E.channelLogIncrement true y| ≤ E.channelIncrementMax :=
    Finset.le_sup' (fun z : Fin E.alphabetSize => |E.channelLogIncrement true z|) (Finset.mem_univ y)
  cases x with
  | true => exact h
  | false => simpa only [E.channelLogIncrement_false, abs_neg] using h

theorem channelIncrementMax_nonneg (E : BinaryExperiment) : 0 ≤ E.channelIncrementMax :=
  (abs_nonneg (E.channelLogIncrement true E.completionSymbol)).trans (E.channelLogIncrement_abs_le true _)

theorem divergence_le_channelIncrementMax (E : BinaryExperiment) (x : Bool) :
    E.divergence x ≤ E.channelIncrementMax := by
  calc
    _ ≤ ∑ y : Fin E.alphabetSize, E.channelReal x y * E.channelIncrementMax := by
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (E.channelLogIncrement_abs_le x y))
        (E.channelReal_pos x y).le
    _ = _ := by rw [← Finset.sum_mul, E.channelReal_sum, one_mul]

theorem channelIncrementMax_pos (E : BinaryExperiment) : 0 < E.channelIncrementMax :=
  (E.divergence_pos true).trans_le (E.divergence_le_channelIncrementMax true)

noncomputable def tapeLogIncrement (E : BinaryExperiment) (x : Bool) (n : ℕ) (tape : E.Tape) : ℝ :=
  E.channelLogIncrement x (tape n)

noncomputable def centeredNegativeIncrement (E : BinaryExperiment) (x : Bool) (n : ℕ) (tape : E.Tape) : ℝ :=
  E.divergence x - E.tapeLogIncrement x n tape

theorem measurable_tapeLogIncrement (E : BinaryExperiment) (x : Bool) (n : ℕ) :
    Measurable (E.tapeLogIncrement x n) :=
  (measurable_of_countable (E.channelLogIncrement x)).comp (measurable_pi_apply n)

theorem integrable_tapeLogIncrement (E : BinaryExperiment) (x : Bool) (n : ℕ) :
    Integrable (E.tapeLogIncrement x n) (E.tapeLaw x) := by
  apply (integrable_const E.channelIncrementMax).mono' (E.measurable_tapeLogIncrement x n).aestronglyMeasurable
  exact ae_of_all _ (fun tape => E.channelLogIncrement_abs_le x (tape n))

theorem integral_tapeLogIncrement (E : BinaryExperiment) (x : Bool) (n : ℕ) :
    ∫ tape, E.tapeLogIncrement x n tape ∂(E.tapeLaw x) = E.divergence x := by
  have hm : Measurable (E.channelLogIncrement x) := measurable_of_countable _
  have hmap := integral_map (measurable_pi_apply n).aemeasurable hm.aestronglyMeasurable (μ := E.tapeLaw x)
  rw [E.tapeLaw_coordinate] at hmap
  unfold tapeLogIncrement
  rw [← hmap]
  simpa only [channelLogIncrement, E.channelLaw_llr] using E.channelLaw_integral_llr x

theorem measurable_centeredNegativeIncrement (E : BinaryExperiment) (x : Bool) (n : ℕ) :
    Measurable (E.centeredNegativeIncrement x n) :=
  measurable_const.sub (E.measurable_tapeLogIncrement x n)

theorem integral_centeredNegativeIncrement (E : BinaryExperiment) (x : Bool) (n : ℕ) :
    ∫ tape, E.centeredNegativeIncrement x n tape ∂(E.tapeLaw x) = 0 := by
  unfold centeredNegativeIncrement
  rw [integral_sub (integrable_const _) (E.integrable_tapeLogIncrement x n), E.integral_tapeLogIncrement]
  simp

theorem centeredNegativeIncrement_mem_Icc (E : BinaryExperiment) (x : Bool) (n : ℕ) (tape : E.Tape) :
    E.centeredNegativeIncrement x n tape ∈ Set.Icc (E.divergence x - E.channelIncrementMax)
      (E.divergence x + E.channelIncrementMax) := by
  have h := abs_le.mp (E.channelLogIncrement_abs_le x (tape n))
  change E.divergence x - E.channelLogIncrement x (tape n) ∈ _
  exact ⟨by linarith [h.2], by linarith [h.1]⟩

noncomputable def channelSubgaussianParameter (E : BinaryExperiment) : NNReal :=
  ⟨E.channelIncrementMax ^ 2, sq_nonneg _⟩

theorem centeredNegativeIncrement_subgaussian (E : BinaryExperiment) (x : Bool) (n : ℕ) :
    HasSubgaussianMGF (E.centeredNegativeIncrement x n) E.channelSubgaussianParameter (E.tapeLaw x) := by
  have h := hasSubgaussianMGF_of_mem_Icc_of_integral_eq_zero
    (E.measurable_centeredNegativeIncrement x n).aemeasurable
    (ae_of_all _ (E.centeredNegativeIncrement_mem_Icc x n)) (E.integral_centeredNegativeIncrement x n)
  have heq : ((‖(E.divergence x + E.channelIncrementMax) - (E.divergence x - E.channelIncrementMax)‖₊ / 2) ^ 2) =
      E.channelSubgaussianParameter := by
    apply Subtype.ext
    change ((‖(E.divergence x + E.channelIncrementMax) - (E.divergence x - E.channelIncrementMax)‖ : ℝ) / 2) ^ 2 =
      E.channelIncrementMax ^ 2
    rw [Real.norm_of_nonneg (by have hM := E.channelIncrementMax_nonneg; linarith)]
    ring
  rw [heq] at h
  exact h

theorem centeredNegativeIncrement_independent (E : BinaryExperiment) (x : Bool) :
    iIndepFun (E.centeredNegativeIncrement x) (E.tapeLaw x) := by
  have h := (E.tapeLaw_independent x).comp
    (fun _n : ℕ => fun y : Fin E.alphabetSize => E.divergence x - E.channelLogIncrement x y)
    (fun _n => measurable_of_countable _)
  exact h

theorem centeredNegativeIncrement_hoeffding (E : BinaryExperiment) (x : Bool) (n : ℕ) (epsilon : ℝ)
    (hepsilon : 0 ≤ epsilon) :
    (E.tapeLaw x).real {tape | epsilon ≤ ∑ k ∈ Finset.range n, E.centeredNegativeIncrement x k tape} ≤
      Real.exp (-epsilon ^ 2 / (2 * n * E.channelIncrementMax ^ 2)) := by
  have h := HasSubgaussianMGF.measure_sum_range_ge_le_of_iIndepFun
    (n := n) (E.centeredNegativeIncrement_independent x) (fun k _hk => E.centeredNegativeIncrement_subgaussian x k) hepsilon
  exact h

theorem referenceQuotaConstant_real_pos (N : ℕ) : (0 : ℝ) < (referenceQuotaConstant N : ℝ) := by
  simp only [referenceQuotaConstant, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  positivity

theorem referenceQuotaConstant_real_ge_six (N : ℕ) : (6 : ℝ) ≤ (referenceQuotaConstant N : ℝ) := by
  simp only [referenceQuotaConstant, Rat.cast_mul, Rat.cast_pow, Rat.cast_ofNat]
  have h : (1 : ℝ) ≤ (2 : ℝ) ^ (N + 1) := one_le_pow₀ (by norm_num)
  linarith

theorem quotaLog_pos (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 2) (N : ℕ) :
    0 < Real.log ((referenceQuotaConstant N : ℝ) / delta) := by
  apply Real.log_pos
  apply (lt_div_iff₀ hdelta).mpr
  have h := referenceQuotaConstant_real_ge_six N
  linarith

theorem analyticQuota_drift_lower (E : BinaryExperiment) (delta : ℝ) (N : ℕ) :
    2 * (Real.log ((referenceQuotaConstant N : ℝ) / delta) + E.priorLogOddsMax) /
      E.channelMinDivergence ≤ (E.analyticQuota delta N : ℝ) :=
  (le_max_left _ _).trans (Nat.le_ceil _)

theorem analyticQuota_tail_lower (E : BinaryExperiment) (delta : ℝ) (N : ℕ) :
    (8 * E.channelIncrementMax ^ 2 / E.channelMinDivergence ^ 2) * Real.log ((2 * N : ℝ) / delta) ≤
      (E.analyticQuota delta N : ℝ) :=
  (le_max_right _ _).trans (Nat.le_ceil _)

theorem analyticQuota_pos (E : BinaryExperiment) (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta ≤ 1 / 2) (N : ℕ) : 0 < E.analyticQuota delta N := by
  have hlog := quotaLog_pos delta hdelta hsmall N
  have hprior : 0 ≤ E.priorLogOddsMax := abs_nonneg _
  have hpos : 0 < 2 * (Real.log ((referenceQuotaConstant N : ℝ) / delta) + E.priorLogOddsMax) /
      E.channelMinDivergence := div_pos (by linarith) E.channelMinDivergence_pos
  exact_mod_cast hpos.trans_le (E.analyticQuota_drift_lower delta N)

theorem analyticQuota_drift_bound (E : BinaryExperiment) (delta : ℝ) (N : ℕ) :
    Real.log ((referenceQuotaConstant N : ℝ) / delta) + E.priorLogOddsMax ≤
      E.channelMinDivergence * (E.analyticQuota delta N : ℝ) / 2 := by
  have h := (div_le_iff₀ E.channelMinDivergence_pos).mp (E.analyticQuota_drift_lower delta N)
  nlinarith

theorem analyticQuota_exponent_bound (E : BinaryExperiment) (delta : ℝ) (N : ℕ) :
    Real.log ((2 * N : ℝ) / delta) ≤
      E.channelMinDivergence ^ 2 * (E.analyticQuota delta N : ℝ) / (8 * E.channelIncrementMax ^ 2) := by
  have hM := E.channelIncrementMax_pos
  have hquota : (8 * E.channelIncrementMax ^ 2 * Real.log ((2 * N : ℝ) / delta)) /
      E.channelMinDivergence ^ 2 ≤ (E.analyticQuota delta N : ℝ) := by
    calc
      _ = (8 * E.channelIncrementMax ^ 2 / E.channelMinDivergence ^ 2) * Real.log ((2 * N : ℝ) / delta) := by ring
      _ ≤ _ := E.analyticQuota_tail_lower delta N
  have hc := (div_le_iff₀ (sq_pos_of_pos E.channelMinDivergence_pos)).mp hquota
  apply (le_div_iff₀ (by positivity : (0 : ℝ) < 8 * E.channelIncrementMax ^ 2)).mpr
  nlinarith

theorem posteriorThreshold_le_quotaLog (p : ℚ) (hp : 0 < p)
    (hplt : p < 1) (delta : ℝ) (hdelta : 0 < delta) (N : ℕ)
    (hfloor : delta / (referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) :
    Real.log ((1 - (p : ℝ)) / (p : ℝ)) ≤ Real.log ((referenceQuotaConstant N : ℝ) / delta) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hmul := (div_le_iff₀ (referenceQuotaConstant_real_pos N)).mp hfloor
  have hinverse : 1 / (p : ℝ) ≤ (referenceQuotaConstant N : ℝ) / delta :=
    (div_le_div_iff₀ hpR hdelta).mpr (by simpa only [one_mul, mul_one, mul_comm] using hmul)
  exact (posteriorThreshold_le_log_inv p hp hplt).trans (Real.log_le_log (one_div_pos.mpr hpR) hinverse)

theorem posteriorSPRT_overflow_direction_sum_lt (E : BinaryExperiment) (p : ℚ) (hp : 0 < p)
    (hplt : p < 1) (delta : ℝ) (hdelta : 0 < delta) (N n : ℕ)
    (hfloor : delta / (referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) (x : Bool) (tape : E.Tape)
    (hoverflow : (n : ℕ∞) < E.posteriorThresholdStop p tape) :
    (∑ k ∈ Finset.range n, E.tapeLogIncrement x k tape) <
      Real.log ((referenceQuotaConstant N : ℝ) / delta) + E.priorLogOddsMax := by
  have hscore := E.logOddsScore_before_stop p tape n hoverflow
  have hthreshold := posteriorThreshold_le_quotaLog p hp hplt delta hdelta N hfloor
  have hnorm := E.prefixLogSum_norm_le_score ((), tape) x n
  change ‖∑ k ∈ Finset.range n, E.tapeLogIncrement x k tape‖ ≤ |E.logOddsScore tape n| + E.priorLogOddsMax at hnorm
  rw [Real.norm_eq_abs] at hnorm
  exact lt_of_le_of_lt ((le_abs_self _).trans hnorm) (by linarith)

theorem posteriorSPRT_overflow_subset_deviation (E : BinaryExperiment) (p : ℚ) (hp : 0 < p)
    (hplt : p < 1) (delta : ℝ) (hdelta : 0 < delta) (N : ℕ)
    (hfloor : delta / (referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) (x : Bool) :
    {tape | (E.analyticQuota delta N : ℕ∞) < E.posteriorThresholdStop p tape} ⊆
      {tape | E.channelMinDivergence * (E.analyticQuota delta N : ℝ) / 2 ≤
        ∑ k ∈ Finset.range (E.analyticQuota delta N), E.centeredNegativeIncrement x k tape} := by
  intro tape hoverflow
  have hsum := E.posteriorSPRT_overflow_direction_sum_lt p hp hplt delta hdelta N _ hfloor x tape hoverflow
  have hquota := E.analyticQuota_drift_bound delta N
  have hmean := mul_le_mul_of_nonneg_left (E.channelMinDivergence_le x)
    (Nat.cast_nonneg (E.analyticQuota delta N) : (0 : ℝ) ≤ (E.analyticQuota delta N : ℝ))
  have heq : (∑ k ∈ Finset.range (E.analyticQuota delta N), E.centeredNegativeIncrement x k tape) =
      (E.analyticQuota delta N : ℝ) * E.divergence x -
        ∑ k ∈ Finset.range (E.analyticQuota delta N), E.tapeLogIncrement x k tape := by
    simp only [centeredNegativeIncrement, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_range, nsmul_eq_mul]
  change _ ≤ ∑ k ∈ Finset.range (E.analyticQuota delta N), E.centeredNegativeIncrement x k tape
  rw [heq]
  nlinarith

theorem analyticQuota_eq_intCeil (E : BinaryExperiment) (delta : ℝ) (hdelta : 0 < delta)
    (hsmall : delta ≤ 1 / 2) (N : ℕ) :
    (E.analyticQuota delta N : ℤ) = ⌈max
      (2 * (Real.log ((referenceQuotaConstant N : ℝ) / delta) + E.priorLogOddsMax) / E.channelMinDivergence)
      ((8 * E.channelIncrementMax ^ 2 / E.channelMinDivergence ^ 2) * Real.log ((2 * N : ℝ) / delta))⌉ := by
  apply Int.natCast_ceil_eq_ceil
  have hlog := quotaLog_pos delta hdelta hsmall N
  have hprior : 0 ≤ E.priorLogOddsMax := abs_nonneg _
  have hfirst : (0 : ℝ) ≤ 2 * (Real.log ((referenceQuotaConstant N : ℝ) / delta) + E.priorLogOddsMax) /
      E.channelMinDivergence := div_nonneg (by linarith) E.channelMinDivergence_pos.le
  exact hfirst.trans (le_max_left _ _)

/-- The original analytic quota gives the exact frozen overflow constant.
Both truth directions use their real iid channel law and the actual first-exit
SPRT stopping function. The quota has not been weakened to a Markov quota. -/
theorem posteriorSPRT_overflow_real_le (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hpquarter : p ≤ 1 / 4)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N)
    (hfloor : delta / (referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) (x : Bool) :
    (E.tapeLaw x).real {tape | (E.analyticQuota delta N : ℕ∞) < E.posteriorThresholdStop p tape} ≤
      delta / (2 * N) := by
  have hplt : p < 1 := by linarith
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hQreal : (0 : ℝ) < E.analyticQuota delta N := by exact_mod_cast E.analyticQuota_pos delta hdelta hsmall N
  have hM := E.channelIncrementMax_pos
  have hd := E.channelMinDivergence_pos
  have hsubset := E.posteriorSPRT_overflow_subset_deviation p hp hplt delta hdelta N hfloor x
  have hmeasure := measureReal_mono (μ := E.tapeLaw x) hsubset (measure_ne_top _ _)
  have hhoeffding := E.centeredNegativeIncrement_hoeffding x (E.analyticQuota delta N)
    (E.channelMinDivergence * (E.analyticQuota delta N : ℝ) / 2) (by positivity)
  have hexponent : -(E.channelMinDivergence * (E.analyticQuota delta N : ℝ) / 2) ^ 2 /
        (2 * (E.analyticQuota delta N : ℝ) * E.channelIncrementMax ^ 2) =
      -(E.channelMinDivergence ^ 2 * (E.analyticQuota delta N : ℝ) / (8 * E.channelIncrementMax ^ 2)) := by
    field_simp [ne_of_gt hM, ne_of_gt hQreal]
    ring
  rw [hexponent] at hhoeffding
  have hexpBound := E.analyticQuota_exponent_bound delta N
  calc
    _ ≤ Real.exp (-(E.channelMinDivergence ^ 2 * (E.analyticQuota delta N : ℝ) / (8 * E.channelIncrementMax ^ 2))) :=
      hmeasure.trans hhoeffding
    _ ≤ Real.exp (-Real.log ((2 * N : ℝ) / delta)) := Real.exp_le_exp.mpr (neg_le_neg hexpBound)
    _ = delta / (2 * N) := by
      rw [Real.exp_neg, Real.exp_log (div_pos (by positivity : (0 : ℝ) < 2 * N) hdelta)]
      exact inv_div _ _

theorem posteriorSPRT_overflow_le (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hpquarter : p ≤ 1 / 4)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N)
    (hfloor : delta / (referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) (x : Bool) :
    E.tapeLaw x {tape | (E.analyticQuota delta N : ℕ∞) < E.posteriorThresholdStop p tape} ≤
      ENNReal.ofReal (delta / (2 * N)) := by
  have h := ENNReal.ofReal_le_ofReal (E.posteriorSPRT_overflow_real_le p hp hpquarter delta hdelta hsmall N hN hfloor x)
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

theorem posteriorSPRT_conditional_overflow_le (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hpquarter : p ≤ 1 / 4)
    (delta : ℝ) (hdelta : 0 < delta) (hsmall : delta ≤ 1 / 2) (N : ℕ) (hN : 0 < N)
    (hfloor : delta / (referenceQuotaConstant N : ℝ) ≤ (p : ℝ)) (x : Bool) :
    E.conditionalLaw (Measure.dirac ()) x {sample |
      (E.analyticQuota delta N : ℕ∞) < (E.posteriorSPRT p).rule.stop sample.1 sample.2} ≤
      ENNReal.ofReal (delta / (2 * N)) := by
  change (Measure.dirac ()).prod (E.tapeLaw x) {sample : Unit × E.Tape |
    (E.analyticQuota delta N : ℕ∞) < E.posteriorThresholdStop p sample.2} ≤ _
  have heq : {sample : Unit × E.Tape | (E.analyticQuota delta N : ℕ∞) < E.posteriorThresholdStop p sample.2} =
      Set.univ ×ˢ {tape | (E.analyticQuota delta N : ℕ∞) < E.posteriorThresholdStop p tape} := by
    ext sample
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
  rw [heq, Measure.prod_prod, measure_univ, one_mul]
  exact E.posteriorSPRT_overflow_le p hp hpquarter delta hdelta hsmall N hN hfloor x

end PaperProofs.Statistics.BinaryExperiment
