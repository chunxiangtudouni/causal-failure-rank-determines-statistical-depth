module

public import PaperProofs.Star.PDROC_StarOverflowTail_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Statistics PaperProofs.Statistics.BinarySymmetric PaperProofs.Star

namespace PDROC.StarOverflowTail

theorem realStop_score_before (E : BinaryExperiment) (r : ℝ) (tape : E.Tape) (n : ℕ)
    (hbefore : (n : ℕ∞) < realPosteriorStop E r tape) :
    |E.logOddsScore tape n| < Real.log ((1-r)/r) := by
  apply lt_of_not_ge
  intro hhit
  exact (not_le_of_gt hbefore) (sInf_le (show (n : ℕ∞) ∈
    {t : ℕ∞ | ∃ k : ℕ, t = k ∧ Real.log ((1-r)/r) ≤ |E.logOddsScore tape k|} from
      ⟨n, rfl, hhit⟩))

theorem realStop_commonQuota_subset (P : PaperProofs.Star.Parameters) (delta r : ℝ) (exponent : ℕ)
    (hd : 0 < delta) (hr : 0 < r) (hrhalf : r ≤ 1/2) (hfloor : delta/10 ≤ r)
    (hqual : DyadicQualifies (20*(P.tools+1 : ℕ)) delta exponent) (truth : Bool) :
    {tape | (P.commonQuota exponent : ℕ∞) < realPosteriorStop P.channel.experiment r tape} ⊆
    {tape | P.channel.kappa*(P.commonQuota exponent : ℝ)/2 ≤
      ∑ k ∈ Finset.range (P.commonQuota exponent),
        P.channel.experiment.centeredNegativeIncrement truth k tape} := by
  intro tape hbefore
  have hscore := realStop_score_before P.channel.experiment r tape (P.commonQuota exponent) hbefore
  have hthreshold := real_threshold_le_exponent P.tools delta r exponent hd hr hrhalf hfloor hqual
  have hnorm := P.channel.experiment.prefixLogSum_norm_le_score ((),tape) truth (P.commonQuota exponent)
  change ‖∑ k ∈ Finset.range (P.commonQuota exponent),
    P.channel.experiment.tapeLogIncrement truth k tape‖ ≤
      |P.channel.experiment.logOddsScore tape (P.commonQuota exponent)| +
        P.channel.experiment.priorLogOddsMax at hnorm
  rw [bsc_priorLogOddsMax_zero, add_zero, Real.norm_eq_abs] at hnorm
  have hsum : (∑ k ∈ Finset.range (P.commonQuota exponent),
      P.channel.experiment.tapeLogIncrement truth k tape) < exponent :=
    lt_of_le_of_lt ((le_abs_self _).trans hnorm) (hscore.trans_le hthreshold)
  have hg : (0 : ℝ) < P.channel.gamma := by exact_mod_cast P.channel.gamma_pos
  have hquota := commonQuota_drift_lower P exponent
  have hh := mul_le_mul_of_nonneg_right (bsc_h_ge_gamma P.channel)
    (mul_nonneg hg.le (Nat.cast_nonneg (P.commonQuota exponent)))
  have hmean : (exponent : ℝ) ≤ P.channel.kappa*(P.commonQuota exponent : ℝ)/2 := by
    unfold BinarySymmetric.Parameters.kappa
    nlinarith
  have heq : (∑ k ∈ Finset.range (P.commonQuota exponent),
      P.channel.experiment.centeredNegativeIncrement truth k tape) =
        (P.commonQuota exponent : ℝ)*P.channel.kappa -
          ∑ k ∈ Finset.range (P.commonQuota exponent), P.channel.experiment.tapeLogIncrement truth k tape := by
    simp only [BinaryExperiment.centeredNegativeIncrement, Finset.sum_sub_distrib,
      Finset.sum_const, Finset.card_range, nsmul_eq_mul, P.channel.divergence_eq_kappa]
  change _ ≤ ∑ k ∈ Finset.range (P.commonQuota exponent),
    P.channel.experiment.centeredNegativeIncrement truth k tape
  rw [heq]
  nlinarith

/-- Both actual truth directions; no finite stopping or expected-cost premise. -/
theorem realPosteriorStop_commonQuota_tail (P : PaperProofs.Star.Parameters)
    (delta r : ℝ) (exponent : ℕ) (hd : 0 < delta)
    (hminimal : IsMinimalDyadicExponent (20*(P.tools+1 : ℕ)) delta exponent)
    (hr : 0 < r) (hrhalf : r ≤ 1/2) (hfloor : delta/10 ≤ r) (truth : Bool) :
    P.channel.experiment.tapeLaw truth
      {tape | (P.commonQuota exponent : ℕ∞) < realPosteriorStop P.channel.experiment r tape} ≤
        ENNReal.ofReal (delta/(2*(P.tools+1 : ℕ))) := by
  have hquota := commonQuota_drift_lower P exponent
  have hQ : (0 : ℝ) < P.commonQuota exponent := by
    exact_mod_cast commonQuota_pos P exponent hminimal.1
  have hsubset := realStop_commonQuota_subset P delta r exponent hd hr hrhalf hfloor hminimal.2.1 truth
  have hm := measureReal_mono (μ := P.channel.experiment.tapeLaw truth) hsubset (measure_ne_top _ _)
  have hh := P.channel.experiment.centeredNegativeIncrement_hoeffding truth (P.commonQuota exponent)
    (P.channel.kappa*(P.commonQuota exponent : ℝ)/2)
    (div_nonneg (mul_nonneg P.channel.kappa_pos.le hQ.le) (by norm_num))
  rw [bsc_incrementMax_eq_h] at hh
  have heq : -(P.channel.kappa*(P.commonQuota exponent : ℝ)/2)^2 /
      (2*(P.commonQuota exponent : ℝ)*P.channel.h^2) =
        -((P.channel.gamma : ℝ)^2*(P.commonQuota exponent : ℝ)/2) := by
    unfold BinarySymmetric.Parameters.kappa
    field_simp [hQ.ne', P.channel.h_pos.ne']
  rw [heq] at hh
  have hreal : (P.channel.experiment.tapeLaw truth).real
      {tape | (P.commonQuota exponent : ℕ∞) < realPosteriorStop P.channel.experiment r tape} ≤
        delta/(2*(P.tools+1 : ℕ)) := by
    calc
      _ ≤ Real.exp (-((P.channel.gamma : ℝ)^2*(P.commonQuota exponent : ℝ)/2)) := hm.trans hh
      _ ≤ Real.exp (-(exponent : ℝ)) := Real.exp_le_exp.mpr (by linarith)
      _ ≤ Real.exp (-Real.log ((2*(P.tools+1 : ℕ) : ℝ)/delta)) :=
        Real.exp_le_exp.mpr (neg_le_neg (commonExponent_log_bounds P.tools delta exponent hd hminimal.2.1).2)
      _ = _ := by
        rw [Real.exp_neg, Real.exp_log (by positivity : (0 : ℝ) < (2*(P.tools+1 : ℕ) : ℝ)/delta)]
        exact inv_div _ _
  have h := ENNReal.ofReal_le_ofReal hreal
  simpa only [measureReal_def, ENNReal.ofReal_toReal (measure_ne_top _ _)] using h

end PDROC.StarOverflowTail
