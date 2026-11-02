module

public import PaperProofs.Star.PStarLR_RealTestLaw_007
public import PaperProofs.Statistics.RationalQuota

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Statistics PaperProofs.Statistics.BinarySymmetric PaperProofs.Star

namespace PDROC.StarOverflowTail

theorem bsc_h_ge_gamma (channel : BinarySymmetric.Parameters) :
    (channel.gamma : ℝ) ≤ channel.h := by
  have hg : (0 : ℝ) < channel.gamma := by exact_mod_cast channel.gamma_pos
  have hquarter : (channel.gamma : ℝ) ≤ 1/4 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr channel.gamma_le_quarter
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hp : (0 : ℝ) < 1 + 2*(channel.gamma : ℝ) := by positivity
  have hm : (0 : ℝ) < 1 - 2*(channel.gamma : ℝ) := by linarith
  have hl := Real.one_sub_inv_le_log_of_pos (div_pos hp hm)
  rw [← channel.h_formula] at hl
  have hinv : 1 - ((1+2*(channel.gamma : ℝ))/(1-2*(channel.gamma : ℝ)))⁻¹ =
      4*(channel.gamma : ℝ)/(1+2*(channel.gamma : ℝ)) := by
    rw [inv_div]
    field_simp [hp.ne']
    ring
  rw [hinv] at hl
  apply le_trans _ hl
  apply (le_div_iff₀ hp).mpr
  nlinarith [mul_nonneg hg.le (show 0 ≤ 1/4-(channel.gamma : ℝ) by linarith)]

theorem bsc_incrementMax_eq_h (channel : BinarySymmetric.Parameters) :
    channel.experiment.channelIncrementMax = channel.h := by
  have hp (y : Fin 2) : |channel.experiment.channelLogIncrement true y| = channel.h := by
    change |Real.log (channel.experiment.channelReal true y / channel.experiment.channelReal false y)| = _
    rw [channel.logIncrement_eq_signed]
    split_ifs <;> simp only [Int.cast_one, Int.cast_neg, mul_one, mul_neg,
      abs_neg, abs_of_pos channel.h_pos]
  unfold BinaryExperiment.channelIncrementMax
  apply le_antisymm
  · exact Finset.sup'_le _ _ (fun y _ => (hp y).le)
  · have hle := Finset.le_sup'
      (fun y : Fin channel.experiment.alphabetSize => |channel.experiment.channelLogIncrement true y|)
      (Finset.mem_univ channel.experiment.completionSymbol)
    exact (hp channel.experiment.completionSymbol).symm.le.trans hle

theorem bsc_priorLogOddsMax_zero (channel : BinarySymmetric.Parameters) :
    channel.experiment.priorLogOddsMax = 0 := by
  norm_num [BinaryExperiment.priorLogOddsMax, BinaryExperiment.priorReal, channel.prior_eq_half]

theorem commonQuota_drift_lower (P : PaperProofs.Star.Parameters) (exponent : ℕ) :
    2*(exponent : ℝ) ≤ (P.channel.gamma : ℝ)^2 * (P.commonQuota exponent : ℝ) := by
  have hq : (2*(exponent : ℚ)/P.channel.gamma^2) ≤ (P.commonQuota exponent : ℚ) := Nat.le_ceil _
  have h := (Rat.cast_le (K := ℝ)).mpr hq
  push_cast at h
  have hg : (0 : ℝ) < P.channel.gamma := by exact_mod_cast P.channel.gamma_pos
  have hh := (div_le_iff₀ (sq_pos_of_pos hg)).mp h
  nlinarith

theorem commonQuota_pos (P : PaperProofs.Star.Parameters) (exponent : ℕ) (he : 1 ≤ exponent) :
    0 < P.commonQuota exponent := by
  have h := commonQuota_drift_lower P exponent
  have her : (1 : ℝ) ≤ exponent := by exact_mod_cast he
  have hp : (0 : ℝ) < P.commonQuota exponent := by nlinarith
  exact_mod_cast hp

theorem commonExponent_log_bounds (q : ℕ) (delta : ℝ) (exponent : ℕ)
    (hd : 0 < delta) (hqual : DyadicQualifies (20*(q+1 : ℕ)) delta exponent) :
    Real.log (10/delta) ≤ exponent ∧ Real.log ((2*(q+1 : ℕ) : ℝ)/delta) ≤ exponent := by
  have ht := hqual
  dsimp only [DyadicQualifies] at ht
  push_cast at ht
  have hq : (0 : ℝ) ≤ q := Nat.cast_nonneg _
  have hten : 10/delta ≤ (2 : ℝ)^exponent := (div_le_iff₀ hd).mpr (by nlinarith)
  have htwo : (2*(q+1 : ℕ) : ℝ)/delta ≤ (2 : ℝ)^exponent := by
    apply (div_le_iff₀ hd).mpr
    push_cast
    nlinarith
  exact ⟨BinaryExperiment.log_le_integer_of_le_two_pow _ (by positivity) _ hten,
    BinaryExperiment.log_le_integer_of_le_two_pow _ (by positivity) _ htwo⟩

theorem real_threshold_le_exponent (q : ℕ) (delta r : ℝ) (exponent : ℕ)
    (hd : 0 < delta) (hr : 0 < r) (hrhalf : r ≤ 1/2) (hfloor : delta/10 ≤ r)
    (hqual : DyadicQualifies (20*(q+1 : ℕ)) delta exponent) :
    Real.log ((1-r)/r) ≤ exponent := by
  have hinv : 1/r ≤ 10/delta := (div_le_div_iff₀ hr hd).mpr (by nlinarith)
  have hratio : (1-r)/r ≤ 10/delta :=
    (div_le_div_of_nonneg_right (by linarith : 1-r ≤ 1) hr.le).trans hinv
  exact (Real.log_le_log (div_pos (by linarith) hr) hratio).trans
    (commonExponent_log_bounds q delta exponent hd hqual).1

end PDROC.StarOverflowTail
