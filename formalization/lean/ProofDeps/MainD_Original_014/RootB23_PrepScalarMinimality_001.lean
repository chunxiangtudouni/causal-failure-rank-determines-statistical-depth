module

public import PaperProofs.Statistics.RationalQuota

/-! Exact stopping tests for the ORIGINAL preparation numbers. These lemmas
do not supply a machine or an arithmetic oracle. A native consumer still
has to implement every comparison, increment, branch and output transfer.
The quota bounds justify counting such loops in the original arithmeticScale,
which already contains the numerical quotas. -/

@[expose] public section
set_option autoImplicit false
set_option warningAsError true

open scoped BigOperators

namespace RootB23.PrepScalar

open PaperProofs.Statistics

theorem ratio_bound_le_iff (r : Rat) (n : Nat) :
    BinaryExperiment.ratioIntegerBound r ≤ n ↔
      r ≤ (2 : Rat)^n ∧ 1/r ≤ (2 : Rat)^n := by
  rw [BinaryExperiment.ratioIntegerBound, Nat.clog_le_iff_le_pow (by norm_num), Nat.ceil_le]
  simp only [Nat.cast_pow, Nat.cast_ofNat, max_le_iff]

theorem ratio_first_pass (r : Rat) (n : Nat)
    (pass : r ≤ (2 : Rat)^n ∧ 1/r ≤ (2 : Rat)^n)
    (earlier : ∀ k < n, ¬(r ≤ (2 : Rat)^k ∧ 1/r ≤ (2 : Rat)^k)) :
    BinaryExperiment.ratioIntegerBound r = n := by
  apply Nat.le_antisymm ((ratio_bound_le_iff r n).mpr pass)
  by_contra failed
  exact earlier _ (Nat.lt_of_not_ge failed) ((ratio_bound_le_iff r _).mp le_rfl)

theorem quota_le_iff (E : BinaryExperiment) (exponent n : Nat) :
    E.rationalQuota exponent ≤ n ↔
      2*((exponent : Rat)+E.priorIntegerMax)/E.channelDriftLower ≤ n ∧
      8*(E.channelIntegerMax : Rat)^2*exponent/E.channelDriftLower^2 ≤ n := by
  rw [BinaryExperiment.rationalQuota, Nat.ceil_le, max_le_iff]

theorem quota_first_pass (E : BinaryExperiment) (exponent n : Nat)
    (pass : 2*((exponent : Rat)+E.priorIntegerMax)/E.channelDriftLower ≤ n ∧
      8*(E.channelIntegerMax : Rat)^2*exponent/E.channelDriftLower^2 ≤ n)
    (earlier : ∀ k < n, ¬(2*((exponent : Rat)+E.priorIntegerMax)/E.channelDriftLower ≤ k ∧
      8*(E.channelIntegerMax : Rat)^2*exponent/E.channelDriftLower^2 ≤ k)) :
    E.rationalQuota exponent = n := by
  apply Nat.le_antisymm ((quota_le_iff E exponent n).mpr pass)
  by_contra failed
  exact earlier _ (Nat.lt_of_not_ge failed) ((quota_le_iff E exponent _).mp le_rfl)

theorem exponent_le_iff (budget : Rat) (positive : 0 < budget) (N n : Nat) :
    BinaryExperiment.quotaExponent budget N ≤ n ↔
      1 ≤ n ∧ (2*N*referenceQuotaConstant N : Rat) ≤ (2 : Rat)^n*budget := by
  rw [BinaryExperiment.quotaExponent, max_le_iff,
    Nat.clog_le_iff_le_pow (by norm_num), Nat.ceil_le, div_le_iff₀ positive]
  simp only [Nat.cast_pow, Nat.cast_ofNat]

theorem exponent_first_pass (budget : Rat) (positive : 0 < budget) (N n : Nat)
    (pass : 1 ≤ n ∧ (2*N*referenceQuotaConstant N : Rat) ≤ (2 : Rat)^n*budget)
    (earlier : ∀ k < n, ¬(1 ≤ k ∧ (2*N*referenceQuotaConstant N : Rat) ≤ (2 : Rat)^k*budget)) :
    BinaryExperiment.quotaExponent budget N = n := by
  apply Nat.le_antisymm ((exponent_le_iff budget positive N n).mpr pass)
  by_contra failed
  exact earlier _ (Nat.lt_of_not_ge failed) ((exponent_le_iff budget positive N _).mp le_rfl)

theorem exponent_zero_stages (budget : Rat) : BinaryExperiment.quotaExponent budget 0 = 1 := by
  simp [BinaryExperiment.quotaExponent]

theorem channelTV_le_one (E : BinaryExperiment) : E.channelTV ≤ 1 := by
  have bound : (∑ y : Fin E.alphabetSize, |E.channel false y-E.channel true y|) ≤
      ∑ y : Fin E.alphabetSize, (E.channel false y+E.channel true y) := by
    apply Finset.sum_le_sum
    intro y _
    have left := (E.channel_pos false y).le
    have right := (E.channel_pos true y).le
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rw [Finset.sum_add_distrib, E.channel_sum false, E.channel_sum true] at bound
  unfold BinaryExperiment.channelTV
  linarith

theorem drift_le_two (E : BinaryExperiment) : E.channelDriftLower ≤ 2 := by
  have lower := E.channelTV_pos
  have upper := channelTV_le_one E
  unfold BinaryExperiment.channelDriftLower
  nlinarith

theorem exponent_add_prior_le_quota (E : BinaryExperiment) (exponent : Nat) :
    exponent+E.priorIntegerMax ≤ E.rationalQuota exponent := by
  have tests := (quota_le_iff E exponent _).mp le_rfl
  have positive := E.channelDriftLower_pos
  have drift := drift_le_two E
  have Qnonneg : (0 : Rat) ≤ E.rationalQuota exponent := Nat.cast_nonneg _
  have multiplied := (div_le_iff₀ positive).mp tests.1
  have upper := mul_le_mul_of_nonneg_left drift Qnonneg
  have result : (exponent : Rat)+E.priorIntegerMax ≤ E.rationalQuota exponent := by nlinarith
  exact_mod_cast result

theorem channel_integer_le_quota (E : BinaryExperiment) (exponent : Nat) (positive : 1 ≤ exponent) :
    E.channelIntegerMax ≤ E.rationalQuota exponent := by
  have tests := (quota_le_iff E exponent _).mp le_rfl
  have dpositive := E.channelDriftLower_pos
  have drift := drift_le_two E
  have dsquare : E.channelDriftLower^2 ≤ 4 := by nlinarith
  have Qnonneg : (0 : Rat) ≤ E.rationalQuota exponent := Nat.cast_nonneg _
  have multiplied := (div_le_iff₀ (sq_pos_of_pos dpositive)).mp tests.2
  have upper := mul_le_mul_of_nonneg_left dsquare Qnonneg
  have epositive : (1 : Rat) ≤ exponent := by exact_mod_cast positive
  have lower := mul_le_mul_of_nonneg_left epositive (show (0 : Rat) ≤ 8*(E.channelIntegerMax : Rat)^2 by positivity)
  have integer_square : (E.channelIntegerMax : Rat) ≤ (E.channelIntegerMax : Rat)^2 := by
    cases value : E.channelIntegerMax with
    | zero => simp
    | succ k => push_cast; nlinarith [sq_nonneg (k : Rat)]
  have result : (E.channelIntegerMax : Rat) ≤ E.rationalQuota exponent := by nlinarith
  exact_mod_cast result

end RootB23.PrepScalar
