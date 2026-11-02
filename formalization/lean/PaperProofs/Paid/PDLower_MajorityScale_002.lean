module

public import PaperProofs.Paid.PDLower_MajorityScale_001
public import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDLower

theorem majority_power_of_time {g R : ℝ} (hg : 0 < g) (hgq : g ≤ 1 / 4)
    (hR : 1 < R) (t : ℕ) (ht : Real.log R / (2 * g ^ 2) ≤ (t : ℝ)) :
    (1 - 4 * g ^ 2) ^ t ≤ (R⁻¹) ^ 2 := by
  have hsq : g ^ 2 ≤ 1 / 16 := by nlinarith [mul_self_le_mul_self hg.le hgq]
  have hv : 0 < 1 - 4 * g ^ 2 := by linarith
  have hR0 : 0 < R := lt_trans zero_lt_one hR
  have hl : Real.log (1 - 4 * g ^ 2) ≤ -(4 * g ^ 2) := by
    have h := Real.log_le_sub_one_of_pos hv
    linarith
  have ht' : Real.log R ≤ (t : ℝ) * (2 * g ^ 2) :=
    (div_le_iff₀ (by positivity : 0 < 2 * g ^ 2)).mp ht
  apply (Real.log_le_log_iff (pow_pos hv t) (sq_pos_of_pos (inv_pos.mpr hR0))).mp
  rw [Real.log_pow, Real.log_pow, Real.log_inv]
  norm_num only [Nat.cast_ofNat]
  have hmul := mul_le_mul_of_nonneg_left hl (Nat.cast_nonneg t)
  nlinarith

noncomputable def majorityUpperTime (g R : ℝ) : ℕ :=
  2 * Nat.ceil (Real.log R / (4 * g ^ 2)) + 1

theorem majorityUpperTime_pos (g R : ℝ) : 1 ≤ majorityUpperTime g R := by
  unfold majorityUpperTime
  omega

theorem majorityUpperTime_odd (g R : ℝ) : Odd (majorityUpperTime g R) := by
  exact ⟨Nat.ceil (Real.log R / (4 * g ^ 2)), by unfold majorityUpperTime; omega⟩

theorem majorityUpperTime_lower (g R : ℝ) :
    Real.log R / (2 * g ^ 2) ≤ (majorityUpperTime g R : ℝ) := by
  have hn := Nat.le_ceil (Real.log R / (4 * g ^ 2))
  have heq : (2 : ℝ) * (Real.log R / (4 * g ^ 2)) = Real.log R / (2 * g ^ 2) := by
    field_simp
    ring
  simp only [majorityUpperTime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [← heq]
  linarith

theorem majorityUpperTime_upper (g R : ℝ) (hR : 1 < R) :
    (majorityUpperTime g R : ℝ) ≤ Real.log R / (2 * g ^ 2) + 3 := by
  have ha : 0 ≤ Real.log R / (4 * g ^ 2) := div_nonneg (Real.log_pos hR).le (by positivity)
  have hn := Nat.ceil_lt_add_one ha
  have heq : (2 : ℝ) * (Real.log R / (4 * g ^ 2)) = Real.log R / (2 * g ^ 2) := by
    field_simp
    ring
  simp only [majorityUpperTime, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
  rw [← heq]
  linarith

end PDLower
