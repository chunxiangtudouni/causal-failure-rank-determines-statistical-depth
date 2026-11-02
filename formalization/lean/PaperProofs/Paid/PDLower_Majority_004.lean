module

public import PaperProofs.Paid.PDLower_Majority_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Statistics

namespace PDLower

theorem majority_radius_sq (P : BinarySymmetric.Parameters) (n : ℕ) :
    ((2 : ℝ) ^ n * Real.sqrt (((1 / 4 : ℝ) - (P.gamma : ℝ) ^ 2) ^ n)) ^ 2 =
      (1 - 4 * (P.gamma : ℝ) ^ 2) ^ n := by
  have hp : ((2 : ℝ) ^ n) ^ 2 = (4 : ℝ) ^ n := by
    rw [← pow_mul, Nat.mul_comm n 2, pow_mul]
    norm_num
  rw [mul_pow, hp, Real.sq_sqrt (pow_nonneg (majority_variance_quarter_nonneg P) n)]
  rw [← mul_pow]
  congr 1
  ring

theorem majority_tail_of_variance (P : BinarySymmetric.Parameters) (n : ℕ) (x : Bool)
    (target : ℝ) (htarget : 0 ≤ target)
    (hvariance : (1 - 4 * (P.gamma : ℝ) ^ 2) ^ n ≤ target ^ 2) :
    P.experiment.tapeLaw x
      {tape | decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore
        (List.ofFn (fun i : Fin n => (tape i.val).val))) ≠ x} ≤ ENNReal.ofReal target := by
  let radius := (2 : ℝ) ^ n * Real.sqrt (((1 / 4 : ℝ) - (P.gamma : ℝ) ^ 2) ^ n)
  have hr0 : 0 ≤ radius := mul_nonneg (pow_nonneg (by norm_num) n) (Real.sqrt_nonneg _)
  have hrsq : radius ^ 2 ≤ target ^ 2 := by
    change ((2 : ℝ) ^ n * Real.sqrt (((1 / 4 : ℝ) - (P.gamma : ℝ) ^ 2) ^ n)) ^ 2 ≤ _
    rw [majority_radius_sq]
    exact hvariance
  have hr : radius ≤ target := (sq_le_sq₀ hr0 htarget).mp hrsq
  calc
    _ ≤ (2 : ℝ≥0∞) ^ n * ENNReal.ofReal (Real.sqrt (((1 / 4 : ℝ) - (P.gamma : ℝ) ^ 2) ^ n)) :=
      majority_finite_word_bound P n x
    _ = ENNReal.ofReal radius := by
      rw [ENNReal.ofReal_mul (pow_nonneg (show (0 : ℝ) ≤ 2 by norm_num) n),
        ENNReal.ofReal_pow (p := 2) (by norm_num) n]
      norm_num
    _ ≤ _ := ENNReal.ofReal_le_ofReal hr

end PDLower
