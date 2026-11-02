module

public import PaperProofs.Paid.PDROC_ZeroChargeLower_001
public import PaperProofs.Paid.PDROC_ZeroChargeLower_Binomial_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open scoped ENNReal
open PaperProofs.Paid

namespace PDROC.ZeroChargeLower

theorem half_ofReal_scaled_sum (a x y : ℚ) (ha : 0 ≤ a) (hx : 0 ≤ x) (hy : 0 ≤ y) :
    ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal ((a * x : ℚ) : ℝ) +
      ENNReal.ofReal (1 / 2 : ℝ) * ENNReal.ofReal ((a * y : ℚ) : ℝ) =
        ENNReal.ofReal ((a * ((x + y) / 2) : ℚ) : ℝ) := by
  have hax : (0 : ℝ) ≤ ((a * x : ℚ) : ℝ) := by exact_mod_cast mul_nonneg ha hx
  have hay : (0 : ℝ) ≤ ((a * y : ℚ) : ℝ) := by exact_mod_cast mul_nonneg ha hy
  rw [← ENNReal.ofReal_mul (by norm_num), ← ENNReal.ofReal_mul (by norm_num),
    ← ENNReal.ofReal_add (mul_nonneg (by norm_num) hax) (mul_nonneg (by norm_num) hay)]
  congr 1
  push_cast
  ring

/-- Exact independent full-policy F at every small rational penalty when
corrections have zero fee. All n,k, including k≥n, are retained. -/
theorem freshPaidPenalty_zeroFee (P : Parameters) (hfee : (0 : ℚ) ≤ 0)
    (a : ℚ) (ha : 0 ≤ a) (hreview : a ≤ P.reviewFee) (n k : ℕ) :
    P.freshPaidPenalty 0 hfee n k (ENNReal.ofReal (a : ℝ)) =
      ENNReal.ofReal ((a * Binomial.tail n k : ℚ) : ℝ) := by
  have small : ENNReal.ofReal (a : ℝ) ≤ ENNReal.ofReal (P.reviewFee : ℝ) :=
    ENNReal.ofReal_le_ofReal (by exact_mod_cast hreview)
  induction n generalizing k with
  | zero => simp only [P.freshPaidPenalty_empty, Binomial.tail_zero, mul_zero, Rat.cast_zero,
      ENNReal.ofReal_zero]
  | succ n ih =>
    rw [freshPaidPenalty_small_step P 0 hfee (n + 1) k (by omega) _ small]
    simp only [Parameters.paidGoodSuccessor, Nat.add_sub_cancel]
    cases k with
    | zero =>
      rw [Parameters.paidBadSuccessor, ih, Binomial.tail_succ_zero]
      simpa only [mul_one] using half_ofReal_scaled_sum a (Binomial.tail n 0) 1
        ha (Binomial.tail_nonneg n 0) (by norm_num)
    | succ k =>
      have bad : P.paidBadSuccessor 0 hfee (n + 1) (k + 1) (ENNReal.ofReal (a : ℝ)) =
          P.freshPaidPenalty 0 hfee n k (ENNReal.ofReal (a : ℝ)) := by
        simp only [Parameters.paidBadSuccessor, Rat.cast_zero, ENNReal.ofReal_zero, zero_add,
          Nat.add_sub_cancel]
        exact min_eq_right (P.freshPaidPenalty_le_penalty 0 hfee n k _)
      rw [bad, ih, ih, Binomial.tail_succ_succ]
      exact half_ofReal_scaled_sum a (Binomial.tail n (k + 1)) (Binomial.tail n k)
        ha (Binomial.tail_nonneg n (k + 1)) (Binomial.tail_nonneg n k)

/-- A correction price at least the penalty makes the actual bad branch
equal abandonment, still inside the original full-policy Bellman problem. -/
theorem paidBadSuccessor_eq_smallPenalty (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (a : ℚ) (hprice : a ≤ fee) (n k : ℕ) :
    P.paidBadSuccessor fee hfee n k (ENNReal.ofReal (a : ℝ)) = ENNReal.ofReal (a : ℝ) := by
  cases k with
  | zero => rfl
  | succ k =>
    apply min_eq_left
    exact (ENNReal.ofReal_le_ofReal (by exact_mod_cast hprice)).trans (le_add_right le_rfl)

theorem freshPaidPenalty_fee_ge_smallPenalty (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (a : ℚ) (ha : 0 ≤ a) (hreview : a ≤ P.reviewFee) (hprice : a ≤ fee) (n k : ℕ) :
    P.freshPaidPenalty fee hfee n k (ENNReal.ofReal (a : ℝ)) =
      ENNReal.ofReal ((a * Binomial.tail n 0 : ℚ) : ℝ) := by
  have small : ENNReal.ofReal (a : ℝ) ≤ ENNReal.ofReal (P.reviewFee : ℝ) :=
    ENNReal.ofReal_le_ofReal (by exact_mod_cast hreview)
  induction n generalizing k with
  | zero => simp only [P.freshPaidPenalty_empty, Binomial.tail_zero, mul_zero, Rat.cast_zero,
      ENNReal.ofReal_zero]
  | succ n ih =>
    rw [freshPaidPenalty_small_step P fee hfee (n + 1) k (by omega) _ small,
      paidBadSuccessor_eq_smallPenalty P fee hfee a hprice]
    simp only [Parameters.paidGoodSuccessor, Nat.add_sub_cancel]
    rw [ih, Binomial.tail_succ_zero]
    simpa only [mul_one] using half_ofReal_scaled_sum a (Binomial.tail n 0) 1
      ha (Binomial.tail_nonneg n 0) (by norm_num)

/-- Original small-penalty identity for the independently defined full
history policy infimum, with no small-penalty identity supplied as a premise. -/
theorem smallPenaltyValue (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    P.freshPaidPenalty fee hfee P.certificate.stages P.tools
      (ENNReal.ofReal (P.firstChargeFloor fee : ℝ)) =
        ENNReal.ofReal ((P.firstChargeFloor fee * P.zeroChargeRisk fee : ℚ) : ℝ) := by
  by_cases free : fee = 0
  · subst fee
    change P.freshPaidPenalty 0 hfee P.certificate.stages P.tools
      (ENNReal.ofReal (P.reviewFee : ℝ)) =
        ENNReal.ofReal ((P.reviewFee * P.blindBinomialTail : ℚ) : ℝ)
    rw [← Binomial.tail_stages_tools P]
    exact freshPaidPenalty_zeroFee P hfee P.reviewFee P.reviewFee_pos.le le_rfl _ _
  · have floorEq : P.firstChargeFloor fee = min P.reviewFee fee := by
      simp only [Parameters.firstChargeFloor, free, ite_false]
    have nonneg : 0 ≤ P.firstChargeFloor fee := by
      rw [floorEq]
      exact le_min P.reviewFee_pos.le hfee
    have review : P.firstChargeFloor fee ≤ P.reviewFee := by rw [floorEq]; exact min_le_left _ _
    have price : P.firstChargeFloor fee ≤ fee := by rw [floorEq]; exact min_le_right _ _
    have identity := freshPaidPenalty_fee_ge_smallPenalty P fee hfee (P.firstChargeFloor fee)
      nonneg review price P.certificate.stages P.tools
    simpa only [Parameters.zeroChargeRisk, free, ite_false, Binomial.tail_zero_eq] using identity

end PDROC.ZeroChargeLower
