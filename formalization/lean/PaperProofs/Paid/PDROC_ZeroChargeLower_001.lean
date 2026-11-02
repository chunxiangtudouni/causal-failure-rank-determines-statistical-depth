module

public import PaperProofs.Paid.PDMenu_PaidPenaltyProgram_059
public import PaperProofs.Paid.MultiplierSearch

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open scoped ENNReal
open PaperProofs.Paid

namespace PDROC.ZeroChargeLower

theorem half_mul_add_self (x : ℝ≥0∞) :
    ENNReal.ofReal (1 / 2 : ℝ) * x + ENNReal.ofReal (1 / 2 : ℝ) * x = x := by
  rw [← add_mul, ← ENNReal.ofReal_add (by norm_num) (by norm_num)]
  norm_num

theorem paidEndpointObjective_zero (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (penalty : ℝ≥0∞) :
    P.paidEndpointObjective fee hfee n k penalty 0 =
      ENNReal.ofReal (1 / 2 : ℝ) * P.paidGoodSuccessor fee hfee n k penalty +
      ENNReal.ofReal (1 / 2 : ℝ) * P.paidBadSuccessor fee hfee n k penalty := by
  norm_num [Parameters.paidEndpointObjective]

theorem paidEndpointObjective_zero_le_penalty (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (penalty : ℝ≥0∞) : P.paidEndpointObjective fee hfee n k penalty 0 ≤ penalty := by
  rw [paidEndpointObjective_zero]
  calc
    _ ≤ ENNReal.ofReal (1 / 2 : ℝ) * penalty + ENNReal.ofReal (1 / 2 : ℝ) * penalty :=
      add_le_add (mul_le_mul' le_rfl (P.freshPaidPenalty_le_penalty fee hfee (n - 1) k penalty))
        (mul_le_mul' le_rfl (PDMenu.paidBadSuccessor_le_penalty P fee hfee n k penalty))
    _ = penalty := half_mul_add_self penalty

theorem endpointCharge_ge_reviewFee (P : Parameters) (m : ℕ) (hm : 1 ≤ m) :
    P.reviewFee ≤ P.binarySymmetric.endpointCharge m := by
  have hlin := PDMenu.endpointCharge_linear_lower P.binarySymmetric m
  change P.reviewFee * (m : ℚ) ≤ P.binarySymmetric.endpointCharge m at hlin
  have hone : (1 : ℚ) ≤ (m : ℚ) := by exact_mod_cast hm
  calc
    P.reviewFee = P.reviewFee * 1 := (mul_one _).symm
    _ ≤ P.reviewFee * m := mul_le_mul_of_nonneg_left hone P.reviewFee_pos.le
    _ ≤ _ := hlin

/-- At a multiplier no greater than one genuine review fee, every
positive endpoint level is dominated by the original zero-review level. -/
theorem endpoint_zero_minimizes_smallPenalty (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (penalty : ℝ≥0∞) (hsmall : penalty ≤ ENNReal.ofReal (P.reviewFee : ℝ)) :
    P.IsPaidEndpointMinimizer fee hfee n k penalty 0 := by
  intro m
  cases m with
  | zero => exact le_rfl
  | succ m =>
    have hcharge : ENNReal.ofReal (P.reviewFee : ℝ) ≤
        ENNReal.ofReal (P.binarySymmetric.endpointCharge (m + 1) : ℝ) :=
      ENNReal.ofReal_le_ofReal (by exact_mod_cast endpointCharge_ge_reviewFee P (m + 1) (by omega))
    apply (paidEndpointObjective_zero_le_penalty P fee hfee n k penalty).trans
    apply hsmall.trans (hcharge.trans ?_)
    unfold Parameters.paidEndpointObjective
    exact le_add_right (le_add_right le_rfl)

/-- The independently defined full-policy value has the exact zero-review
Bellman step at every small multiplier. No recurrence is made a definition. -/
theorem freshPaidPenalty_small_step (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (hn : 0 < n) (penalty : ℝ≥0∞)
    (hsmall : penalty ≤ ENNReal.ofReal (P.reviewFee : ℝ)) :
    P.freshPaidPenalty fee hfee n k penalty =
      ENNReal.ofReal (1 / 2 : ℝ) * P.paidGoodSuccessor fee hfee n k penalty +
      ENNReal.ofReal (1 / 2 : ℝ) * P.paidBadSuccessor fee hfee n k penalty := by
  have hp : penalty ≠ ⊤ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hsmall
  have hmin := endpoint_zero_minimizes_smallPenalty P fee hfee n k penalty hsmall
  have hinf : (⨅ m : ℕ, P.paidEndpointObjective fee hfee n k penalty m) =
      P.paidEndpointObjective fee hfee n k penalty 0 :=
    le_antisymm (iInf_le _ 0) (le_iInf hmin)
  rw [PDMenu.paidExactPenaltyBellman P fee hfee n k penalty hn hp, hinf,
    min_eq_right (paidEndpointObjective_zero_le_penalty P fee hfee n k penalty), paidEndpointObjective_zero]

end PDROC.ZeroChargeLower
