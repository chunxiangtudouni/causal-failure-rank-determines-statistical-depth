module

public import PaperProofs.Paid.ComputationalClaims
public import Mathlib.Data.Nat.Choose.Bounds
public import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.D27Prepare.Binomial

/-- The integer held in the rational tail accumulator before index j.
The upper limit is N+1, independently of the numeric value of K. -/
def partialTail (N K j : ℕ) : ℕ :=
  ∑ i ∈ Finset.range j, if K < i then N.choose i else 0

theorem partialTail_zero (N K : ℕ) : partialTail N K 0 = 0 := by
  simp [partialTail]

theorem partialTail_succ (N K j : ℕ) :
    partialTail N K (j + 1) = partialTail N K j + if K < j then N.choose j else 0 := by
  exact Finset.sum_range_succ _ _

theorem partialTail_le (N K j : ℕ) (hj : j ≤ N + 1) : partialTail N K j ≤ 2 ^ N := by
  calc
    partialTail N K j ≤ ∑ i ∈ Finset.range j, N.choose i := by
      apply Finset.sum_le_sum
      intro i _
      split_ifs <;> omega
    _ ≤ ∑ i ∈ Finset.range (N + 1), N.choose i :=
      Finset.sum_le_sum_of_subset (Finset.range_mono hj)
    _ = 2 ^ N := Nat.sum_range_choose N

/-- The exact multiply/divide recurrence used by page30; the denominator
is i+1 even on the final i=N iteration, hence never zero. -/
theorem choose_rat_step (N i : ℕ) :
    (N.choose i : ℚ) * ((N - i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ) =
      (N.choose (i + 1) : ℚ) := by
  apply (div_eq_iff (by positivity : ((i + 1 : ℕ) : ℚ) ≠ 0)).mpr
  exact_mod_cast (Nat.choose_succ_right_eq N i).symm

theorem choose_rat_step_grouped (N i : ℕ) :
    (N.choose i : ℚ) * (((N - i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)) =
      (N.choose (i + 1) : ℚ) := by
  simpa only [mul_div_assoc] using choose_rat_step N i

theorem choose_product_le (N i : ℕ) :
    N.choose i * (N - i) ≤ N * 2 ^ N := by
  calc
    N.choose i * (N - i) ≤ 2 ^ N * N :=
      Nat.mul_le_mul (Nat.choose_le_two_pow N i) (Nat.sub_le N i)
    _ = N * 2 ^ N := Nat.mul_comm _ _

theorem ratio_nonnegative (N i : ℕ) :
    0 ≤ (((N - i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)) := by positivity

theorem ratio_le (N i : ℕ) :
    (((N - i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)) ≤ (N : ℚ) := by
  apply (div_le_iff₀ (by positivity : (0 : ℚ) < ((i + 1 : ℕ) : ℚ))).mpr
  have hs : ((N - i : ℕ) : ℚ) ≤ N := by exact_mod_cast Nat.sub_le N i
  have hi : (1 : ℚ) ≤ ((i + 1 : ℕ) : ℚ) := by exact_mod_cast (by omega : 1 ≤ i + 1)
  nlinarith

theorem partialTail_rat_succ (N K i : ℕ) :
    (partialTail N K (i + 1) : ℚ) =
      (partialTail N K i : ℚ) + if K < i then (N.choose i : ℚ) else 0 := by
  rw [partialTail_succ, Nat.cast_add]
  split_ifs <;> simp

theorem partialTail_rat_le (N K i : ℕ) (hi : i ≤ N + 1) :
    0 ≤ (partialTail N K i : ℚ) ∧ (partialTail N K i : ℚ) ≤ (2 : ℚ) ^ N := by
  constructor
  · positivity
  · exact_mod_cast partialTail_le N K i hi

theorem final_tail_eq (P : Parameters) :
    (partialTail P.certificate.stages P.tools (P.certificate.stages + 1) : ℚ) *
      (1 / 2 : ℚ) ^ P.certificate.stages = P.blindBinomialTail := by
  unfold partialTail blindBinomialTail
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i _
  split_ifs <;> simp

theorem dyadic_step (i : ℕ) :
    (1 / 2 : ℚ) ^ i * (1 / 2 : ℚ) = (1 / 2 : ℚ) ^ (i + 1) := by
  exact (pow_succ _ _).symm

theorem original_zeta_fee_zero (P : Parameters) :
    (partialTail P.certificate.stages P.tools (P.certificate.stages + 1) : ℚ) *
      (1 / 2 : ℚ) ^ P.certificate.stages = P.zeroChargeRisk 0 := by
  simpa [zeroChargeRisk] using final_tail_eq P

end PDROC.D27Prepare.Binomial
