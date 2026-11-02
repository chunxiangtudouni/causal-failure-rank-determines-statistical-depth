module

public import PaperProofs.Paid.MultiplierSearch
public import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators

namespace PDROC.ZeroChargeLower.Binomial

/-- The literal original strict Bin(n,1/2) upper-tail sum. -/
def tail (n k : ℕ) : ℚ :=
  ∑ j ∈ Finset.range (n + 1),
    if k < j then (Nat.choose n j : ℚ) * (1 / 2 : ℚ) ^ n else 0

theorem tail_zero (k : ℕ) : tail 0 k = 0 := by
  simp [tail]

theorem sum_choose_half (n : ℕ) :
    (∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℚ) * (1 / 2 : ℚ) ^ n) = 1 := by
  have choose_sum : (∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℚ)) = (2 : ℚ) ^ n := by
    exact_mod_cast Nat.sum_range_choose n
  calc
    _ = (∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℚ)) * (1 / 2 : ℚ) ^ n :=
      (Finset.sum_mul _ _ _).symm
    _ = 1 := by rw [choose_sum, ← mul_pow]; norm_num

theorem tail_nonneg (n k : ℕ) : 0 ≤ tail n k := by
  unfold tail
  apply Finset.sum_nonneg
  intro j _member
  split_ifs <;> positivity

theorem tail_le_one (n k : ℕ) : tail n k ≤ 1 := by
  unfold tail
  calc
    _ ≤ ∑ j ∈ Finset.range (n + 1), (Nat.choose n j : ℚ) * (1 / 2 : ℚ) ^ n := by
      apply Finset.sum_le_sum
      intro j _member
      split_ifs
      · exact le_rfl
      · positivity
    _ = 1 := sum_choose_half n

theorem tail_eq_zero_of_le {n k : ℕ} (bound : n ≤ k) : tail n k = 0 := by
  unfold tail
  apply Finset.sum_eq_zero
  intro j member
  have upper : j ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp member)
  exact ite_eq_right (not_lt_of_ge (upper.trans bound))

private theorem tail_succ_split (n k : ℕ) :
    tail (n + 1) k =
      (tail n k + ∑ j ∈ Finset.range (n + 1),
        if k < j + 1 then (Nat.choose n j : ℚ) * (1 / 2 : ℚ) ^ n else 0) / 2 := by
  have recurrence := Finset.sum_choose_succ_mul
    (fun j _other : ℕ => if k < j then (1 / 2 : ℚ) ^ n else 0) n
  simp only [mul_ite, mul_zero] at recurrence
  calc
    _ = (∑ j ∈ Finset.range (n + 2),
        if k < j then (Nat.choose (n + 1) j : ℚ) * (1 / 2 : ℚ) ^ n else 0) / 2 := by
      unfold tail
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro j _member
      by_cases above : k < j
      · simp only [above, ite_true, pow_succ]
        ring
      · simp only [above, ite_false, zero_div]
    _ = _ := by
      unfold tail
      exact congrArg (fun value : ℚ => value / 2) recurrence

theorem tail_succ_zero (n : ℕ) : tail (n + 1) 0 = (tail n 0 + 1) / 2 := by
  rw [tail_succ_split]
  simp only [Nat.zero_lt_succ, ite_true, sum_choose_half]

theorem tail_succ_succ (n k : ℕ) :
    tail (n + 1) (k + 1) = (tail n (k + 1) + tail n k) / 2 := by
  have shifted : (∑ j ∈ Finset.range (n + 1),
      if k + 1 < j + 1 then (Nat.choose n j : ℚ) * (1 / 2 : ℚ) ^ n else 0) = tail n k := by
    simp only [Nat.add_lt_add_iff_right]
    rfl
  rw [tail_succ_split, shifted]

theorem tail_zero_eq (n : ℕ) : tail n 0 = 1 - (1 / 2 : ℚ) ^ n := by
  induction n with
  | zero => simp only [tail_zero, pow_zero, sub_self]
  | succ n ih => rw [tail_succ_zero, ih, pow_succ]; ring

theorem tail_stages_tools (P : PaperProofs.Paid.Parameters) :
    tail P.certificate.stages P.tools = P.blindBinomialTail := rfl

end PDROC.ZeroChargeLower.Binomial
