module

public import PaperProofs.Star.RootStarEnvelope_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal

namespace RootStarCostSum

open PaperProofs.Star PaperProofs.Star.Parameters

noncomputable def target (P : Parameters) (r : ℝ) (j : ℕ) : ℝ :=
  countTargetReal (P.countBudgetReal r j) (P.tools-j)

noncomputable def price (P : Parameters) (r : ℝ) (j : ℕ) : ℝ :=
  P.channel.a * (Real.log (1 / target P r j) + P.channel.h)

noncomputable def tail (P : Parameters) (r : ℝ) (j : ℕ) : ℝ≥0∞ :=
  if j ≤ P.tools then ENNReal.ofReal (P.countObservationEnvelope (P.tools-j) (P.countBudgetReal r j)) else 0

theorem tail_step (P : Parameters) (r : ℝ) (hr : 0 < r) (hq : r ≤ 1/4)
    (j : ℕ) (hj : j ≤ P.tools) :
    tail P r j = ENNReal.ofReal (price P r j) + ENNReal.ofReal (target P r j) * tail P r (j+1) := by
  by_cases last : j = P.tools
  · subst j
    simp [tail, price, target, countTargetReal, countObservationEnvelope]
  · have next : j+1 ≤ P.tools := by omega
    have depth : P.tools-j = (P.tools-(j+1))+1 := by omega
    have nz : P.tools-j ≠ 0 := by omega
    have budgets := RootStarQuota.countBudget_bounds P r hr hq j
    have bp : 0 < P.countBudgetReal r j := hr.trans_le budgets.1
    obtain ⟨tp, _, tq⟩ := RootStarQuota.countTarget_bounds _ bp budgets.2 (P.tools-j)
    have pricePos : 0 ≤ price P r j := mul_nonneg P.channel.a_pos.le
      (add_nonneg (RootStarEnvelope.log_inverse_nonnegative _ tp tq) P.channel.h_pos.le)
    have nextBudgets := RootStarQuota.countBudget_bounds P r hr hq (j+1)
    have nextPos := RootStarEnvelope.envelope_nonnegative P (P.tools-(j+1))
      (P.countBudgetReal r (j+1)) (hr.trans_le nextBudgets.1) nextBudgets.2
    have realStep : P.countObservationEnvelope (P.tools-j) (P.countBudgetReal r j) =
        price P r j + target P r j * P.countObservationEnvelope (P.tools-(j+1)) (P.countBudgetReal r (j+1)) := by
      rw [depth, countObservationEnvelope]
      simp only [price, target, countTargetReal, ite_eq_right nz, countBudgetReal, ← depth]
    have targetNonneg : 0 ≤ target P r j := tp.le
    rw [tail, ite_eq_left hj, realStep, ENNReal.ofReal_add pricePos (mul_nonneg targetNonneg nextPos),
      ENNReal.ofReal_mul targetNonneg, tail, ite_eq_left next]

theorem count_cost_sum (P : Parameters) (r : ℝ) (hr : 0 < r) (hq : r ≤ 1/4) :
    (∑ j ∈ Finset.range (P.tools+1),
      (∏ i ∈ Finset.range j, ENNReal.ofReal (countTargetReal (P.countBudgetReal r i) (P.tools-i))) *
        ENNReal.ofReal (P.channel.a * (Real.log (1 / countTargetReal (P.countBudgetReal r j) (P.tools-j)) + P.channel.h))) =
      ENNReal.ofReal (P.countObservationEnvelope P.tools r) := by
  have invariant : ∀ n, n ≤ P.tools+1 →
      (∑ j ∈ Finset.range n, (∏ i ∈ Finset.range j, ENNReal.ofReal (target P r i)) * ENNReal.ofReal (price P r j)) +
        (∏ i ∈ Finset.range n, ENNReal.ofReal (target P r i)) * tail P r n = tail P r 0 := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      intro hn
      have before : n ≤ P.tools+1 := by omega
      have step := tail_step P r hr hq n (by omega)
      rw [Finset.sum_range_succ, Finset.prod_range_succ]
      calc
        _ = (∑ j ∈ Finset.range n, (∏ i ∈ Finset.range j, ENNReal.ofReal (target P r i)) * ENNReal.ofReal (price P r j)) +
            (∏ i ∈ Finset.range n, ENNReal.ofReal (target P r i)) *
              (ENNReal.ofReal (price P r n) + ENNReal.ofReal (target P r n) * tail P r (n+1)) := by
          rw [mul_add]; ac_rfl
        _ = tail P r 0 := by rw [← step]; exact ih before
  have final := invariant (P.tools+1) le_rfl
  simpa only [tail, Nat.add_one_le_iff, lt_self_iff_false, ite_false, mul_zero, add_zero,
    Nat.zero_le, ite_true, Nat.sub_zero, countBudgetReal, target, price] using final

end RootStarCostSum
