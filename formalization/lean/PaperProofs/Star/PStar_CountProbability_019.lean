module

public import PaperProofs.Star.PStar_LocalWorld_012
public import PaperProofs.Star.RootStarQuota_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarCountProbability019

open Parameters MeasureTheory
open scoped BigOperators ENNReal

noncomputable def stageTarget (P : PaperProofs.Star.Parameters) (r : ℝ) (stage : ℕ) : ℝ :=
  countTargetReal (P.countBudgetReal r stage) (P.tools - stage)

noncomputable def prefixWeight (P : PaperProofs.Star.Parameters) (r : ℝ) (length : ℕ) : ℝ≥0∞ :=
  ∏ stage ∈ Finset.range length, ENNReal.ofReal (stageTarget P r stage)

theorem stageTarget_bounds (P : PaperProofs.Star.Parameters) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1 / 4) (stage : ℕ) :
    0 < stageTarget P r stage ∧ stageTarget P r stage ≤ 1 / 4 := by
  have budget := RootStarQuota.countBudget_bounds P r positive quarter stage
  have target := RootStarQuota.countTarget_bounds _ (positive.trans_le budget.1) budget.2 (P.tools - stage)
  exact ⟨target.1, target.2.2⟩

theorem target_mul_next_budget_le (P : PaperProofs.Star.Parameters) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1 / 4) (stage : ℕ) :
    stageTarget P r stage * P.countBudgetReal r (stage+1) ≤ P.countBudgetReal r stage := by
  have targetPositive := (stageTarget_bounds P r positive quarter stage).1
  change stageTarget P r stage * min (1 / 4) (P.countBudgetReal r stage / stageTarget P r stage) ≤ _
  calc
    _ ≤ stageTarget P r stage * (P.countBudgetReal r stage / stageTarget P r stage) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) targetPositive.le
    _ = _ := by field_simp [targetPositive.ne']

theorem prefixWeight_succ (P : PaperProofs.Star.Parameters) (r : ℝ) (length : ℕ) :
    prefixWeight P r (length+1) = prefixWeight P r length * ENNReal.ofReal (stageTarget P r length) := by
  exact Finset.prod_range_succ _ _

/-- The original adaptive count budgets telescope in ENNReal; no division
of event probabilities, positive event mass or attainment assumption. -/
theorem prefixWeight_mul_budget_le (P : PaperProofs.Star.Parameters) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1 / 4) (length : ℕ) :
    prefixWeight P r length * ENNReal.ofReal (P.countBudgetReal r length) ≤ ENNReal.ofReal r := by
  induction length with
  | zero => simp only [prefixWeight, Finset.range_zero, Finset.prod_empty, countBudgetReal, one_mul, le_refl]
  | succ length ih =>
    rw [prefixWeight_succ, mul_assoc,
      ← ENNReal.ofReal_mul (stageTarget_bounds P r positive quarter length).1.le]
    exact (mul_le_mul' le_rfl (ENNReal.ofReal_le_ofReal
      (target_mul_next_budget_le P r positive quarter length))).trans ih

theorem fullErrorProduct_le (P : PaperProofs.Star.Parameters) (r : ℝ)
    (positive : 0 < r) (quarter : r ≤ 1 / 4) :
    prefixWeight P r (P.tools+1) ≤ ENNReal.ofReal r := by
  rw [prefixWeight_succ]
  have lastTarget : stageTarget P r P.tools = P.countBudgetReal r P.tools := by
    simp only [stageTarget, Nat.sub_self, countTargetReal, ↓reduceIte]
  rw [lastTarget]
  exact prefixWeight_mul_budget_le P r positive quarter P.tools

end PaperProofs.Star.PStarCountProbability019
