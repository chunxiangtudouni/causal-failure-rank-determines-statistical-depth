module

public import PaperProofs.Star.Claims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootStarQuota

open PaperProofs.Star PaperProofs.Star.Parameters PaperProofs.Statistics

theorem clog_ceil_real (x : ℝ) (hx : 0 < x) :
    Nat.clog 2 ⌈x⌉₊ = ⌈Real.logb 2 x⌉₊ := by
  apply eq_of_forall_ge_iff
  intro n
  rw [Nat.clog_le_iff_le_pow (by norm_num), Nat.ceil_le, Nat.ceil_le,
    Real.logb_le_iff_le_rpow (by norm_num) hx, Real.rpow_natCast]
  constructor <;> intro h <;> exact_mod_cast h

theorem analytic_initial_bounds (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4) :
    2 ≤ analyticControllerB (1 / r) 1 ∧ (analyticControllerB (1 / r) 1 : ℝ) ≤ 1 / r := by
  have hx : 0 < 1 / r := one_div_pos.mpr hr
  have hinv : (4 : ℝ) ≤ 1 / r := (le_div_iff₀ hr).mpr (by linarith)
  have hceil : 4 ≤ ⌈1 / r⌉₊ := by exact_mod_cast (hinv.trans (Nat.le_ceil (1 / r)))
  have hlo : 2 ≤ Nat.clog 2 ⌈1 / r⌉₊ := by
    have h : 1 < Nat.clog 2 ⌈1 / r⌉₊ :=
      (Nat.lt_clog_iff_pow_lt (by norm_num)).mpr (by simpa using (show 2 < ⌈1 / r⌉₊ by omega))
    omega
  have hone : 1 ≤ ⌈1 / r⌉₊ := by omega
  have hpow : ⌈1 / r⌉₊ ≤ 2 ^ (⌈1 / r⌉₊ - 1) := by
    have h := Nat.lt_pow_self (n := ⌈1 / r⌉₊ - 1) (show 1 < 2 by norm_num)
    omega
  have hclog := (Nat.clog_le_iff_le_pow (by norm_num)).mpr hpow
  have hcast : (Nat.clog 2 ⌈1 / r⌉₊ : ℝ) ≤ (⌈1 / r⌉₊ : ℝ) - 1 := by
    simpa only [Nat.cast_sub hone, Nat.cast_one] using
      (show (Nat.clog 2 ⌈1 / r⌉₊ : ℝ) ≤ (⌈1 / r⌉₊ - 1 : ℕ) by exact_mod_cast hclog)
  have hceil_lt := Nat.ceil_lt_add_one hx.le
  rw [analyticControllerB_one, ← clog_ceil_real _ hx]
  exact ⟨hlo, by linarith⟩

theorem analytic_bound (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4) (j : ℕ) (hj : 1 ≤ j) :
    (analyticControllerB (1 / r) j : ℝ) ≤ 1 / r := by
  have hi := analytic_initial_bounds r hr hq
  have hb := thresholdSequence_bounds (analyticControllerB (1 / r) 1) hi.1 j hj
  have he : thresholdSequence (analyticControllerB (1 / r) 1) j = analyticControllerB (1 / r) j := rfl
  rw [he] at hb
  exact (by exact_mod_cast hb.2 : (analyticControllerB (1 / r) j : ℝ) ≤
    (analyticControllerB (1 / r) 1 : ℝ)).trans hi.2

theorem starTarget_pos (r : ℝ) (j : ℕ) : 0 < starTargetReal r j := by
  unfold starTargetReal
  positivity

theorem starTarget_le_quarter (r : ℝ) (j : ℕ) : starTargetReal r j ≤ 1 / 4 := by
  unfold starTargetReal
  apply one_div_le_one_div_of_le (by norm_num)
  have h : (0 : ℝ) ≤ analyticControllerB (1 / r) j := Nat.cast_nonneg _
  linarith

theorem starTarget_floor (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4) (j : ℕ) :
    r / 5 ≤ starTargetReal r j := by
  cases j with
  | zero => simp only [starTargetReal, analyticControllerB, thresholdSequence]; norm_num; linarith
  | succ j =>
    have hb := analytic_bound r hr hq (j + 1) (by omega)
    have hm := mul_le_mul_of_nonneg_left hb hr.le
    rw [mul_one_div_cancel hr.ne'] at hm
    unfold starTargetReal
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 4 * (1 + analyticControllerB (1 / r) (j + 1)))).mpr
    nlinarith

theorem countTarget_bounds (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4) (k : ℕ) :
    0 < countTargetReal r k ∧ r / 5 ≤ countTargetReal r k ∧ countTargetReal r k ≤ 1 / 4 := by
  by_cases hk : k = 0
  · simp only [countTargetReal, hk, ↓reduceIte]
    exact ⟨hr, by linarith, hq⟩
  · simp only [countTargetReal, hk, ↓reduceIte]
    exact ⟨starTarget_pos r k, starTarget_floor r hr hq k, starTarget_le_quarter r k⟩

theorem countBudget_bounds (P : Parameters) (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4) (j : ℕ) :
    r ≤ P.countBudgetReal r j ∧ P.countBudgetReal r j ≤ 1 / 4 := by
  induction j with
  | zero => exact ⟨le_rfl, hq⟩
  | succ j ih =>
    have hp : 0 < P.countBudgetReal r j := hr.trans_le ih.1
    obtain ⟨ht, _, hquarter⟩ := countTarget_bounds _ hp ih.2 (P.tools - j)
    have hdiv : P.countBudgetReal r j ≤
        P.countBudgetReal r j / countTargetReal (P.countBudgetReal r j) (P.tools - j) := by
      apply (le_div_iff₀ ht).mpr
      nlinarith
    exact ⟨le_min hq (ih.1.trans hdiv), min_le_left _ _⟩

end RootStarQuota
