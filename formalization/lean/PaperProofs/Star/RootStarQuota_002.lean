module

public import PaperProofs.Star.RootStarQuota_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace RootStarQuota

open PaperProofs.Star PaperProofs.Star.Parameters PaperProofs.Common PaperProofs.Common.Native
open PaperProofs.Statistics

theorem badBudget_bounds (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4) :
    r ≤ min (1 / 4) (r / starTargetReal r 1) ∧ min (1 / 4) (r / starTargetReal r 1) ≤ 1 / 4 := by
  have ht := starTarget_pos r 1
  have hquarter := starTarget_le_quarter r 1
  refine ⟨le_min hq ?_, min_le_left _ _⟩
  apply (le_div_iff₀ ht).mpr
  nlinarith

theorem countChosen_bounds (P : Parameters) (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4) (j k : ℕ) :
    r / 5 ≤ countTargetReal (P.countBudgetReal r j) k ∧
      countTargetReal (P.countBudgetReal r j) k ≤ 1 / 2 := by
  have hb := countBudget_bounds P r hr hq j
  have hp := hr.trans_le hb.1
  have ht := countTarget_bounds _ hp hb.2 k
  exact ⟨(div_le_div_of_nonneg_right hb.1 (by norm_num)).trans ht.2.1, ht.2.2.trans (by norm_num)⟩

/-- This bound holds for every visible history, before any run invariant is used. -/
theorem chosenTarget_bounds (P : Parameters) (order : Order) (kind : PortKind)
    (r : ℝ) (hr : 0 < r) (hq : r ≤ 1 / 4)
    (history : List (VisibleEvent (starInstance P.tools order)))
    (stage : (starInstance P.tools order).Stage) (target : ℝ)
    (hc : P.chosenTargetReal order kind r history stage = some target) :
    r / 5 ≤ target ∧ target ≤ 1 / 2 := by
  cases kind with
  | lateRetained =>
    simp only [chosenTargetReal] at hc
    split at hc
    · have he := Option.some.inj hc
      subst target
      exact ⟨by linarith, hq.trans (by norm_num)⟩
    · cases hc
  | earlyRetained =>
    simp only [chosenTargetReal] at hc
    split at hc
    · have he := Option.some.inj hc
      subst target
      exact countChosen_bounds P r hr hq stage.val (P.tools - stage.val)
    · cases hc
  | current =>
    cases order with
    | singletonsFirst =>
      simp only [chosenTargetReal] at hc
      split at hc
      · have he := Option.some.inj hc
        subst target
        exact countChosen_bounds P r hr hq stage.val (P.tools - stage.val)
      · cases hc
    | universalFirst =>
      simp only [chosenTargetReal] at hc
      split at hc
      · have he := Option.some.inj hc
        subst target
        exact ⟨starTarget_floor r hr hq 1, (starTarget_le_quarter r 1).trans (by norm_num)⟩
      · split at hc
        · have he := Option.some.inj hc
          subst target
          have hb := badBudget_bounds r hr hq
          exact ⟨(by linarith : r / 5 ≤ r).trans hb.1, hb.2.trans (by norm_num)⟩
        · cases hc

theorem commonTargetFloor (P : Parameters) : P.CommonTargetFloor := by
  intro order kind C _hcontract accounting delta hd hh limit sample n stage target
  dsimp only
  intro _hlive _hunwritten hchosen
  have hr : 0 < delta / 2 := by linarith
  have hq : delta / 2 ≤ 1 / 4 := by linarith
  have h := chosenTarget_bounds P order kind (delta / 2) hr hq _ stage target hchosen
  simpa only [div_div, show (2 : ℝ) * 5 = 10 by norm_num] using h

theorem commonExponent_le_iff (P : Parameters) (delta : ℚ) (hd : 0 < delta) (exponent : ℕ) :
    P.commonExponentRat delta ≤ exponent ↔
      1 ≤ exponent ∧ DyadicQualifies (20 * (P.tools + 1 : ℕ)) (delta : ℝ) exponent := by
  rw [commonExponentRat, max_le_iff, Nat.clog_le_iff_le_pow (by norm_num), Nat.ceil_le]
  rw [div_le_iff₀ hd]
  constructor
  · rintro ⟨hone, h⟩
    refine ⟨hone, ?_⟩
    change ((20 * (P.tools + 1 : ℕ) : ℚ) : ℝ) ≤ (2 : ℝ) ^ exponent * (delta : ℝ)
    exact_mod_cast h
  · rintro ⟨hone, h⟩
    refine ⟨hone, ?_⟩
    change ((20 * (P.tools + 1 : ℕ) : ℚ) : ℝ) ≤ (2 : ℝ) ^ exponent * (delta : ℝ) at h
    exact_mod_cast h

theorem commonExponent_minimal (P : Parameters) (delta : ℚ) (hd : 0 < delta) :
    IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) (delta : ℝ) (P.commonExponentRat delta) := by
  have h := (commonExponent_le_iff P delta hd (P.commonExponentRat delta)).mp le_rfl
  refine ⟨h.1, h.2, ?_⟩
  intro smaller hpos hsmall hqual
  have he := (commonExponent_le_iff P delta hd smaller).mpr ⟨hpos, hqual⟩
  exact (not_le_of_gt hsmall) he

theorem commonExponent_real_exists (P : Parameters) (delta : ℝ) (hd : 0 < delta) :
    ∃ exponent, IsMinimalDyadicExponent (20 * (P.tools + 1 : ℕ)) delta exponent := by
  classical
  obtain ⟨r, hr, _half, hrle⟩ := exists_rationalRisk_factorTwo delta hd
  have h := commonExponent_minimal P r hr
  have hex : ∃ exponent : ℕ, 1 ≤ exponent ∧ DyadicQualifies (20 * (P.tools + 1 : ℕ)) delta exponent :=
    ⟨P.commonExponentRat r, h.1, dyadicQualifies_mono _ _ hrle h.2.1⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  intro smaller hpos hsmall hqual
  exact Nat.find_min hex hsmall ⟨hpos, hqual⟩

theorem commonQuotaArithmetic (P : Parameters) : P.CommonQuotaArithmetic :=
  ⟨commonExponent_real_exists P, commonExponent_minimal P, fun _exponent => Nat.le_ceil _⟩

theorem c10Claims (P : Parameters) : P.C10Claims :=
  ⟨commonQuotaArithmetic P, commonTargetFloor P⟩

end RootStarQuota
