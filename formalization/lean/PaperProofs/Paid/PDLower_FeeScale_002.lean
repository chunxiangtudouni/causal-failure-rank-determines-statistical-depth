module

public import PaperProofs.Paid.PDLower_FeeScale_001
public import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Statistics.BinarySymmetric

namespace PDLower

theorem log_one_add_le_twice {w : ℝ} (hw : 16 ≤ w) :
    Real.log (1 + w) ≤ 2 * Real.log w := by
  have hsq : 1 + w ≤ w ^ 2 := by nlinarith [sq_nonneg (w - 1)]
  have h := Real.log_le_log (show 0 < 1 + w by linarith) hsq
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem large_fee_scalar_square {u q d p w s : ℝ}
    (hu : 0 ≤ u) (hq : 0 ≤ q) (hp : 0 < p) (hph : p ≤ 1 / 2)
    (hpqd : p ≤ q + d) (hwu : w ≤ u) (hwd : w * d ≤ 1)
    (hs : 4 ≤ s) (hws : w = s ^ 2) :
    Real.log (1 + w) / 16 ≤ phiReal p + u * q := by
  have hs0 : 0 < s := by linarith
  have hw16 : 16 ≤ w := by rw [hws]; nlinarith
  have hlogw : Real.log w = 2 * Real.log s := by rw [hws, Real.log_pow]; norm_num
  have hlogBound : Real.log (1 + w) ≤ 4 * Real.log s := by
    have h := log_one_add_le_twice hw16
    rw [hlogw] at h
    linarith
  have hφ := phiReal_nonneg hp hph
  have huq := mul_nonneg hu hq
  by_cases hps : p ≤ 1 / s
  · have hsp : s * p ≤ 1 := by
      have h := (le_div_iff₀ hs0).mp hps
      nlinarith
    have hpq : p ≤ 1 / 4 :=
      hps.trans (one_div_le_one_div_of_le (by norm_num) hs)
    have hodds : s / 2 ≤ (1 - p) / p := (le_div_iff₀ hp).mpr (by nlinarith)
    have hlogOdds : Real.log (s / 2) ≤ Real.log ((1 - p) / p) :=
      Real.log_le_log (div_pos hs0 (by norm_num)) hodds
    rw [Real.log_div hs0.ne' (by norm_num)] at hlogOdds
    have hlogs : 2 * Real.log 2 ≤ Real.log s := by
      have h := Real.log_le_log (show (0 : ℝ) < 2 ^ 2 by norm_num) (show (2 : ℝ) ^ 2 ≤ s by norm_num; exact hs)
      simpa only [Real.log_pow, Nat.cast_ofNat] using h
    have hl0 : 0 ≤ Real.log ((1 - p) / p) :=
      Real.log_nonneg ((le_div_iff₀ hp).mpr (by linarith))
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hphiOdds : (1 / 2) * Real.log ((1 - p) / p) ≤
        (1 - 2 * p) * Real.log ((1 - p) / p) :=
      mul_le_mul_of_nonneg_right (by linarith) hl0
    unfold phiReal
    nlinarith
  · have hsp : 1 < s * p := by
      have h := (div_lt_iff₀ hs0).mp (lt_of_not_ge hps)
      nlinarith
    have hqLower : s - 1 ≤ w * q := by
      have hw0 : 0 ≤ w := by rw [hws]; positivity
      have hpMul := mul_le_mul_of_nonneg_left hpqd hw0
      have hprod : s ≤ w * p := by
        rw [hws]
        have hmul := mul_le_mul_of_nonneg_left hsp.le hs0.le
        nlinarith
      nlinarith
    have huLower : w * q ≤ u * q := mul_le_mul_of_nonneg_right hwu hq
    have hlogs : Real.log s ≤ s - 1 := Real.log_le_sub_one_of_pos hs0
    linarith

end PDLower
