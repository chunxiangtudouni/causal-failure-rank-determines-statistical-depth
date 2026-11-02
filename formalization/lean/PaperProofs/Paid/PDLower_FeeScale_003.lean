module

public import PaperProofs.Paid.PDLower_FeeScale_002
public import Mathlib.Analysis.Convex.SpecificFunctions.Basic

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Statistics.BinarySymmetric

namespace PDLower

theorem fee_scalar {u q d p : ℝ} (hu : 0 ≤ u) (hq : 0 ≤ q)
    (hd : 0 < d) (hdsmall : d ≤ 1 / 63)
    (hp : 0 < p) (hph : p ≤ 1 / 2) (hpqd : p ≤ q + d) :
    Real.log (1 + min u (1 / d)) / 16 ≤ phiReal p + u * q := by
  let w := min u (1 / d)
  have hw : 0 ≤ w := le_min hu (one_div_pos.mpr hd).le
  have hwu : w ≤ u := min_le_left _ _
  by_cases hw16 : w ≤ 16
  · exact small_fee_scalar hu hq hdsmall hp hph hpqd hw hwu hw16
  · have hwlarge : 16 ≤ w := (lt_of_not_ge hw16).le
    have hwd : w * d ≤ 1 := by
      have h := mul_le_mul_of_nonneg_right (min_le_right u (1 / d)) hd.le
      simpa only [one_div_mul_cancel hd.ne'] using h
    have hs0 := Real.sqrt_nonneg w
    have hsq := Real.sq_sqrt hw
    have hs4 : 4 ≤ Real.sqrt w := by nlinarith
    exact large_fee_scalar_square hu hq hp hph hpqd hwu hwd hs4 hsq.symm

theorem log_one_add_scale {β v : ℝ} (hβ : 0 ≤ β) (hβ1 : β ≤ 1) (hv : 0 ≤ v) :
    β * Real.log (1 + v) ≤ Real.log (1 + β * v) := by
  have h := strictConcaveOn_log_Ioi.concaveOn.2
    (show (0 : ℝ) < 1 + v by linarith) (show (0 : ℝ) < 1 by norm_num)
    hβ (show 0 ≤ 1 - β by linarith) (show β + (1 - β) = 1 by ring)
  simpa only [smul_eq_mul, Real.log_one, mul_zero, add_zero,
    show β * (1 + v) + (1 - β) * 1 = 1 + β * v by ring] using h

end PDLower
