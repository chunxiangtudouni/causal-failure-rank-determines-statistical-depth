module

public import PaperProofs.Paid.PDLower_Cost_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Statistics.BinarySymmetric

namespace PDLower

theorem phiReal_quarter : phiReal (1 / 4) = (1 / 2) * Real.log 3 := by
  norm_num [phiReal]

theorem phiReal_ge_quarter {p : ℝ} (hp : 0 < p) (hpq : p ≤ 1 / 4) :
    (1 / 2) * Real.log 3 ≤ phiReal p := by
  rw [← phiReal_quarter]
  exact phiReal_strictAntiOn.antitoneOn ⟨hp, by linarith⟩ (by norm_num) hpq

theorem log_seventeen_le : Real.log 17 ≤ 4 * Real.log 3 := by
  have h : Real.log 17 ≤ Real.log ((3 : ℝ) ^ 4) :=
    Real.log_le_log (by norm_num) (by norm_num)
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem small_fee_scalar {u q d p w : ℝ}
    (hu : 0 ≤ u) (hq : 0 ≤ q) (hd : d ≤ 1 / 63)
    (hp : 0 < p) (hph : p ≤ 1 / 2) (hpqd : p ≤ q + d)
    (hw : 0 ≤ w) (hwu : w ≤ u) (hw16 : w ≤ 16) :
    Real.log (1 + w) / 16 ≤ phiReal p + u * q := by
  have hφ := phiReal_nonneg hp hph
  have huq : 0 ≤ u * q := mul_nonneg hu hq
  by_cases hpq : p ≤ 1 / 4
  · have hφq := phiReal_ge_quarter hp hpq
    have hl : Real.log (1 + w) ≤ 4 * Real.log 3 :=
      (Real.log_le_log (by linarith) (by linarith)).trans log_seventeen_le
    have hlog3 : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
    linarith
  · have hqf : 1 / 5 ≤ q := by linarith
    have huw : w * (1 / 5) ≤ u * q := mul_le_mul hwu hqf (by norm_num) hu
    have hl : Real.log (1 + w) ≤ w := by
      have h := Real.log_le_sub_one_of_pos (show 0 < 1 + w by linarith)
      linarith
    linarith

end PDLower
