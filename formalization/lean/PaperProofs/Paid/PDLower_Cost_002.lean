module

public import PaperProofs.Paid.PDLower_Cost_001
public import PaperProofs.Statistics.BSCInformation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid PaperProofs.Statistics
open PaperProofs.Statistics.BinarySymmetric

namespace PDLower

theorem phiDerivative_nonpos {z : ℝ} (hz : 0 < z) (hh : z ≤ 1 / 2) :
    phiDerivative z ≤ 0 := by
  have hl : 0 ≤ Real.log ((1 - z) / z) :=
    Real.log_nonneg ((le_div_iff₀ hz).mpr (by linarith))
  have hd : 0 ≤ (1 - 2 * z) / (z * (1 - z)) :=
    div_nonneg (by linarith) (mul_nonneg hz.le (by linarith))
  unfold phiDerivative
  linarith

theorem phiReal_support {z p : ℝ} (hz : 0 < z) (hzh : z ≤ 1 / 2)
    (hp : 0 < p) (hph : p ≤ 1 / 2) :
    phiReal z + (-phiDerivative z) * z ≤ phiReal p + (-phiDerivative z) * p := by
  have hd := hasDerivAt_phiReal hz (by linarith)
  rcases lt_trichotomy z p with hlt | heq | hgt
  · have hs := phiReal_convexOn.le_slope_of_hasDerivAt ⟨hz, hzh⟩ ⟨hp, hph⟩ hlt hd
    rw [slope_def_field] at hs
    have hm := (le_div_iff₀ (sub_pos.mpr hlt)).mp hs
    nlinarith
  · subst p
    exact le_rfl
  · have hs := phiReal_convexOn.slope_le_of_hasDerivAt ⟨hp, hph⟩ ⟨hz, hzh⟩ hgt hd
    rw [slope_def_field] at hs
    have hm := (div_le_iff₀ (sub_pos.mpr hgt)).mp hs
    nlinarith

theorem phi_support {z p : ℝ} (hz : 0 < z) (hzh : z ≤ 1 / 2)
    (hp : 0 ≤ p) (hph : p ≤ 1 / 2) :
    ENNReal.ofReal (phiReal z + (-phiDerivative z) * z) ≤
      phi p + ENNReal.ofReal (-phiDerivative z) * ENNReal.ofReal p := by
  by_cases hpzero : p = 0
  · simp [hpzero]
  · have hp' : 0 < p := lt_of_le_of_ne hp (Ne.symm hpzero)
    rw [phi_of_pos hp', ← ENNReal.ofReal_mul (neg_nonneg.mpr (phiDerivative_nonpos hz hzh)),
      ← ENNReal.ofReal_add (phiReal_nonneg hp' hph) (mul_nonneg (neg_nonneg.mpr (phiDerivative_nonpos hz hzh)) hp)]
    exact ENNReal.ofReal_le_ofReal (phiReal_support hz hzh hp' hph)

end PDLower
