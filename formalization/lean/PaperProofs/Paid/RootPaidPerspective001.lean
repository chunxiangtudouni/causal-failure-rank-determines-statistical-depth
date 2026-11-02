module

public import PaperProofs.Statistics.BSCInformation

@[expose] public section

namespace RootPaidPerspective

open PaperProofs.Statistics.BinarySymmetric
open scoped ENNReal

noncomputable def realValue (mass error : ℝ) : ℝ :=
  mass * phiReal (min (1 / 2) (error / mass))

noncomputable def value (mass error : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal mass * phi (min (1 / 2) (error / mass))

theorem realValue_eq_zero_of_half_le {mass error : ℝ} (hh : 1 / 2 ≤ error / mass) :
    realValue mass error = 0 := by
  simp only [realValue, min_eq_left hh, phiReal_half, mul_zero]

theorem value_eq_zero_of_half_le {mass error : ℝ} (hh : 1 / 2 ≤ error / mass) :
    value mass error = 0 := by
  simp only [value, min_eq_left hh, phi_half, mul_zero]

theorem value_eq_ofReal {mass error : ℝ} (hm : 0 < mass) (he : 0 < error) :
    value mass error = ENNReal.ofReal (realValue mass error) := by
  rw [value, phi_of_pos (lt_min (by norm_num) (div_pos he hm)), ← ENNReal.ofReal_mul hm.le]
  rfl

theorem realValue_nonneg {mass error : ℝ} (hm : 0 < mass) (he : 0 < error) :
    0 ≤ realValue mass error :=
  mul_nonneg hm.le (phiReal_nonneg (lt_min (by norm_num) (div_pos he hm)) (min_le_left _ _))

theorem realValue_error_antitone {mass x y : ℝ} (hm : 0 < mass) (hx : 0 < x) (hxy : x ≤ y) :
    realValue mass y ≤ realValue mass x := by
  have hy : 0 < y := hx.trans_le hxy
  apply mul_le_mul_of_nonneg_left _ hm.le
  exact phiReal_strictAntiOn.antitoneOn
    ⟨lt_min (by norm_num) (div_pos hx hm), min_le_left _ _⟩
    ⟨lt_min (by norm_num) (div_pos hy hm), min_le_left _ _⟩
    (min_le_min_left _ (div_le_div_of_nonneg_right hxy hm.le))

theorem realValue_mass_monotone {m M x : ℝ} (hm : 0 < m) (hmM : m ≤ M) (hx : 0 < x) :
    realValue m x ≤ realValue M x := by
  have hM : 0 < M := hm.trans_le hmM
  have hphi := phiReal_strictAntiOn.antitoneOn
    ⟨lt_min (by norm_num) (div_pos hx hM), min_le_left _ _⟩
    ⟨lt_min (by norm_num) (div_pos hx hm), min_le_left _ _⟩
    (min_le_min_left _ (div_le_div_of_nonneg_left hx.le hm hmM))
  exact (mul_le_mul_of_nonneg_right hmM
    (phiReal_nonneg (lt_min (by norm_num) (div_pos hx hm)) (min_le_left _ _))).trans
      (mul_le_mul_of_nonneg_left hphi hM.le)

theorem value_error_antitone {mass x y : ℝ} (hm : 0 < mass) (hx : 0 < x) (hxy : x ≤ y) :
    value mass y ≤ value mass x := by
  rw [value_eq_ofReal hm (hx.trans_le hxy), value_eq_ofReal hm hx]
  exact ENNReal.ofReal_le_ofReal (realValue_error_antitone hm hx hxy)

theorem value_mass_monotone {m M x : ℝ} (hm : 0 < m) (hmM : m ≤ M) (hx : 0 < x) :
    value m x ≤ value M x := by
  rw [value_eq_ofReal hm hx, value_eq_ofReal (hm.trans_le hmM) hx]
  exact ENNReal.ofReal_le_ofReal (realValue_mass_monotone hm hmM hx)

theorem phiDerivative_neg {q : ℝ} (hq : 0 < q) (hh : q < 1 / 2) : phiDerivative q < 0 := by
  have hl : 0 < Real.log ((1 - q) / q) := Real.log_pos ((one_lt_div hq).mpr (by linarith))
  have hd : 0 < (1 - 2 * q) / (q * (1 - q)) := div_pos (by linarith) (mul_pos hq (by linarith))
  unfold phiDerivative
  linarith

theorem perspective_derivative_positive {q : ℝ} (hq : 0 < q) (hh : q < 1 / 2) :
    0 < phiReal q - q * phiDerivative q := by
  have hn := phiReal_nonneg hq hh.le
  have hp := mul_pos hq (neg_pos.mpr (phiDerivative_neg hq hh))
  nlinarith

theorem hasDerivAt_unclamped {mass error : ℝ} (hm : 0 < mass) (he : 0 < error)
    (hh : error / mass < 1 / 2) :
    HasDerivAt (fun m : ℝ => m * phiReal (error / m))
      (phiReal (error / mass) - (error / mass) * phiDerivative (error / mass)) mass := by
  have hdiv := (hasDerivAt_const mass error).div (hasDerivAt_id mass) hm.ne'
  have hphi := (hasDerivAt_phiReal (div_pos he hm) (by linarith)).comp mass hdiv
  have hprod := (hasDerivAt_id mass).mul hphi
  change HasDerivAt (fun m : ℝ => m * phiReal (error / m))
    (1 * phiReal (error / mass) + mass * (phiDerivative (error / mass) *
      ((0 * mass - error * 1) / mass ^ 2))) mass at hprod
  convert hprod using 1
  field_simp [hm.ne']
  ring

theorem realValue_hasDerivAt {mass error : ℝ} (hm : 0 < mass) (he : 0 < error)
    (hh : error / mass < 1 / 2) :
    HasDerivAt (fun m : ℝ => realValue m error)
      (phiReal (error / mass) - (error / mass) * phiDerivative (error / mass)) mass := by
  have ht : ∀ᶠ m in nhds mass, error / m < 1 / 2 :=
    (continuousAt_const.div continuousAt_id hm.ne').eventually_lt continuousAt_const hh
  exact (hasDerivAt_unclamped hm he hh).congr_of_eventuallyEq
    (ht.mono fun m h => congrArg (fun q => m * phiReal q) (min_eq_right h.le))

end RootPaidPerspective
