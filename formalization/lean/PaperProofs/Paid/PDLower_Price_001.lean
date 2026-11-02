module

public import PaperProofs.Paid.PDLower_FeeScale_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDLower

theorem min_add_price_bound (A D S V : ℝ≥0∞) (hA : A ≤ V)
    (hD : min D S ≤ 128 * V) : min (A + D) S / 129 ≤ V := by
  apply (ENNReal.div_le_iff (by norm_num) (by norm_num)).mpr
  calc
    min (A + D) S ≤ min (A + D) (A + S) := min_le_min le_rfl le_add_self
    _ = A + min D S := (add_min _ _ _).symm
    _ ≤ V + 128 * V := add_le_add hA hD
    _ = V * 129 := by ring

theorem feeScale_min_eq_lower (P : Parameters) (fee : ℚ) (hf : 0 ≤ fee) :
    min (P.feeScale fee) P.saturationScale = 128 * P.feeScaleLowerAmount fee := by
  have hfee : (0 : ℝ) ≤ fee := by exact_mod_cast hf
  have hd : 0 < (P.certificate.risk : ℝ) := by exact_mod_cast P.certificate.risk_pos
  let u := (fee : ℝ) / P.a
  let z := (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ)
  have hu : 0 ≤ u := div_nonneg hfee P.a_pos.le
  have hz : 0 ≤ z := div_nonneg (Nat.cast_nonneg _) hd.le
  have hscale : (0 : ℝ) ≤ P.a * P.certificate.stages := mul_nonneg P.a_pos.le (Nat.cast_nonneg _)
  have hexpand : 128 * P.feeScaleLowerAmount fee =
      ENNReal.ofReal ((P.a * P.certificate.stages) * Real.log (1 + min u z)) := by
    change (128 : ℝ≥0∞) * ENNReal.ofReal _ = _
    rw [show (128 : ℝ≥0∞) = ENNReal.ofReal (128 : ℝ) by norm_num,
      ← ENNReal.ofReal_mul (by norm_num)]
    congr 1
    ring
  rw [hexpand]
  rcases le_total u z with h | h
  · have hl : Real.log (1 + u) ≤ Real.log (1 + z) := Real.log_le_log (by linarith) (by linarith)
    have hs : P.feeScale fee ≤ P.saturationScale := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hl hscale
    rw [min_eq_left hs]
    change ENNReal.ofReal ((P.a * P.certificate.stages) * Real.log (1 + u)) = _
    rw [min_eq_left h]
  · have hl : Real.log (1 + z) ≤ Real.log (1 + u) := Real.log_le_log (by linarith) (by linarith)
    have hs : P.saturationScale ≤ P.feeScale fee := by
      apply ENNReal.ofReal_le_ofReal
      exact mul_le_mul_of_nonneg_left hl hscale
    rw [min_eq_right hs]
    change ENNReal.ofReal ((P.a * P.certificate.stages) * Real.log (1 + z)) = _
    rw [min_eq_right h]

theorem separationLower (P : Parameters) (C : P.PaymentContract) (mode : ResourceMode)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.separationScale C mode accounting fee / 129 ≤ P.paidValue C mode accounting fee hf := by
  apply min_add_price_bound
  · exact P.freeValue_le_paidValue C mode accounting fee hf
  · rw [feeScale_min_eq_lower P fee hf]
    exact mul_le_mul' le_rfl (uniformFeeScaleValueLower P C accounting fee hf mode)

theorem nativeSeparationLower (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.NativeSeparationLower C accounting fee hf :=
  separationLower P C .native accounting fee hf

end PDLower
