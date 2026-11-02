module

public import PaperProofs.Paid.PDROC_OverlayScalar_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDROC

/-- D13's local estimates bound both actual overlay increments, in ENNReal.
No subtraction of expected bills or assumption of finite expectations is used. -/
theorem overlayIncrement_le_of_overlayLocalClaims (P : PaperProofs.Paid.Parameters)
    (h : P.OverlayLocalClaims) (fee : ℚ) (hfee : 0 ≤ fee) :
    P.overlayObservationIncrement fee + P.overlayCorrectionAmount fee ≤
      (17 / 2 : ℝ≥0∞) * P.feeScale fee := by
  have hl : 0 ≤ Real.log (1 + (fee : ℝ) / P.a) := by
    apply Real.log_nonneg
    have hf : 0 ≤ (fee : ℝ) := by exact_mod_cast hfee
    linarith [div_nonneg hf P.a_pos.le]
  have hbounds := h fee hfee
  have ha := P.a_pos.le
  unfold PaperProofs.Paid.Parameters.overlayObservationIncrement PaperProofs.Paid.Parameters.overlayCorrectionAmount
  calc
    (P.certificate.stages : ℝ≥0∞) * P.binarySymmetric.rocPrice (P.overlayError fee) +
        (P.certificate.stages : ℝ≥0∞) * ENNReal.ofReal ((fee : ℝ) * P.overlayError fee) ≤
        (P.certificate.stages : ℝ≥0∞) * ENNReal.ofReal (8 * P.a * Real.log (1 + (fee : ℝ) / P.a)) +
          (P.certificate.stages : ℝ≥0∞) * ENNReal.ofReal (P.a / 2 * Real.log (1 + (fee : ℝ) / P.a)) :=
      add_le_add (mul_le_mul_right hbounds.2 _)
        (mul_le_mul_right (ENNReal.ofReal_le_ofReal hbounds.1) _)
    _ = (17 / 2 : ℝ≥0∞) * P.feeScale fee := by
      rw [← mul_add, ← ENNReal.ofReal_add (by positivity) (by positivity)]
      rw [show (P.certificate.stages : ℝ≥0∞) = ENNReal.ofReal (P.certificate.stages : ℝ) by simp]
      rw [← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
      rw [show (17 / 2 : ℝ≥0∞) = ENNReal.ofReal (17 / 2 : ℝ) by
        rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]; norm_num]
      unfold PaperProofs.Paid.Parameters.feeScale PaperProofs.Paid.Parameters.feeScaleReal
      rw [← ENNReal.ofReal_mul (by norm_num)]
      congr 1
      ring

end PDROC
