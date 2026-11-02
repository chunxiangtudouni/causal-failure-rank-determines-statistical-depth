module

public import PaperProofs.Paid.PDLower_Majority_004
public import PaperProofs.Paid.BSCAdapter

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PDLower

theorem paid_majority_t0_tail (P : PaperProofs.Paid.Parameters) (x : Bool) :
    P.experiment.tapeLaw x
      {tape | decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore
        (List.ofFn (fun i : Fin P.certificate.t0 => (tape i.val).val))) ≠ x} ≤
      ENNReal.ofReal (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ) := by
  have htargetRat : (0 : ℚ) ≤ P.certificate.risk / (2 * (P.certificate.stages : ℚ)) :=
    div_nonneg P.certificate.risk_pos.le (mul_nonneg (by norm_num) (Nat.cast_nonneg _))
  have htarget : (0 : ℝ) ≤ (((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ) := by
    simpa only [Rat.cast_zero] using (Rat.cast_le (K := ℝ)).mpr htargetRat
  have hvariance : (1 - 4 * (P.binarySymmetric.gamma : ℝ) ^ 2) ^ P.certificate.t0 ≤
      ((((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ)) ^ 2 := by
    have h := (Rat.cast_le (K := ℝ)).mpr P.certificate.t0_spec.2.2
    change (1 - 4 * (P.certificate.gamma : ℝ) ^ 2) ^ P.certificate.t0 ≤ _
    simpa only [PaperProofs.Paid.CertificateInput.varianceBase, Rat.cast_pow, Rat.cast_sub,
      Rat.cast_one, Rat.cast_mul, Rat.cast_ofNat] using h
  exact majority_tail_of_variance P.binarySymmetric P.certificate.t0 x
    ((((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) : ℚ) : ℝ)) htarget hvariance

end PDLower
