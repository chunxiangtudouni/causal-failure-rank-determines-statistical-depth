module

public import PaperProofs.Paid.RepresentationClaims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Paid PaperProofs.Statistics.BinarySymmetric

namespace PDROC

/-- The logarithmic inequality used by the actual weighted correction bill;
it includes arbitrarily small nonnegative fees and the zero fee. -/
theorem overlay_ratio_le_log (x : ℝ) (hx : 0 ≤ x) :
    x / (1 + x) ≤ Real.log (1 + x) := by
  have hp : 0 < 1 + x := by linarith
  have h := Real.one_sub_inv_le_log_of_pos hp
  have heq : x / (1 + x) = 1 - (1 + x)⁻¹ := by
    field_simp
    ; ring
  rwa [heq]

theorem overlay_log_double_le (x : ℝ) (hx : 0 ≤ x) :
    Real.log (1 + 2 * x) ≤ 2 * Real.log (1 + x) := by
  have hp : 0 < 1 + 2 * x := by linarith
  calc
    Real.log (1 + 2 * x) ≤ Real.log ((1 + x) ^ 2) :=
      Real.log_le_log hp (by nlinarith [sq_nonneg x])
    _ = 2 * Real.log (1 + x) := by rw [Real.log_pow]; norm_num

theorem overlay_phiReal_le (x : ℝ) (hx : 0 ≤ x) :
    phiReal (1 / (2 * (1 + x))) ≤ 2 * Real.log (1 + x) := by
  have hp : 0 < 1 + x := by linarith
  have hratio : 0 ≤ x / (1 + x) := div_nonneg hx hp.le
  have hratio_one : x / (1 + x) ≤ 1 := (div_le_one hp).mpr (by linarith)
  have hl : 0 ≤ Real.log (1 + 2 * x) := Real.log_nonneg (by linarith)
  have hform : phiReal (1 / (2 * (1 + x))) =
      x / (1 + x) * Real.log (1 + 2 * x) := by
    unfold phiReal
    have h1 : 1 - 2 * (1 / (2 * (1 + x))) = x / (1 + x) := by
      field_simp
      ; ring
    have h2 : (1 - 1 / (2 * (1 + x))) / (1 / (2 * (1 + x))) = 1 + 2 * x := by
      field_simp
      ; ring
    rw [h1, h2]
  rw [hform]
  exact (mul_le_of_le_one_left hl hratio_one).trans (overlay_log_double_le x hx)

theorem overlay_h_le_two (P : PaperProofs.Paid.Parameters) : P.h ≤ 2 := by
  have hg : (P.certificate.odds : ℝ) ≤ 3 := by
    have hden := P.certificate.denominator_pos
    have hle : P.certificate.odds ≤ 3 := by
      unfold PaperProofs.Paid.CertificateInput.odds
      apply (div_le_iff₀ hden).mpr
      linarith [P.certificate.gamma_le_quarter]
    exact_mod_cast hle
  have hp : 0 < (P.certificate.odds : ℝ) := by
    exact_mod_cast zero_lt_one.trans P.certificate.odds_gt_one
  exact (Real.log_le_sub_one_of_pos hp).trans (by linarith)

theorem overlay_weightedCorrection_le (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    (fee : ℝ) * P.overlayError fee ≤ P.a / 2 * Real.log (1 + (fee : ℝ) / P.a) := by
  have hf : 0 ≤ (fee : ℝ) := by exact_mod_cast hfee
  have hx : 0 ≤ (fee : ℝ) / P.a := div_nonneg hf P.a_pos.le
  have heq : (fee : ℝ) * P.overlayError fee = P.a / 2 * ((fee : ℝ) / P.a / (1 + (fee : ℝ) / P.a)) := by
    unfold PaperProofs.Paid.Parameters.overlayError
    field_simp [P.a_pos.ne']
  rw [heq]
  exact mul_le_mul_of_nonneg_left (overlay_ratio_le_log _ hx) (div_nonneg P.a_pos.le (by norm_num))

theorem overlay_linearTerm_le (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    ((P.reviewFee : ℝ) / (P.certificate.gamma : ℝ)) * (1 / 2 - P.overlayError fee) ≤
      2 * P.a * Real.log (1 + (fee : ℝ) / P.a) := by
  have hf : 0 ≤ (fee : ℝ) := by exact_mod_cast hfee
  have hx : 0 ≤ (fee : ℝ) / P.a := div_nonneg hf P.a_pos.le
  have hg : 0 < (P.certificate.gamma : ℝ) := by exact_mod_cast P.certificate.gamma_pos
  have hcoef : (P.reviewFee : ℝ) / (P.certificate.gamma : ℝ) = 2 * P.a * P.h := by
    unfold PaperProofs.Paid.Parameters.a PaperProofs.Paid.Parameters.kappa
    field_simp [hg.ne', P.h_pos.ne']
  have hdiff : 1 / 2 - P.overlayError fee = ((fee : ℝ) / P.a) / (2 * (1 + (fee : ℝ) / P.a)) := by
    unfold PaperProofs.Paid.Parameters.overlayError
    field_simp
    ; ring
  have heq : ((P.reviewFee : ℝ) / (P.certificate.gamma : ℝ)) * (1 / 2 - P.overlayError fee) =
      P.a * P.h * ((fee : ℝ) / P.a / (1 + (fee : ℝ) / P.a)) := by
    rw [hcoef, hdiff]
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  rw [heq]
  have hlog : 0 ≤ Real.log (1 + (fee : ℝ) / P.a) := Real.log_nonneg (by linarith)
  calc
    P.a * P.h * ((fee : ℝ) / P.a / (1 + (fee : ℝ) / P.a)) ≤
        P.a * P.h * Real.log (1 + (fee : ℝ) / P.a) :=
      mul_le_mul_of_nonneg_left (overlay_ratio_le_log _ hx) (mul_nonneg P.a_pos.le P.h_pos.le)
    _ ≤ 2 * P.a * Real.log (1 + (fee : ℝ) / P.a) := by
      nlinarith [mul_nonneg P.a_pos.le hlog, overlay_h_le_two P]

theorem overlayLocalClaims_of_uniformLocalSurrogate (P : PaperProofs.Paid.Parameters)
    (h : P.UniformLocalSurrogate) : P.OverlayLocalClaims := by
  intro fee hfee
  constructor
  · exact overlay_weightedCorrection_le P fee hfee
  · have hp := P.overlayError_pos fee hfee
    have hhalf := P.overlayError_le_half fee hfee
    have hf : 0 ≤ (fee : ℝ) := by exact_mod_cast hfee
    have hx : 0 ≤ (fee : ℝ) / P.a := div_nonneg hf P.a_pos.le
    have hphi : P.a * phiReal (P.overlayError fee) ≤
        2 * P.a * Real.log (1 + (fee : ℝ) / P.a) := by
      have hbase := overlay_phiReal_le _ hx
      change phiReal (P.overlayError fee) ≤ _ at hbase
      nlinarith [mul_le_mul_of_nonneg_left hbase P.a_pos.le]
    have hlin := overlay_linearTerm_le P fee hfee
    have hsur : P.rocSurrogate (P.overlayError fee) ≤
        ENNReal.ofReal (2 * P.a * Real.log (1 + (fee : ℝ) / P.a)) := by
      unfold PaperProofs.Paid.Parameters.rocSurrogate
      rw [phi_of_pos hp, ← ENNReal.ofReal_mul P.a_pos.le]
      refine max_le (ENNReal.ofReal_le_ofReal hphi) ?_
      rw [← ENNReal.ofReal_mul (div_nonneg (by exact_mod_cast P.reviewFee_pos.le) (by exact_mod_cast P.certificate.gamma_pos.le))]
      exact ENNReal.ofReal_le_ofReal hlin
    calc
      P.binarySymmetric.rocPrice (P.overlayError fee) ≤ 4 * P.rocSurrogate (P.overlayError fee) := (h.1 _ hp hhalf).2
      _ ≤ 4 * ENNReal.ofReal (2 * P.a * Real.log (1 + (fee : ℝ) / P.a)) := by gcongr
      _ = ENNReal.ofReal (8 * P.a * Real.log (1 + (fee : ℝ) / P.a)) := by
        rw [show (4 : ℝ≥0∞) = ENNReal.ofReal 4 by norm_num, ← ENNReal.ofReal_mul (by norm_num)]
        congr 1
        ring

end PDROC

