module

public import PaperProofs.Paid.PDLower_MajorityScale_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid
open scoped ENNReal

namespace PDLower

theorem paid_kappa_t0_le (P : PaperProofs.Paid.Parameters) :
    P.kappa * (P.certificate.t0 : ℝ) ≤
      7 * Real.log (1 + (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ)) := by
  let g := (P.certificate.gamma : ℝ)
  let L := Real.log (2 * (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ))
  let X := Real.log (1 + (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ))
  have hg : 0 < g := by
    change (0 : ℝ) < (P.certificate.gamma : ℝ)
    exact_mod_cast P.certificate.gamma_pos
  have hgq : g ≤ 1 / 4 := by
    have h := (Rat.cast_le (K := ℝ)).mpr P.certificate.gamma_le_quarter
    norm_num at h
    exact h
  have hsq : g ^ 2 ≤ 1 / 16 := by nlinarith [mul_self_le_mul_self hg.le hgq]
  have hN : (1 : ℝ) ≤ P.certificate.stages := by exact_mod_cast (Nat.succ_le_of_lt P.certificate.stages_pos)
  have hN0 : (0 : ℝ) < P.certificate.stages := by linarith
  have hd : 0 < (P.certificate.risk : ℝ) := by exact_mod_cast P.certificate.risk_pos
  have hd64 : (P.certificate.risk : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr P.certificate.risk_le
    norm_num at h
    exact h
  have ht := certificate_t0_upper P.certificate
  have hk := paid_kappa_upper P
  have hprod : P.kappa * (P.certificate.t0 : ℝ) ≤ (16 / 3) * L + 32 * g ^ 2 := by
    calc
      _ ≤ ((32 / 3) * g ^ 2) * (P.certificate.t0 : ℝ) :=
        mul_le_mul_of_nonneg_right hk (Nat.cast_nonneg _)
      _ ≤ ((32 / 3) * g ^ 2) * (L / (2 * g ^ 2) + 3) :=
        mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by
        field_simp [hg.ne']
        ring
  have hL : L ≤ Real.log 2 + X := by
    have hr : (0 : ℝ) < (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ) := div_pos hN0 hd
    have heq : 2 * (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ) =
        2 * ((P.certificate.stages : ℝ) / (P.certificate.risk : ℝ)) := by ring
    dsimp [L, X]
    rw [heq, Real.log_mul (by norm_num) hr.ne']
    have hlog : Real.log ((P.certificate.stages : ℝ) / (P.certificate.risk : ℝ)) ≤
        Real.log (1 + (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ)) :=
      Real.log_le_log hr (by linarith)
    exact add_le_add le_rfl hlog
  have hX : (37 / 10 : ℝ) ≤ X := saturationLog_lower hN hd hd64
  nlinarith only [hprod, hL, hX, hsq, log_two_upper]

theorem majorityBill_le_saturation (P : PaperProofs.Paid.Parameters) :
    ENNReal.ofReal (P.B : ℝ) ≤ 7 * P.saturationScale := by
  have hc : (0 : ℝ) < P.reviewFee := by exact_mod_cast P.reviewFee_pos
  have hN : (0 : ℝ) < P.certificate.stages := by exact_mod_cast P.certificate.stages_pos
  have hk := paid_kappa_t0_le P
  have hreal : (P.B : ℝ) ≤ 7 * P.saturationScaleReal := by
    calc
      _ = ((P.reviewFee : ℝ) * P.certificate.stages / P.kappa) *
          (P.kappa * (P.certificate.t0 : ℝ)) := by
        unfold Parameters.B
        push_cast
        field_simp [P.kappa_pos.ne']
      _ ≤ ((P.reviewFee : ℝ) * P.certificate.stages / P.kappa) *
          (7 * Real.log (1 + (P.certificate.stages : ℝ) / (P.certificate.risk : ℝ))) :=
        mul_le_mul_of_nonneg_left hk (div_nonneg (mul_nonneg hc.le hN.le) P.kappa_pos.le)
      _ = _ := by unfold Parameters.saturationScaleReal Parameters.a; ring
  calc
    _ ≤ ENNReal.ofReal (7 * P.saturationScaleReal) := ENNReal.ofReal_le_ofReal hreal
    _ = _ := by
      rw [ENNReal.ofReal_mul (by norm_num)]
      norm_num [Parameters.saturationScale]

end PDLower
