module

public import PaperProofs.Paid.PDLower_MajorityScale_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid

namespace PDLower

theorem paid_h_eq_symmetricLogOdds (P : PaperProofs.Paid.Parameters) :
    P.h = symmetricLogOdds (P.certificate.gamma : ℝ) := by
  have hg : 0 < (P.certificate.gamma : ℝ) := by exact_mod_cast P.certificate.gamma_pos
  have hgq : (P.certificate.gamma : ℝ) ≤ 1 / 4 := by
    have h := (Rat.cast_le (K := ℝ)).mpr P.certificate.gamma_le_quarter
    norm_num at h
    exact h
  unfold Parameters.h CertificateInput.odds symmetricLogOdds
  push_cast
  exact Real.log_div (by linarith) (by linarith)

theorem paid_kappa_upper (P : PaperProofs.Paid.Parameters) :
    P.kappa ≤ (32 / 3) * (P.certificate.gamma : ℝ) ^ 2 := by
  have hg : 0 < (P.certificate.gamma : ℝ) := by exact_mod_cast P.certificate.gamma_pos
  have hgq : (P.certificate.gamma : ℝ) ≤ 1 / 4 := by
    have h := (Rat.cast_le (K := ℝ)).mpr P.certificate.gamma_le_quarter
    norm_num at h
    exact h
  rw [Parameters.kappa, paid_h_eq_symmetricLogOdds]
  calc
    _ ≤ (2 * (P.certificate.gamma : ℝ)) * ((16 / 3) * (P.certificate.gamma : ℝ)) :=
      mul_le_mul_of_nonneg_left (symmetricLogOdds_upper hg.le hgq) (by positivity)
    _ = _ := by ring

theorem certificate_t0_upper (D : CertificateInput) :
    (D.t0 : ℝ) ≤ Real.log (2 * (D.stages : ℝ) / (D.risk : ℝ)) /
      (2 * (D.gamma : ℝ) ^ 2) + 3 := by
  let g := (D.gamma : ℝ)
  let R := 2 * (D.stages : ℝ) / (D.risk : ℝ)
  have hg : 0 < g := by
    change (0 : ℝ) < (D.gamma : ℝ)
    exact_mod_cast D.gamma_pos
  have hgq : g ≤ 1 / 4 := by
    have h := (Rat.cast_le (K := ℝ)).mpr D.gamma_le_quarter
    norm_num at h
    exact h
  have hd : 0 < (D.risk : ℝ) := by exact_mod_cast D.risk_pos
  have hd64 : (D.risk : ℝ) ≤ 1 / 64 := by
    have h := (Rat.cast_le (K := ℝ)).mpr D.risk_le
    norm_num at h
    exact h
  have hN : (1 : ℝ) ≤ D.stages := by exact_mod_cast (Nat.succ_le_of_lt D.stages_pos)
  have hR : 1 < R := (one_lt_div hd).mpr (by linarith)
  let t := majorityUpperTime g R
  have hpower : (1 - 4 * g ^ 2) ^ t ≤ (R⁻¹) ^ 2 :=
    majority_power_of_time hg hgq hR t (majorityUpperTime_lower g R)
  have hqual : D.MajorityQualifies t := by
    refine ⟨majorityUpperTime_pos g R, majorityUpperTime_odd g R, ?_⟩
    apply (Rat.cast_le (K := ℝ)).mp
    dsimp [CertificateInput.varianceBase]
    push_cast
    simpa only [g, R, inv_div] using hpower
  have ht : (D.t0 : ℝ) ≤ (t : ℝ) := by exact_mod_cast D.t0_min hqual
  exact ht.trans (majorityUpperTime_upper g R hR)

end PDLower
