module

public import PaperProofs.Paid.PDROC_DataBits_Mixture_001
public import PaperProofs.Paid.PDROC_DataBits_Gap_001
public import PaperProofs.Paid.PDLower_MajorityScale_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

/-- Auxiliary input magnitude, keeping every original certificate counter
and the original frontend numericalSize unchanged. -/
def dataInputSize (D : CertificateInput) : ℕ :=
  D.stages + ratEncodingBits D.gamma + ratEncodingBits D.risk + ⌈D.gamma⁻¹⌉₊ + 1

theorem dataInputSize_pos (D : CertificateInput) : 0 < dataInputSize D := by
  unfold dataInputSize
  omega

theorem stages_le_dataInputSize (D : CertificateInput) : D.stages ≤ dataInputSize D := by
  unfold dataInputSize
  omega

theorem gammaEncoding_le_dataInputSize (D : CertificateInput) : ratEncodingBits D.gamma ≤ dataInputSize D := by
  unfold dataInputSize
  omega

theorem riskEncoding_le_dataInputSize (D : CertificateInput) : ratEncodingBits D.risk ≤ dataInputSize D := by
  unfold dataInputSize
  omega

theorem gammaCeil_le_dataInputSize (D : CertificateInput) : ⌈D.gamma⁻¹⌉₊ ≤ dataInputSize D := by
  unfold dataInputSize
  omega

theorem gamma_inv_le_dataInputSize (D : CertificateInput) : D.gamma⁻¹ ≤ (dataInputSize D : ℚ) :=
  (Nat.le_ceil _).trans (by exact_mod_cast gammaCeil_le_dataInputSize D)

theorem risk_inv_le_den (D : CertificateInput) : D.risk⁻¹ ≤ (D.risk.den : ℚ) := by
  have hδ := rat_one_div_den_le D.risk D.risk_pos
  have hmul : (1 : ℚ) ≤ D.risk * D.risk.den :=
    (div_le_iff₀ (by exact_mod_cast D.risk.den_pos)).mp hδ
  have hdiv : (1 : ℚ) / D.risk ≤ D.risk.den :=
    (div_le_iff₀ D.risk_pos).mpr (by simpa only [mul_comm] using hmul)
  simpa only [one_div] using hdiv

theorem riskMagnitude_bits_le_dataInputSize (D : CertificateInput) :
    natBits (2 * D.stages * D.risk.den) ≤ dataInputSize D := by
  have hprod := natBits_prod_le [2, D.stages, D.risk.den] (by simp)
  have hnorm : natBits (2 * D.stages * D.risk.den) ≤
      natBits 2 + natBits D.stages + natBits D.risk.den := by
    simpa [Nat.mul_assoc, Nat.add_assoc] using hprod
  have htwo : natBits 2 = 2 := by norm_num [natBits]
  rw [htwo] at hnorm
  have hN : natBits D.stages ≤ D.stages + 1 :=
    Nat.add_le_add_right (Nat.log2_le_self _) _
  have hd : natBits D.risk.den ≤ ratEncodingBits D.risk := by
    change ratDenBits D.risk ≤ ratEncodingBits D.risk
    unfold ratEncodingBits
    omega
  have hgnum := natBits_pos D.gamma.num.natAbs
  have hgden := natBits_pos D.gamma.den
  change 0 < ratNumBits D.gamma at hgnum
  change 0 < ratDenBits D.gamma at hgden
  have hgEncoding : 3 ≤ ratEncodingBits D.gamma := by
    unfold ratEncodingBits
    omega
  unfold dataInputSize
  omega

/-- Logarithmic precision is bounded by the actual encoded denominator,
without replacing a small rational risk by an inverse-risk input. -/
theorem certificate_log_risk_bound (D : CertificateInput) :
    Real.log (2 * (D.stages : ℝ) / (D.risk : ℝ)) ≤
      (natBits (2 * D.stages * D.risk.den) : ℝ) := by
  let d := 2 * D.stages * D.risk.den
  let k := natBits d
  have hδ : (0 : ℝ) < D.risk := by exact_mod_cast D.risk_pos
  have hN : (0 : ℝ) < D.stages := by exact_mod_cast D.stages_pos
  have hinv : (D.risk : ℝ)⁻¹ ≤ (D.risk.den : ℝ) := by
    exact_mod_cast risk_inv_le_den D
  have hR : 2 * (D.stages : ℝ) / (D.risk : ℝ) ≤ (d : ℝ) := by
    calc
      _ = (2 * (D.stages : ℝ)) * (D.risk : ℝ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (2 * (D.stages : ℝ)) * (D.risk.den : ℝ) :=
        mul_le_mul_of_nonneg_left hinv (by positivity)
      _ = (d : ℝ) := by dsimp only [d]; push_cast; ring
  have hpow : (d : ℝ) < (2 : ℝ) ^ k := by exact_mod_cast natBits_lt_pow d
  have hlog := Real.log_le_log (div_pos (by positivity : (0 : ℝ) < 2 * D.stages) hδ)
    (hR.trans hpow.le)
  rw [Real.log_pow] at hlog
  have htwo : Real.log (2 : ℝ) ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    linarith
  exact hlog.trans (mul_le_of_le_one_right (Nat.cast_nonneg k) htwo)

/-- Original least positive odd majority count, via the already proved
formal certificate_t0_upper and an encoding-size logarithmic bound. -/
theorem certificate_t0_bound (D : CertificateInput) : D.t0 ≤ 4 * (dataInputSize D) ^ 3 := by
  let S := dataInputSize D
  have hg : (0 : ℝ) < D.gamma := by exact_mod_cast D.gamma_pos
  have hS : (1 : ℝ) ≤ S := by exact_mod_cast Nat.succ_le_of_lt (dataInputSize_pos D)
  have hinv : (D.gamma : ℝ)⁻¹ ≤ (S : ℝ) := by exact_mod_cast gamma_inv_le_dataInputSize D
  have hsquare : ((D.gamma : ℝ)⁻¹) ^ 2 ≤ (S : ℝ) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr hg.le) hinv 2
  have hfactor : (1 : ℝ) / (2 * (D.gamma : ℝ) ^ 2) ≤ (S : ℝ) ^ 2 := by
    calc
      _ ≤ 1 / (D.gamma : ℝ) ^ 2 :=
        one_div_le_one_div_of_le (sq_pos_of_pos hg) (by nlinarith [sq_nonneg (D.gamma : ℝ)])
      _ = ((D.gamma : ℝ)⁻¹) ^ 2 := by simp only [one_div, inv_pow]
      _ ≤ (S : ℝ) ^ 2 := hsquare
  have hlog := certificate_log_risk_bound D
  have hprecision : (natBits (2 * D.stages * D.risk.den) : ℝ) ≤ (S : ℝ) := by
    exact_mod_cast riskMagnitude_bits_le_dataInputSize D
  have hquotient : Real.log (2 * (D.stages : ℝ) / (D.risk : ℝ)) /
      (2 * (D.gamma : ℝ) ^ 2) ≤ (S : ℝ) ^ 3 := by
    calc
      _ ≤ (natBits (2 * D.stages * D.risk.den) : ℝ) / (2 * (D.gamma : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right hlog (by positivity)
      _ = (natBits (2 * D.stages * D.risk.den) : ℝ) * (1 / (2 * (D.gamma : ℝ) ^ 2)) := by ring
      _ ≤ (S : ℝ) * (S : ℝ) ^ 2 :=
        mul_le_mul hprecision hfactor (by positivity) (by positivity)
      _ = (S : ℝ) ^ 3 := by ring
  have ht := PDLower.certificate_t0_upper D
  have hone : (1 : ℝ) ≤ (S : ℝ) ^ 3 := one_le_pow₀ hS
  have hbound : (D.t0 : ℝ) ≤ 4 * (S : ℝ) ^ 3 := by linarith
  exact_mod_cast hbound

end PDROC.DataBits
