module

public import PaperProofs.Paid.PDROC_DataBits_Counts_001
public import Mathlib.Algebra.Order.Ring.Pow

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem counts_half_power_le_inverse (d k : ℕ) (hd : 0 < d) (hpow : d < 2 ^ k) :
    (1 / 2 : ℚ) ^ k ≤ 1 / (d : ℚ) := by
  have hcast : (d : ℚ) ≤ (2 : ℚ) ^ k := by exact_mod_cast hpow.le
  calc
    _ = 1 / (2 : ℚ) ^ k := by rw [div_pow, one_pow]
    _ ≤ 1 / (d : ℚ) := one_div_le_one_div_of_le (by exact_mod_cast hd) hcast

/-- A genuine witness block for the original rational odds, not a new
endpoint or search procedure. -/
theorem certificate_odds_block_ge_two (D : CertificateInput) :
    (2 : ℚ) ≤ D.odds ^ ⌈D.gamma⁻¹⌉₊ := by
  let A := ⌈D.gamma⁻¹⌉₊
  have hceil : D.gamma⁻¹ ≤ (A : ℚ) := Nat.le_ceil _
  have hmul := mul_le_mul_of_nonneg_left hceil D.gamma_pos.le
  have hunit : (1 : ℚ) ≤ D.gamma * A := by
    simpa only [mul_inv_cancel₀ D.gamma_pos.ne'] using hmul
  have hbase : 1 + 4 * D.gamma ≤ D.odds := by
    unfold CertificateInput.odds
    apply (le_div_iff₀ D.denominator_pos).mpr
    nlinarith [sq_nonneg D.gamma]
  have hBernoulli := one_add_mul_le_pow (by linarith [D.gamma_pos] : (-2 : ℚ) ≤ 4 * D.gamma) A
  have hpower := pow_le_pow_left₀ (by linarith [D.gamma_pos] : (0 : ℚ) ≤ 1 + 4 * D.gamma) hbase A
  nlinarith

theorem certificate_M_precision_bound (D : CertificateInput) :
    D.M ≤ ⌈D.gamma⁻¹⌉₊ * natBits (4 * D.stages * D.t0 * D.risk.den) := by
  let A := ⌈D.gamma⁻¹⌉₊
  let d := 4 * D.stages * D.t0 * D.risk.den
  let k := natBits d
  have hd : 0 < d := Nat.mul_pos
    (Nat.mul_pos (Nat.mul_pos (by decide) D.stages_pos) D.t0_pos) D.risk.den_pos
  have hdyadic : (d : ℚ) < (2 : ℚ) ^ k := by exact_mod_cast natBits_lt_pow d
  have hblock : (2 : ℚ) ≤ D.odds ^ A := certificate_odds_block_ge_two D
  have hp : (2 : ℚ) ^ k ≤ D.odds ^ (A * k) := by
    calc
      _ ≤ (D.odds ^ A) ^ k := pow_le_pow_left₀ (by decide : (0 : ℚ) ≤ 2) hblock k
      _ = _ := (pow_mul _ _ _).symm
  have hden : (d : ℚ) ≤ 1 + D.odds ^ (A * k) := by linarith
  have herror : D.rocError (A * k) ≤ 1 / (d : ℚ) :=
    one_div_le_one_div_of_le (by exact_mod_cast hd) hden
  have hlower : 1 / (d : ℚ) ≤ D.menuRatio := by
    unfold CertificateInput.menuRatio
    calc
      _ = (1 / (D.risk.den : ℚ)) / (4 * (D.stages : ℚ) * D.t0) := by
        dsimp only [d]
        push_cast
        rw [div_div]
        congr 1
        ring
      _ ≤ _ := div_le_div_of_nonneg_right (rat_one_div_den_le D.risk D.risk_pos) (by positivity)
  exact D.M_min (herror.trans hlower)

theorem certificate_M_bound (D : CertificateInput) : D.M ≤ 16 * (dataInputSize D) ^ 4 := by
  let S := dataInputSize D
  let A := ⌈D.gamma⁻¹⌉₊
  let k := natBits (4 * D.stages * D.t0 * D.risk.den)
  have hprod := natBits_prod_le [4, D.stages, D.t0, D.risk.den] (by simp)
  have hnorm : k ≤ natBits 4 + natBits D.stages + natBits D.t0 + natBits D.risk.den := by
    simpa [k, Nat.mul_assoc, Nat.add_assoc] using hprod
  have hfour : natBits 4 = 3 := by norm_num [natBits]
  rw [hfour] at hnorm
  have hN : natBits D.stages ≤ D.stages + 1 := Nat.add_le_add_right (Nat.log2_le_self _) _
  have ht : natBits D.t0 ≤ D.t0 + 1 := Nat.add_le_add_right (Nat.log2_le_self _) _
  have hd : natBits D.risk.den ≤ ratEncodingBits D.risk := by unfold ratEncodingBits ratDenBits; omega
  have hgn := natBits_pos D.gamma.num.natAbs
  have hgd := natBits_pos D.gamma.den
  have hg : 3 ≤ ratEncodingBits D.gamma := by unfold ratEncodingBits ratNumBits ratDenBits; omega
  have hk : k ≤ D.t0 + 2 * S := by dsimp only [S, dataInputSize]; omega
  have hA : A ≤ S := gammaCeil_le_dataInputSize D
  have hM : D.M ≤ A * k := certificate_M_precision_bound D
  have hscale := Nat.mul_le_mul hA hk
  have ht0 := certificate_t0_bound D
  have htScale := Nat.mul_le_mul_left S (Nat.add_le_add_right ht0 (2 * S))
  have hS : 1 ≤ S := Nat.succ_le_of_lt (dataInputSize_pos D)
  have h24 : S ^ 2 ≤ S ^ 4 := pow_le_pow_right₀ hS (by decide : 2 ≤ 4)
  nlinarith

theorem certificate_E_precision_bound (D : CertificateInput) :
    D.E ≤ natBits (12 * D.stages * D.t0 * D.gamma.den * D.risk.den) := by
  let J := 12 * D.stages * D.t0
  let d := J * D.gamma.den * D.risk.den
  let k := natBits d
  have hJ : 0 < J := Nat.mul_pos (Nat.mul_pos (by decide) D.stages_pos) D.t0_pos
  have hd : 0 < d := Nat.mul_pos (Nat.mul_pos hJ D.gamma.den_pos) D.risk.den_pos
  have hNnz : (D.stages : ℚ) ≠ 0 := by exact_mod_cast D.stages_pos.ne'
  have htnz : (D.t0 : ℚ) ≠ 0 := by exact_mod_cast D.t0_pos.ne'
  have hratio : D.gamma * D.epsilon = (D.gamma * D.risk) * (J : ℚ)⁻¹ := by
    dsimp only [CertificateInput.epsilon, CertificateInput.menuRatio, J]
    push_cast
    field_simp [hNnz, htnz]; ring
  have hJden : ((J : ℚ)⁻¹).den = J := Rat.inv_natCast_den_of_pos hJ
  have hden : (D.gamma * D.epsilon).den ∣ d := by
    rw [hratio]
    have hJdvd : ((J : ℚ)⁻¹).den ∣ J := by simpa only [hJden] using dvd_refl J
    have hproduct := (Rat.mul_den_dvd (D.gamma * D.risk) ((J : ℚ)⁻¹)).trans
      (Nat.mul_dvd_mul (Rat.mul_den_dvd D.gamma D.risk) hJdvd)
    have heq : D.gamma.den * D.risk.den * J = d := by dsimp only [d]; ring
    simpa only [heq] using hproduct
  have hdenle : (D.gamma * D.epsilon).den ≤ d := Nat.le_of_dvd hd hden
  have hlower : 1 / (d : ℚ) ≤ D.gamma * D.epsilon :=
    (one_div_le_one_div_of_le (by exact_mod_cast (D.gamma * D.epsilon).den_pos)
      (by exact_mod_cast hdenle)).trans
      (rat_one_div_den_le _ (mul_pos D.gamma_pos D.epsilon_pos))
  have hhalf : (1 / 2 : ℚ) ^ k ≤ D.gamma * D.epsilon :=
    (counts_half_power_le_inverse d k hd (natBits_lt_pow d)).trans hlower
  exact D.E_min ⟨Nat.succ_le_of_lt (natBits_pos d), hhalf⟩

theorem certificate_E_bound (D : CertificateInput) : D.E ≤ 16 * (dataInputSize D) ^ 3 := by
  let S := dataInputSize D
  let k := natBits (12 * D.stages * D.t0 * D.gamma.den * D.risk.den)
  have hprod := natBits_prod_le [12, D.stages, D.t0, D.gamma.den, D.risk.den] (by simp)
  have hnorm : k ≤ natBits 12 + natBits D.stages + natBits D.t0 +
      natBits D.gamma.den + natBits D.risk.den := by
    simpa [k, Nat.mul_assoc, Nat.add_assoc] using hprod
  have htwelve : natBits 12 = 4 := by norm_num [natBits]
  rw [htwelve] at hnorm
  have hN : natBits D.stages ≤ D.stages + 1 := Nat.add_le_add_right (Nat.log2_le_self _) _
  have ht : natBits D.t0 ≤ D.t0 + 1 := Nat.add_le_add_right (Nat.log2_le_self _) _
  have hg : natBits D.gamma.den ≤ ratEncodingBits D.gamma := by unfold ratEncodingBits ratDenBits; omega
  have hr : natBits D.risk.den ≤ ratEncodingBits D.risk := by unfold ratEncodingBits ratDenBits; omega
  have hk : k ≤ D.t0 + 6 * S := by dsimp only [S, dataInputSize]; omega
  have hE : D.E ≤ k := certificate_E_precision_bound D
  have ht0 := certificate_t0_bound D
  have hS : 1 ≤ S := Nat.succ_le_of_lt (dataInputSize_pos D)
  have h13 : S ≤ S ^ 3 := by simpa only [pow_one] using pow_le_pow_right₀ hS (by decide : 1 ≤ 3)
  nlinarith

theorem certificate_Q_bound (D : CertificateInput) : D.Q ≤ 64 * (dataInputSize D) ^ 5 := by
  let S := dataInputSize D
  let A := ⌈D.gamma⁻¹⌉₊
  have hA : A ≤ S := gammaCeil_le_dataInputSize D
  have hceil : D.gamma⁻¹ ≤ (A : ℚ) := Nat.le_ceil _
  have hmenuRat : ((D.M : ℚ) + 1) / D.gamma ≤ (((D.M + 1) * A : ℕ) : ℚ) := by
    calc
      _ = ((D.M : ℚ) + 1) * D.gamma⁻¹ := div_eq_mul_inv _ _
      _ ≤ ((D.M : ℚ) + 1) * A := mul_le_mul_of_nonneg_left hceil (by positivity)
      _ = _ := by push_cast; ring
  have hmenu : ⌈((D.M : ℚ) + 1) / D.gamma⌉₊ ≤ (D.M + 1) * A := Nat.ceil_le.mpr hmenuRat
  have hinvSq : (D.gamma⁻¹) ^ 2 ≤ (A : ℚ) ^ 2 :=
    pow_le_pow_left₀ (inv_nonneg.mpr D.gamma_pos.le) hceil 2
  have htailRat : (2 * (D.E : ℚ)) / D.gamma ^ 2 ≤ ((2 * D.E * A ^ 2 : ℕ) : ℚ) := by
    calc
      _ = (2 * (D.E : ℚ)) * (D.gamma⁻¹) ^ 2 := by simp only [div_eq_mul_inv, inv_pow]
      _ ≤ (2 * (D.E : ℚ)) * (A : ℚ) ^ 2 := mul_le_mul_of_nonneg_left hinvSq (by positivity)
      _ = _ := by push_cast; ring
  have htail : ⌈(2 * (D.E : ℚ)) / D.gamma ^ 2⌉₊ ≤ 2 * D.E * A ^ 2 := Nat.ceil_le.mpr htailRat
  have hM := certificate_M_bound D
  have hE := certificate_E_bound D
  have hS : 1 ≤ S := Nat.succ_le_of_lt (dataInputSize_pos D)
  have hS5 : 1 ≤ S ^ 5 := one_le_pow₀ hS
  have h15 : S ≤ S ^ 5 := by simpa only [pow_one] using pow_le_pow_right₀ hS (by decide : 1 ≤ 5)
  have hmenuScale := Nat.mul_le_mul (Nat.add_le_add_right hM 1) hA
  have hASq : A ^ 2 ≤ S ^ 2 := Nat.pow_le_pow_left hA 2
  have htailScale := Nat.mul_le_mul (Nat.mul_le_mul_left 2 hE) hASq
  unfold CertificateInput.Q
  apply max_le
  · nlinarith
  · apply max_le
    · exact hmenu.trans (by nlinarith)
    · exact htail.trans (by nlinarith)

end PDROC.DataBits
