module

public import Paid.PDROC_D27Prepare_Resources_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits

namespace PDROC.D27Prepare.Resources

theorem quadratic_le_operandBudget (P : Parameters) (fee : ℚ) :
    256 * (dataWeight P fee + 1) ^ 2 ≤ operandBudget P fee := by
  have h := Nat.pow_le_pow_right (by omega : 0 < dataWeight P fee + 1) (by decide : 2 ≤ 4)
  unfold operandBudget
  omega

theorem search_base_encodings (P : Parameters) (fee : ℚ) :
    ratEncodingBits P.certificate.varianceBase ≤ 32 * (dataWeight P fee + 1) ∧
    ratEncodingBits P.certificate.odds ≤ 32 * (dataWeight P fee + 1) ∧
    ratEncodingBits P.certificate.menuRatio ≤ 32 * (dataWeight P fee + 1) ∧
    ratEncodingBits (P.certificate.gamma * P.certificate.epsilon) ≤ 32 * (dataWeight P fee + 1) ∧
    ratEncodingBits ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2) ≤ 32 * (dataWeight P fee + 1) ∧
    ratEncodingBits (P.certificate.varianceBase ^ 2) ≤ 32 * (dataWeight P fee + 1) := by
  obtain ⟨hN, ht, _, _, _, _, hg, hd, _⟩ := scalar_data_bounds P fee
  have hNe := natural_cast_encoding P fee P.certificate.stages (by omega)
  have hte := natural_cast_encoding P fee P.certificate.t0 (by omega)
  have hone : ratEncodingBits (1 : ℚ) = 3 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have htwo : ratEncodingBits (2 : ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hthree : ratEncodingBits (3 : ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hfour : ratEncodingBits (4 : ℚ) = 5 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hg2 : ratEncodingBits (P.certificate.gamma ^ 2) ≤ 2 * dataWeight P fee := by
    have h := ratEncodingBits_mul_le P.certificate.gamma P.certificate.gamma
    rw [← pow_two] at h
    omega
  have hfourG := ratEncodingBits_mul_le (4 : ℚ) (P.certificate.gamma ^ 2)
  have hv0 := ratEncodingBits_sub_le (1 : ℚ) (4 * P.certificate.gamma ^ 2)
  have hv : ratEncodingBits P.certificate.varianceBase ≤ 4 * dataWeight P fee + 16 := by
    unfold CertificateInput.varianceBase
    omega
  have htwoG := ratEncodingBits_mul_le (2 : ℚ) P.certificate.gamma
  have hplus := ratEncodingBits_add_le (1 : ℚ) (2 * P.certificate.gamma)
  have hminus := ratEncodingBits_sub_le (1 : ℚ) (2 * P.certificate.gamma)
  have hodds0 := ratEncodingBits_div_le (1 + 2 * P.certificate.gamma) (1 - 2 * P.certificate.gamma)
  have ho : ratEncodingBits P.certificate.odds ≤ 4 * dataWeight P fee + 28 := by
    unfold CertificateInput.odds
    omega
  have hfourN := ratEncodingBits_mul_le (4 : ℚ) (P.certificate.stages : ℚ)
  have hfourNt := ratEncodingBits_mul_le (4 * (P.certificate.stages : ℚ)) (P.certificate.t0 : ℚ)
  have hmenu0 := ratEncodingBits_div_le P.certificate.risk
    (4 * (P.certificate.stages : ℚ) * (P.certificate.t0 : ℚ))
  have hm : ratEncodingBits P.certificate.menuRatio ≤ 3 * dataWeight P fee + 13 := by
    unfold CertificateInput.menuRatio
    omega
  have hepsilon := ratEncodingBits_div_le P.certificate.menuRatio (3 : ℚ)
  have hthreshold := ratEncodingBits_mul_le P.certificate.gamma P.certificate.epsilon
  have he : ratEncodingBits (P.certificate.gamma * P.certificate.epsilon) ≤ 4 * dataWeight P fee + 17 := by
    unfold CertificateInput.epsilon at hthreshold ⊢
    omega
  have htwoN := ratEncodingBits_mul_le (2 : ℚ) (P.certificate.stages : ℚ)
  have hdeltaRatio := ratEncodingBits_div_le P.certificate.risk (2 * (P.certificate.stages : ℚ))
  have hdeltaSquared : ratEncodingBits ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2) ≤
      4 * dataWeight P fee + 16 := by
    have h := ratEncodingBits_mul_le (P.certificate.risk / (2 * (P.certificate.stages : ℚ)))
      (P.certificate.risk / (2 * (P.certificate.stages : ℚ)))
    rw [← pow_two] at h
    omega
  have hvs : ratEncodingBits (P.certificate.varianceBase ^ 2) ≤ 8 * dataWeight P fee + 32 := by
    have h := ratEncodingBits_mul_le P.certificate.varianceBase P.certificate.varianceBase
    rw [← pow_two] at h
    omega
  omega

theorem bounded_power_encoding (P : Parameters) (fee q : ℚ) (j : ℕ)
    (base : ratEncodingBits q ≤ 32 * (dataWeight P fee + 1)) (index : j ≤ dataWeight P fee) :
    ratEncodingBits (q ^ j) ≤ 33 * (dataWeight P fee + 1) ^ 2 := by
  have hbase : ratEncodingBits q + 1 ≤ 33 * (dataWeight P fee + 1) := by omega
  calc
    ratEncodingBits (q ^ j) ≤ (j + 1) * (ratEncodingBits q + 1) := ratEncodingBits_pow_le q j
    _ ≤ (dataWeight P fee + 1) * (33 * (dataWeight P fee + 1)) :=
      Nat.mul_le_mul (by omega) hbase
    _ = 33 * (dataWeight P fee + 1) ^ 2 := by ring

theorem bounded_power_bits (P : Parameters) (fee q : ℚ) (j : ℕ)
    (base : ratEncodingBits q ≤ 32 * (dataWeight P fee + 1)) (index : j ≤ dataWeight P fee) :
    (Cell.rational (q ^ j)).bits ≤ operandBudget P fee := by
  have h := bounded_power_encoding P fee q j base index
  have hp : 1 ≤ (dataWeight P fee + 1) ^ 2 := one_le_pow₀ (by omega)
  exact le_trans (by change 1 + ratEncodingBits (q ^ j) ≤ 256 * (dataWeight P fee + 1) ^ 2; omega)
    (quadratic_le_operandBudget P fee)

theorem endpoint_guard_intermediate_bits (P : Parameters) (fee : ℚ) (j : ℕ)
    (index : j ≤ P.certificate.M) :
    (Cell.rational (1 + P.certificate.odds ^ j)).bits ≤ operandBudget P fee ∧
    (Cell.rational (P.certificate.menuRatio * (1 + P.certificate.odds ^ j))).bits ≤ operandBudget P fee := by
  have bounds := search_base_encodings P fee
  have hM := (scalar_data_bounds P fee).2.2.1
  have power := bounded_power_encoding P fee P.certificate.odds j bounds.2.1 (by omega)
  have hmenu := bounds.2.2.1
  have hone : ratEncodingBits (1 : ℚ) = 3 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hsum := ratEncodingBits_add_le (1 : ℚ) (P.certificate.odds ^ j)
  have hmul := ratEncodingBits_mul_le P.certificate.menuRatio (1 + P.certificate.odds ^ j)
  have hp : 1 ≤ (dataWeight P fee + 1) ^ 2 := one_le_pow₀ (by omega)
  have hlinear : dataWeight P fee + 1 ≤ (dataWeight P fee + 1) ^ 2 :=
    Nat.le_self_pow (by decide : 2 ≠ 0) _
  have hb := quadratic_le_operandBudget P fee
  constructor
  · exact le_trans (by change 1 + ratEncodingBits (1 + P.certificate.odds ^ j) ≤
      256 * (dataWeight P fee + 1) ^ 2; omega) hb
  · exact le_trans (by change 1 + ratEncodingBits (P.certificate.menuRatio * (1 + P.certificate.odds ^ j)) ≤
      256 * (dataWeight P fee + 1) ^ 2; omega) hb

theorem variance_power_bits (P : Parameters) (fee : ℚ) (j : ℕ) (index : j ≤ P.certificate.t0) :
    (Cell.rational (P.certificate.varianceBase ^ j)).bits ≤ operandBudget P fee := by
  have ht := (scalar_data_bounds P fee).2.1
  exact bounded_power_bits P fee _ j (search_base_encodings P fee).1 (by omega)

theorem odds_power_bits (P : Parameters) (fee : ℚ) (j : ℕ) (index : j ≤ P.certificate.M) :
    (Cell.rational (P.certificate.odds ^ j)).bits ≤ operandBudget P fee := by
  have hM := (scalar_data_bounds P fee).2.2.1
  exact bounded_power_bits P fee _ j (search_base_encodings P fee).2.1 (by omega)

theorem exponent_power_bits (P : Parameters) (fee : ℚ) (j : ℕ) (index : j ≤ P.certificate.E) :
    (Cell.rational ((1 / 2 : ℚ) ^ j)).bits ≤ operandBudget P fee := by
  have hE := (scalar_data_bounds P fee).2.2.2.1
  have half : ratEncodingBits (1 / 2 : ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  exact bounded_power_bits P fee _ j (by omega) (by omega)

end PDROC.D27Prepare.Resources
