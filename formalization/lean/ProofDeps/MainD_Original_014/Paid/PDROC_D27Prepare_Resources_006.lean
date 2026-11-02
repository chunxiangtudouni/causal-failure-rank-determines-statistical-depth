module

public import Paid.PDROC_D27Prepare_Resources_001
public import Mathlib.Data.Nat.Choose.Bounds

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits

namespace PDROC.D27Prepare.Resources

def operandBudget (P : Parameters) (fee : ℚ) : ℕ := 4096 * (dataWeight P fee + 1) ^ 4

theorem operandBudget_polynomial : PolynomialBound size (fun x => operandBudget x.1 x.2) := by
  have h := dataWeight_polynomial.add (PolynomialBound.constant size 1) size_pos
  have hsq := h.mul h
  have hp : PolynomialBound size (fun x => (dataWeight x.1 x.2 + 1) ^ 4) := by
    convert hsq.mul hsq using 1
    funext x
    ring
  exact (PolynomialBound.constant size 4096).mul hp

theorem linear_le_operandBudget (P : Parameters) (fee : ℚ) :
    64 * (dataWeight P fee + 1) ≤ operandBudget P fee := by
  have h := Nat.le_self_pow (by decide : 4 ≠ 0) (dataWeight P fee + 1)
  unfold operandBudget
  omega

theorem scalar_data_bounds (P : Parameters) (fee : ℚ) :
    P.certificate.stages ≤ dataWeight P fee ∧
    P.certificate.t0 ≤ dataWeight P fee ∧ P.certificate.M ≤ dataWeight P fee ∧
    P.certificate.E ≤ dataWeight P fee ∧ P.certificate.Q ≤ dataWeight P fee ∧
    P.bisectionBudget fee ≤ dataWeight P fee ∧
    ratEncodingBits P.certificate.gamma ≤ dataWeight P fee ∧
    ratEncodingBits P.certificate.risk ≤ dataWeight P fee ∧
    ratEncodingBits P.reviewFee ≤ dataWeight P fee ∧ ratEncodingBits fee ≤ dataWeight P fee ∧
    ratEncodingBits P.Lambda ≤ dataWeight P fee ∧
    ratEncodingBits (P.zeroChargeRisk fee) ≤ dataWeight P fee ∧
    ratEncodingBits (P.firstChargeFloor fee) ≤ dataWeight P fee ∧
    ratEncodingBits (P.positiveValueFloor fee) ≤ dataWeight P fee ∧
    ratEncodingBits (originalRatio P fee) ≤ dataWeight P fee := by
  unfold dataWeight countWeight variableGammaSize rawSize numericalSize
  omega

theorem natural_small_bits (P : Parameters) (fee : ℚ) (n : ℕ)
    (hn : n ≤ dataWeight P fee + 1) : (Cell.natural n).bits ≤ operandBudget P fee := by
  have h := natBits_le_succ n
  exact le_trans (by change 1 + natBits n ≤ 64 * (dataWeight P fee + 1); omega) (linear_le_operandBudget P fee)

theorem natural_cast_encoding (P : Parameters) (fee : ℚ) (n : ℕ)
    (hn : n ≤ dataWeight P fee + 1) : ratEncodingBits (n : ℚ) ≤ dataWeight P fee + 4 := by
  rw [ratEncodingBits_natCast]
  have h := natBits_le_succ n
  omega

theorem natural_cast_bits (P : Parameters) (fee : ℚ) (n : ℕ)
    (hn : n ≤ dataWeight P fee + 1) : (Cell.rational (n : ℚ)).bits ≤ operandBudget P fee := by
  have h := natural_cast_encoding P fee n hn
  exact le_trans (by change 1 + ratEncodingBits (n : ℚ) ≤ 64 * (dataWeight P fee + 1); omega)
    (linear_le_operandBudget P fee)

/-- Covers both integral choose coefficients and integral partial-tail
accumulators without expanding their numeric size into a loop count. -/
theorem binomial_integer_bits (P : Parameters) (fee : ℚ) (n : ℕ)
    (hn : n ≤ 2 ^ P.certificate.stages) :
    (Cell.rational (n : ℚ)).bits ≤ operandBudget P fee := by
  have hs := (scalar_data_bounds P fee).1
  have hb := natBits_mono hn
  have hpow : natBits (2 ^ P.certificate.stages) = P.certificate.stages + 1 := by
    simp only [natBits, Nat.log2_two_pow]
  rw [hpow] at hb
  have henc := ratEncodingBits_natCast n
  exact le_trans (by change 1 + ratEncodingBits (n : ℚ) ≤ 64 * (dataWeight P fee + 1); omega)
    (linear_le_operandBudget P fee)

theorem binomial_choose_bits (P : Parameters) (fee : ℚ) (i : ℕ) :
    (Cell.rational (P.certificate.stages.choose i : ℚ)).bits ≤ operandBudget P fee :=
  binomial_integer_bits P fee _ (Nat.choose_le_two_pow _ _)

theorem multiplier_intermediate_bits (P : Parameters) (fee : ℚ) :
    (Cell.rational (4 * P.reviewFee)).bits ≤ operandBudget P fee ∧
    (Cell.rational (4 * P.reviewFee * P.certificate.stages)).bits ≤ operandBudget P fee ∧
    (Cell.rational (4 * P.reviewFee * P.certificate.stages * P.certificate.t0)).bits ≤ operandBudget P fee := by
  obtain ⟨hN, ht, _, _, _, _, _, _, hc, _⟩ := scalar_data_bounds P fee
  have h4 : ratEncodingBits (4 : ℚ) = 5 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hNenc := natural_cast_encoding P fee P.certificate.stages (by omega)
  have htenc := natural_cast_encoding P fee P.certificate.t0 (by omega)
  have first := ratEncodingBits_mul_le (4 : ℚ) P.reviewFee
  have second := ratEncodingBits_mul_le (4 * P.reviewFee) (P.certificate.stages : ℚ)
  have third := ratEncodingBits_mul_le (4 * P.reviewFee * P.certificate.stages) (P.certificate.t0 : ℚ)
  have hb := linear_le_operandBudget P fee
  constructor
  · exact le_trans (by change 1 + ratEncodingBits (4 * P.reviewFee) ≤ 64 * (dataWeight P fee + 1); omega) hb
  constructor
  · exact le_trans (by change 1 + ratEncodingBits (4 * P.reviewFee * P.certificate.stages) ≤ 64 * (dataWeight P fee + 1); omega) hb
  · exact le_trans (by change 1 + ratEncodingBits (4 * P.reviewFee * P.certificate.stages * P.certificate.t0) ≤ 64 * (dataWeight P fee + 1); omega) hb

theorem dyadic_intermediate_bits (P : Parameters) (fee : ℚ) (i : ℕ)
    (hi : i ≤ P.certificate.stages) :
    (Cell.rational ((1 / 2 : ℚ) ^ i)).bits ≤ operandBudget P fee := by
  have hN := (scalar_data_bounds P fee).1
  have hp := ratEncodingBits_pow_le (1 / 2 : ℚ) i
  have hh : ratEncodingBits (1 / 2 : ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  rw [hh] at hp
  exact le_trans (by change 1 + ratEncodingBits ((1 / 2 : ℚ) ^ i) ≤ 64 * (dataWeight P fee + 1); omega)
    (linear_le_operandBudget P fee)

theorem risk_gap_bits (P : Parameters) (fee : ℚ) :
    (Cell.rational (P.zeroChargeRisk fee - P.certificate.risk)).bits ≤ operandBudget P fee := by
  have data := scalar_data_bounds P fee
  have hr := data.2.2.2.2.2.2.2.1
  have hz := data.2.2.2.2.2.2.2.2.2.2.2.1
  have hs := ratEncodingBits_sub_le (P.zeroChargeRisk fee) P.certificate.risk
  exact le_trans (by change 1 + ratEncodingBits (P.zeroChargeRisk fee - P.certificate.risk) ≤ 64 * (dataWeight P fee + 1); omega)
    (linear_le_operandBudget P fee)

theorem ratio_intermediate_bits (P : Parameters) (fee : ℚ) :
    (Cell.rational (2 * P.Lambda)).bits ≤ operandBudget P fee ∧
    (Cell.rational (2 * P.Lambda * P.certificate.risk)).bits ≤ operandBudget P fee := by
  have data := scalar_data_bounds P fee
  have hr := data.2.2.2.2.2.2.2.1
  have hL := data.2.2.2.2.2.2.2.2.2.2.1
  have htwo : ratEncodingBits (2 : ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have hfirst := ratEncodingBits_mul_le (2 : ℚ) P.Lambda
  have hsecond := ratEncodingBits_mul_le (2 * P.Lambda) P.certificate.risk
  have hb := linear_le_operandBudget P fee
  constructor
  · exact le_trans (by change 1 + ratEncodingBits (2 * P.Lambda) ≤ 64 * (dataWeight P fee + 1); omega) hb
  · exact le_trans (by change 1 + ratEncodingBits (2 * P.Lambda * P.certificate.risk) ≤ 64 * (dataWeight P fee + 1); omega) hb

/-- x can be numerically huge. Only its bit length is charged, and the
halving loop's j is bounded by the original budget. -/
theorem budget_halving_bits (P : Parameters) (fee : ℚ) (x j : ℕ)
    (hx : x ≤ ⌈originalRatio P fee⌉₊) (hj : j ≤ P.bisectionBudget fee) :
    (Cell.natural x).bits ≤ operandBudget P fee ∧
    (Cell.natural (x / 2)).bits ≤ operandBudget P fee ∧
    (Cell.natural (j + 1)).bits ≤ operandBudget P fee := by
  have data := scalar_data_bounds P fee
  have hJ := data.2.2.2.2.2.1
  have hratio := data.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  have hceil := ceil_cell_bits (originalRatio P fee)
  have hxb := Nat.add_le_add_left (natBits_mono hx) 1
  have hhalf := Nat.add_le_add_left (natBits_mono (Nat.div_le_self x 2)) 1
  have hb := linear_le_operandBudget P fee
  refine ⟨?_, ?_, natural_small_bits P fee (j + 1) (by omega)⟩
  · exact le_trans (by change 1 + natBits x ≤ 64 * (dataWeight P fee + 1); change 1 + natBits ⌈originalRatio P fee⌉₊ ≤ _ at hceil; omega) hb
  · exact le_trans (by change 1 + natBits (x / 2) ≤ 64 * (dataWeight P fee + 1); change 1 + natBits ⌈originalRatio P fee⌉₊ ≤ _ at hceil; omega) hb

end PDROC.D27Prepare.Resources
