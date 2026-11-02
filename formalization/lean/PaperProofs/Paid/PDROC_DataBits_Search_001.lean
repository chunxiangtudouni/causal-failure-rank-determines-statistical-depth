module

public import PaperProofs.Paid.PDROC_DataBits_Mixture_001
public import PaperProofs.Paid.PDROC_DataBits_Gap_001
public import Mathlib.Data.Nat.Choose.Sum

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators
open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem blindBinomialTail_unitInterval (P : Parameters) :
    0 ≤ P.blindBinomialTail ∧ P.blindBinomialTail ≤ 1 := by
  have hchoose : (∑ k ∈ Finset.range (P.certificate.stages + 1),
      (Nat.choose P.certificate.stages k : ℚ)) = (2 : ℚ) ^ P.certificate.stages := by
    exact_mod_cast Nat.sum_range_choose P.certificate.stages
  constructor
  · unfold PaperProofs.Paid.Parameters.blindBinomialTail
    apply Finset.sum_nonneg
    intro k _hk
    split_ifs <;> positivity
  · unfold PaperProofs.Paid.Parameters.blindBinomialTail
    calc
      _ ≤ ∑ k ∈ Finset.range (P.certificate.stages + 1),
          (Nat.choose P.certificate.stages k : ℚ) * (1 / 2 : ℚ) ^ P.certificate.stages := by
        apply Finset.sum_le_sum
        intro k _hk
        split_ifs
        · exact le_rfl
        · positivity
      _ = (∑ k ∈ Finset.range (P.certificate.stages + 1),
          (Nat.choose P.certificate.stages k : ℚ)) * (1 / 2 : ℚ) ^ P.certificate.stages :=
        (Finset.sum_mul _ _ _).symm
      _ = 1 := by rw [hchoose, ← mul_pow]; norm_num

theorem zeroChargeRisk_unitInterval (P : Parameters) (fee : ℚ) :
    0 ≤ P.zeroChargeRisk fee ∧ P.zeroChargeRisk fee ≤ 1 := by
  unfold PaperProofs.Paid.Parameters.zeroChargeRisk
  split_ifs
  · exact blindBinomialTail_unitInterval P
  · have h0 : 0 ≤ (1 / 2 : ℚ) ^ P.certificate.stages := by positivity
    have h1 : (1 / 2 : ℚ) ^ P.certificate.stages ≤ 1 :=
      pow_le_one₀ (by norm_num) (by norm_num)
    constructor <;> linarith

theorem zeroChargeRisk_encoding (P : Parameters) (fee : ℚ) :
    ratEncodingBits (P.zeroChargeRisk fee) ≤ 2 * P.certificate.stages + 3 := by
  obtain ⟨h0, h1⟩ := zeroChargeRisk_unitInterval P fee
  have hn := ratNumBits_le_ratDenBits (P.zeroChargeRisk fee) h0 h1
  have hd : ratDenBits (P.zeroChargeRisk fee) ≤ P.certificate.stages + 1 := by
    have hh := ratDenBits_le_of_dvd (by positivity : 0 < 2 ^ P.certificate.stages)
      (zeroChargeRisk_den_dvd P fee)
    simpa only [natBits, Nat.log2_two_pow] using hh
  unfold ratEncodingBits
  omega

theorem rat_le_numAbs (q : ℚ) : q ≤ (q.num.natAbs : ℚ) := by
  conv_lhs => rw [← Rat.num_div_den q]
  apply (div_le_iff₀ (by exact_mod_cast q.den_pos)).mpr
  have hnum : (q.num : ℚ) ≤ (q.num.natAbs : ℚ) := by
    simpa only [Int.cast_natCast] using (Int.cast_le (R := ℚ)).mpr (Int.le_natAbs (a := q.num))
  have hmul : q.num.natAbs ≤ q.num.natAbs * q.den := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left q.num.natAbs (show 1 ≤ q.den from q.den_pos)
  have hmulq : (q.num.natAbs : ℚ) ≤ (q.num.natAbs : ℚ) * (q.den : ℚ) := by exact_mod_cast hmul
  exact hnum.trans hmulq

/-- The actual total natural ceil and clog, including q≤0 and q=0. -/
theorem rat_clog_natCeil_le_numBits (q : ℚ) : Nat.clog 2 ⌈q⌉₊ ≤ ratNumBits q := by
  apply (Nat.clog_le_iff_le_pow (by norm_num : 1 < 2)).mpr
  have hceil : ⌈q⌉₊ ≤ q.num.natAbs := Nat.ceil_le.mpr (rat_le_numAbs q)
  exact hceil.trans (natBits_lt_pow q.num.natAbs).le

theorem ratEncodingBits_natCast (n : ℕ) : ratEncodingBits (n : ℚ) = natBits n + 2 := by
  simp only [ratEncodingBits, ratNumBits, ratDenBits, Rat.num_natCast, Rat.den_natCast,
    Int.natAbs_natCast]
  norm_num [natBits]
  omega

theorem natBits_le_self_add_one (n : ℕ) : natBits n ≤ n + 1 :=
  Nat.add_le_add_right (Nat.log2_le_self n) 1

end PDROC.DataBits
