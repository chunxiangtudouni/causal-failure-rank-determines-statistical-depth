module

public import Paid.PDROC_D27Prepare_Resources_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDROC.D27Prepare.Resources

theorem operandBudget_address_bits (P : Parameters) (fee : ℚ) :
    1 + natBits 64 ≤ operandBudget P fee := by
  have h := linear_le_operandBudget P fee
  have address : 1 + natBits 64 = 8 := by decide
  rw [address]
  omega

theorem rational_data_bits (P : Parameters) (fee q : ℚ)
    (bounded : ratEncodingBits q ≤ dataWeight P fee) :
    (Cell.rational q).bits ≤ operandBudget P fee := by
  exact le_trans (by change 1 + ratEncodingBits q ≤ 64 * (dataWeight P fee + 1); omega)
    (linear_le_operandBudget P fee)

theorem rawInput_cell_bits (P : Parameters) (fee : ℚ) :
    ∀ cell ∈ rawInput P fee, cell.bits ≤ operandBudget P fee := by
  obtain ⟨hN, _, _, _, _, _, hg, hd, hc, hf, _⟩ := scalar_data_bounds P fee
  have hK : natBits P.tools ≤ dataWeight P fee := by
    unfold dataWeight variableGammaSize rawSize
    omega
  intro cell member
  simp only [rawInput, List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl
  · exact natural_small_bits P fee _ (by omega)
  · exact le_trans (by change 1 + natBits P.tools ≤ 64 * (dataWeight P fee + 1); omega) (linear_le_operandBudget P fee)
  · exact rational_data_bits P fee _ hg
  · exact rational_data_bits P fee _ hd
  · exact rational_data_bits P fee _ hc
  · exact rational_data_bits P fee _ hf

/-- Used with the actual append-only-output theorem: every output cell
encountered at any real prefix belongs to this exact original output. -/
theorem preparedInput_cell_bits (P : Parameters) (fee : ℚ) :
    ∀ cell ∈ preparedInput P fee, cell.bits ≤ operandBudget P fee := by
  obtain ⟨_, ht, hM, hE, hQ, hJ, _, _, _, _, hL, hz, _⟩ := scalar_data_bounds P fee
  intro cell member
  simp only [preparedInput, List.mem_append] at member
  rcases member with raw | derived
  · exact rawInput_cell_bits P fee cell raw
  · simp only [List.mem_cons, List.not_mem_nil, or_false] at derived
    rcases derived with rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact natural_small_bits P fee _ (by omega)
    · exact natural_small_bits P fee _ (by omega)
    · exact natural_small_bits P fee _ (by omega)
    · exact natural_small_bits P fee _ (by omega)
    · exact natural_small_bits P fee _ (by omega)
    · exact rational_data_bits P fee _ hL
    · exact rational_data_bits P fee _ hz

theorem binomial_ratio_bits (P : Parameters) (fee : ℚ) (i : ℕ)
    (inside : i ≤ P.certificate.stages) :
    (Cell.rational (((P.certificate.stages - i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ))).bits ≤ operandBudget P fee := by
  have hN := (scalar_data_bounds P fee).1
  have hleft := natural_cast_encoding P fee (P.certificate.stages - i) (by omega)
  have hright := natural_cast_encoding P fee (i + 1) (by omega)
  have hdiv := PDROC.DataBits.ratEncodingBits_div_le
    ((P.certificate.stages - i : ℕ) : ℚ) ((i + 1 : ℕ) : ℚ)
  exact le_trans (by change 1 + ratEncodingBits (((P.certificate.stages - i : ℕ) : ℚ) / ((i + 1 : ℕ) : ℚ)) ≤
    64 * (dataWeight P fee + 1); omega) (linear_le_operandBudget P fee)

theorem binomial_tail_add_bits (P : Parameters) (fee : ℚ) (partialSum i : ℕ)
    (partialBound : partialSum ≤ 2 ^ P.certificate.stages) :
    (Cell.rational ((partialSum : ℚ) + (P.certificate.stages.choose i : ℚ))).bits ≤ operandBudget P fee := by
  have hN := (scalar_data_bounds P fee).1
  have hpow : natBits (2 ^ P.certificate.stages) = P.certificate.stages + 1 := by
    simp only [natBits, Nat.log2_two_pow]
  have hpartial := PDROC.DataBits.natBits_mono partialBound
  have hchoose := PDROC.DataBits.natBits_mono (Nat.choose_le_two_pow P.certificate.stages i)
  rw [hpow] at hpartial hchoose
  have hpe := PDROC.DataBits.ratEncodingBits_natCast partialSum
  have hce := PDROC.DataBits.ratEncodingBits_natCast (P.certificate.stages.choose i)
  have hadd := PDROC.DataBits.ratEncodingBits_add_le (partialSum : ℚ) (P.certificate.stages.choose i : ℚ)
  exact le_trans (by change 1 + ratEncodingBits ((partialSum : ℚ) + (P.certificate.stages.choose i : ℚ)) ≤
    64 * (dataWeight P fee + 1); omega) (linear_le_operandBudget P fee)

end PDROC.D27Prepare.Resources
