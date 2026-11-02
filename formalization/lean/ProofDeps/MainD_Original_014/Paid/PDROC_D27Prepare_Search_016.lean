module

public import Paid.PDROC_D27Prepare_Resources_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Resources PDROC.DataBits

namespace PDROC.D27Prepare.Search

/-- Every scalar actually produced by the nine-command majority setup.
This finite certificate is subsequently consumed at each literal command
prefix, rather than inferring intermediate bounds from the final heap. -/
theorem majority_setup_value_bits (P : Parameters) (fee : ℚ) :
    ∀ q ∈ [(P.certificate.stages : ℚ), P.certificate.gamma ^ 2,
      4 * P.certificate.gamma ^ 2, P.certificate.varianceBase,
      P.certificate.varianceBase ^ 2, 2 * (P.certificate.stages : ℚ),
      P.certificate.risk / (2 * (P.certificate.stages : ℚ)),
      (P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2,
      P.certificate.varianceBase], (Cell.rational q).bits ≤ operandBudget P fee := by
  obtain ⟨hN, _, _, _, _, _, hg, hr, _⟩ := scalar_data_bounds P fee
  have castN := natural_cast_encoding P fee P.certificate.stages (by omega)
  have two : ratEncodingBits (2 : ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have four : ratEncodingBits (4 : ℚ) = 5 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have square : ratEncodingBits (P.certificate.gamma ^ 2) ≤ 2 * dataWeight P fee := by
    have h := ratEncodingBits_mul_le P.certificate.gamma P.certificate.gamma
    rw [← pow_two] at h
    omega
  have fourG := ratEncodingBits_mul_le (4 : ℚ) (P.certificate.gamma ^ 2)
  have twoN := ratEncodingBits_mul_le (2 : ℚ) (P.certificate.stages : ℚ)
  have ratio := ratEncodingBits_div_le P.certificate.risk (2 * (P.certificate.stages : ℚ))
  have bases := search_base_encodings P fee
  have variance := bases.1
  have threshold := bases.2.2.2.2.1
  have varianceSquared := bases.2.2.2.2.2
  have small (q : ℚ) (h : ratEncodingBits q ≤ 32 * (dataWeight P fee + 1)) :
      (Cell.rational q).bits ≤ operandBudget P fee :=
    le_trans (by change 1 + ratEncodingBits q ≤ 64 * (dataWeight P fee + 1); omega)
      (linear_le_operandBudget P fee)
  intro q member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals
    apply small
    omega

end PDROC.D27Prepare.Search
