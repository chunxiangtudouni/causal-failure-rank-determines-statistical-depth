module

public import Paid.PDROC_D27Prepare_EndpointRun_001
public import Paid.PDROC_D27Prepare_Resources_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Resources PDROC.DataBits

namespace PDROC.D27Prepare.EndpointRun

theorem setup_value_bits (P : Parameters) (fee : ℚ) :
    ∀ q ∈ [(P.certificate.t0 : ℚ), 4 * (P.certificate.stages : ℚ),
      4 * (P.certificate.stages : ℚ) * P.certificate.t0, P.certificate.menuRatio,
      2 * P.certificate.gamma, 1 + 2 * P.certificate.gamma, 1 - 2 * P.certificate.gamma,
      P.certificate.odds, (1 : ℚ)], (Cell.rational q).bits ≤ operandBudget P fee := by
  obtain ⟨hN, ht, _, _, _, _, hg, _⟩ := scalar_data_bounds P fee
  have castN := natural_cast_encoding P fee P.certificate.stages (by omega)
  have castT := natural_cast_encoding P fee P.certificate.t0 (by omega)
  have one : ratEncodingBits (1 : ℚ) = 3 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have two : ratEncodingBits (2 : ℚ) = 4 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have four : ratEncodingBits (4 : ℚ) = 5 := by norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  have fourN := ratEncodingBits_mul_le (4 : ℚ) (P.certificate.stages : ℚ)
  have fourNt := ratEncodingBits_mul_le (4 * (P.certificate.stages : ℚ)) (P.certificate.t0 : ℚ)
  have twoG := ratEncodingBits_mul_le (2 : ℚ) P.certificate.gamma
  have plus := ratEncodingBits_add_le (1 : ℚ) (2 * P.certificate.gamma)
  have minus := ratEncodingBits_sub_le (1 : ℚ) (2 * P.certificate.gamma)
  have menu := (search_base_encodings P fee).2.2.1
  have odds := (search_base_encodings P fee).2.1
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

end PDROC.D27Prepare.EndpointRun
