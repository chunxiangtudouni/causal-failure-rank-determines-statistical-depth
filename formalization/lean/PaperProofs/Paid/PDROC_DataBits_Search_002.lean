module

public import PaperProofs.Paid.PDROC_DataBits_Search_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem Lambda_encoding (P : Parameters) :
    ratEncodingBits P.Lambda ≤ ratEncodingBits P.reviewFee + ratEncodingBits P.certificate.risk +
      P.certificate.stages + natBits P.certificate.t0 + 10 := by
  have hdiv := ratEncodingBits_div_le (4 * P.B) P.certificate.risk
  have h4 := ratEncodingBits_mul_le 4 P.B
  have hB := ratEncodingBits_mul_le (P.reviewFee * (P.certificate.stages : ℚ))
    (P.certificate.t0 : ℚ)
  have hc := ratEncodingBits_mul_le P.reviewFee (P.certificate.stages : ℚ)
  have hN := natBits_le_self_add_one P.certificate.stages
  have hfour : ratEncodingBits (4 : ℚ) = 5 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  rw [ratEncodingBits_natCast] at hc
  rw [ratEncodingBits_natCast] at hB
  dsimp only [PaperProofs.Paid.Parameters.Lambda, PaperProofs.Paid.Parameters.B] at hdiv h4 ⊢
  omega

theorem bisectionArgument_encoding (P : Parameters) (fee : ℚ) :
    ratEncodingBits (2 * P.Lambda * P.certificate.risk / P.positiveValueFloor fee) ≤
      64 * (P.certificate.stages + ratEncodingBits P.certificate.risk + ratEncodingBits P.reviewFee +
        ratEncodingBits fee + natBits P.certificate.t0 + 1) := by
  let floor := P.firstChargeFloor fee
  let zeta := P.zeroChargeRisk fee
  have hdiv := ratEncodingBits_div_le (2 * P.Lambda * P.certificate.risk)
    (floor * (zeta - P.certificate.risk))
  have hnum := ratEncodingBits_mul_le (2 * P.Lambda) P.certificate.risk
  have htwo := ratEncodingBits_mul_le 2 P.Lambda
  have hden := ratEncodingBits_mul_le floor (zeta - P.certificate.risk)
  have hgap := ratEncodingBits_sub_le zeta P.certificate.risk
  have hfloor := firstChargeFloor_encoding P fee
  have hzeta := zeroChargeRisk_encoding P fee
  have hLambda := Lambda_encoding P
  have htwoBits : ratEncodingBits (2 : ℚ) = 4 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  change ratEncodingBits floor ≤ _ at hfloor
  change ratEncodingBits zeta ≤ _ at hzeta
  change ratEncodingBits (2 * P.Lambda * P.certificate.risk /
    (floor * (zeta - P.certificate.risk))) ≤ _
  omega

/-- Exact original computed J_bis, with full fee encoding and original
baseline t0 bits; no positive-gap, policy-risk or optimality premise. -/
theorem bisectionBudget_bit_bound (P : Parameters) (fee : ℚ) :
    P.bisectionBudget fee ≤
      64 * (P.certificate.stages + ratEncodingBits P.certificate.risk + ratEncodingBits P.reviewFee +
        ratEncodingBits fee + natBits P.certificate.t0 + 1) := by
  unfold PaperProofs.Paid.Parameters.bisectionBudget
  apply (rat_clog_natCeil_le_numBits _).trans
  apply (show ratNumBits (2 * P.Lambda * P.certificate.risk / P.positiveValueFloor fee) ≤
      ratEncodingBits (2 * P.Lambda * P.certificate.risk / P.positiveValueFloor fee) by
    unfold ratEncodingBits
    omega).trans
  exact bisectionArgument_encoding P fee

end PDROC.DataBits
