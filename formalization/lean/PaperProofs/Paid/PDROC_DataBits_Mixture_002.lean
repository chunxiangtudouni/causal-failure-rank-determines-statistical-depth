module

public import PaperProofs.Paid.PDROC_DataBits_Mixture_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.DataBits

theorem mixtureWeight_encoding (P : Parameters) (lower upper : MultiplierSolve) :
    ratEncodingBits (P.mixtureWeight lower upper) ≤
      4 * (ratEncodingBits P.certificate.risk + ratEncodingBits (P.solveRisk lower) +
        ratEncodingBits (P.solveRisk upper) + 1) := by
  have hdiv := ratEncodingBits_div_le (P.certificate.risk - P.solveRisk upper)
    (P.solveRisk lower - P.solveRisk upper)
  have hnum := ratEncodingBits_sub_le P.certificate.risk (P.solveRisk upper)
  have hden := ratEncodingBits_sub_le (P.solveRisk lower) (P.solveRisk upper)
  change ratEncodingBits ((P.certificate.risk - P.solveRisk upper) /
    (P.solveRisk lower - P.solveRisk upper)) ≤ _
  omega

theorem mixtureCost_encoding (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) :
    ratEncodingBits (P.mixtureCost fee lower upper) ≤
      16 * (ratEncodingBits (P.mixtureWeight lower upper) + ratEncodingBits (P.solveCost fee lower) +
        ratEncodingBits (P.solveCost fee upper) + 1) := by
  let w := P.mixtureWeight lower upper
  let a := P.solveCost fee lower
  let b := P.solveCost fee upper
  have hsum := ratEncodingBits_add_le (w * a) ((1 - w) * b)
  have hmul1 := ratEncodingBits_mul_le w a
  have hmul2 := ratEncodingBits_mul_le (1 - w) b
  have hsub := ratEncodingBits_sub_le 1 w
  have hone : ratEncodingBits (1 : ℚ) = 3 := by
    norm_num [ratEncodingBits, ratNumBits, ratDenBits, natBits]
  change ratEncodingBits (w * a + (1 - w) * b) ≤
    16 * (ratEncodingBits w + ratEncodingBits a + ratEncodingBits b + 1)
  omega

/-- Original mixture data-size target for the actual rational cached
endpoint risks/costs; valid brackets, policy performance and nonzero
denominators are not additional inputs, and division by zero is covered. -/
theorem mixtureBitClaims : MixtureBitClaims := by
  refine ⟨16, by norm_num, ?_⟩
  intro P fee lower upper
  refine ⟨?_, mixtureCost_encoding P fee lower upper⟩
  exact (mixtureWeight_encoding P lower upper).trans (by omega)

end PDROC.DataBits
