module

public import Paid.PDLower_CoreSearch_Guards_007
public import Paid.PDCompute_SolverSequenceBits_155

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver

namespace PDLower.CoreSearch

/-- Intrinsic values of the genuine current two solutions. This internal
certificate is separate from the caller's arbitrary scratch/live/output
carry. The outer cached-search representation supplies it from its grid. -/
structure ScalarInputBits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (scale : ℕ) : Prop where
  risk : ratEncodingBits P.certificate.risk≤scale
  fee : ratEncodingBits fee≤scale
  lowerPrice : ratEncodingBits lower.multiplier≤scale
  upperPrice : ratEncodingBits upper.multiplier≤scale
  lowerObs : ratEncodingBits (P.solveRecord lower).observation≤scale
  lowerRep : ratEncodingBits (P.solveRecord lower).repairs≤scale
  lowerRisk : ratEncodingBits (P.solveRisk lower)≤scale
  upperObs : ratEncodingBits (P.solveRecord upper).observation≤scale
  upperRep : ratEncodingBits (P.solveRecord upper).repairs≤scale
  upperRisk : ratEncodingBits (P.solveRisk upper)≤scale

def scalarValueBudget (scale : ℕ) : ℕ := 128*(scale+1)

/-- Every literal arithmetic intermediate in the original fixed-depth
prepare/ratio/mixture-cost scripts. No valid bracket, denominator≠0,
positivity, clipping, optimality or successful-run premise is needed. -/
structure ScalarArithmeticBits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (budget : ℕ) : Prop where
  denominator : ratEncodingBits (P.solveRisk lower-P.solveRisk upper)≤budget
  numerator : ratEncodingBits (P.certificate.risk-P.solveRisk upper)≤budget
  lowerProduct : ratEncodingBits (fee*(P.solveRecord lower).repairs)≤budget
  lowerCost : ratEncodingBits (P.solveCost fee lower)≤budget
  upperProduct : ratEncodingBits (fee*(P.solveRecord upper).repairs)≤budget
  upperCost : ratEncodingBits (P.solveCost fee upper)≤budget
  width : ratEncodingBits (upper.multiplier-lower.multiplier)≤budget
  gap : ratEncodingBits ((upper.multiplier-lower.multiplier)*P.certificate.risk)≤budget
  half : ratEncodingBits (1/2:ℚ)≤budget
  zero : ratEncodingBits (0:ℚ)≤budget
  one : ratEncodingBits (1:ℚ)≤budget
  weight : ratEncodingBits (P.mixtureWeight lower upper)≤budget
  complement : ratEncodingBits (1-P.mixtureWeight lower upper)≤budget
  weightedUpper : ratEncodingBits ((1-P.mixtureWeight lower upper)*P.solveCost fee upper)≤budget
  weightedLower : ratEncodingBits (P.mixtureWeight lower upper*P.solveCost fee lower)≤budget
  mixture : ratEncodingBits (P.mixtureCost fee lower upper)≤budget
  halfMixture : ratEncodingBits (P.mixtureCost fee lower upper/2)≤budget

theorem scalarArithmetic_bits (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve) (scale : ℕ)
    (bounded : ScalarInputBits P fee lower upper scale) :
    ScalarArithmeticBits P fee lower upper (scalarValueBudget scale) := by
  obtain ⟨risk,feeBits,priceL,priceU,obsL,repL,riskL,obsU,repU,riskU⟩ := bounded
  have den := ratEncodingBits_sub_le (P.solveRisk lower) (P.solveRisk upper)
  have num := ratEncodingBits_sub_le P.certificate.risk (P.solveRisk upper)
  have productL := ratEncodingBits_mul_le fee (P.solveRecord lower).repairs
  have costL := ratEncodingBits_add_le (P.solveRecord lower).observation (fee*(P.solveRecord lower).repairs)
  have productU := ratEncodingBits_mul_le fee (P.solveRecord upper).repairs
  have costU := ratEncodingBits_add_le (P.solveRecord upper).observation (fee*(P.solveRecord upper).repairs)
  change ratEncodingBits (P.solveCost fee lower)≤_ at costL
  change ratEncodingBits (P.solveCost fee upper)≤_ at costU
  have width := ratEncodingBits_sub_le upper.multiplier lower.multiplier
  have gap := ratEncodingBits_mul_le (upper.multiplier-lower.multiplier) P.certificate.risk
  have half : ratEncodingBits (1/2:ℚ)=4 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have zero : ratEncodingBits (0:ℚ)=3 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have one : ratEncodingBits (1:ℚ)=3 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have weight := ratEncodingBits_div_le (P.certificate.risk-P.solveRisk upper) (P.solveRisk lower-P.solveRisk upper)
  change ratEncodingBits (P.mixtureWeight lower upper)≤_ at weight
  have complement := ratEncodingBits_sub_le (1:ℚ) (P.mixtureWeight lower upper)
  have termU := ratEncodingBits_mul_le (1-P.mixtureWeight lower upper) (P.solveCost fee upper)
  have termL := ratEncodingBits_mul_le (P.mixtureWeight lower upper) (P.solveCost fee lower)
  have mix := ratEncodingBits_add_le (P.mixtureWeight lower upper*P.solveCost fee lower)
    ((1-P.mixtureWeight lower upper)*P.solveCost fee upper)
  change ratEncodingBits (P.mixtureCost fee lower upper)≤_ at mix
  have two : ratEncodingBits (2:ℚ)=4 := by norm_num [ratEncodingBits,ratNumBits,ratDenBits,natBits]
  have halfMix := ratEncodingBits_div_le (P.mixtureCost fee lower upper) (2:ℚ)
  unfold scalarValueBudget
  constructor <;> omega

end PDLower.CoreSearch
