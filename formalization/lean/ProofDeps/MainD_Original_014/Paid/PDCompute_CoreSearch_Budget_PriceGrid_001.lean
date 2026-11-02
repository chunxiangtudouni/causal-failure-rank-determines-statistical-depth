module
public import PaperProofs.Paid.PDROC_DataBits_007
public import Paid.PDCompute_SolverNumericScale_162
public import Paid.PDLower_CoreSearch_ScalarNumbers_017

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreSearchBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver

/-- Thin extraction of the multiplier part of original solutionGrid_bits.
No whole encoded table is charged to each midpoint arithmetic update. -/
theorem solutionGrid_price_bits (P : Parameters) (fee : ℚ) (steps : ℕ) (solution : MultiplierSolve)
    (grid : SolutionGrid P fee (2^steps*P.Lambda.den) solution) :
    ratEncodingBits solution.multiplier≤8*(steps+ratEncodingBits P.Lambda+1):=by
  have positive : 0<2^steps*P.Lambda.den:=by positivity
  have denominator:=ratDenBits_le_of_dvd positive grid.den_dvd
  have product:=natBits_mul_le (2^steps) P.Lambda.den
  have power : natBits (2^steps)=steps+1:=by simp only [natBits,Nat.log2_two_pow]
  rw [power] at product
  have encoding:=ratEncodingBits_le_of_range solution.multiplier P.Lambda
    (steps+1+ratDenBits P.Lambda) grid.multiplier_nonneg grid.multiplier_le (denominator.trans product)
  unfold ratEncodingBits at encoding ⊢
  omega

/-- J+1 includes every midpoint of every reached state through J, even
the final updated state and the degenerate J=0 boundary. -/
def priceBudget (P : Parameters) (J : ℕ) : ℕ:=8*(J+ratEncodingBits P.Lambda+2)

theorem solutionGrid_price_uniform (P : Parameters) (fee : ℚ) (J steps : ℕ) (solution : MultiplierSolve)
    (inside : steps≤J+1) (grid : SolutionGrid P fee (2^steps*P.Lambda.den) solution) :
    ratEncodingBits solution.multiplier≤priceBudget P J:=by
  have price:=solutionGrid_price_bits P fee steps solution grid
  unfold priceBudget
  omega

end PDCompute.CoreSearchBudget
