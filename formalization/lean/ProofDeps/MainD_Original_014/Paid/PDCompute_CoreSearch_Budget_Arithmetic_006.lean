module
public import Paid.PDCompute_CoreSearch_Budget_Polynomial_004

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreSearchBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDLower.CoreSearch

def StateArithmeticBits (P : Parameters) (fee : ℚ) (scale : ℕ) : MultiplierState→Prop
  | .exact solution=>ScalarArithmeticBits P fee solution solution (scalarValueBudget scale)
  | .bracket lower upper=>ScalarArithmeticBits P fee lower upper (scalarValueBudget scale)

theorem StateScalarInput.arithmetic {P : Parameters} {fee : ℚ} {scale : ℕ} {state : MultiplierState}
    (intrinsic : StateScalarInput P fee scale state) : StateArithmeticBits P fee scale state:=by
  cases state with
  | exact solution=>exact scalarArithmetic_bits P fee solution solution scale intrinsic
  | bracket lower upper=>exact scalarArithmetic_bits P fee lower upper scale intrinsic

/-- The actual original current state supplies every intermediate of
017 at ONE fixed scale, including exact/J0/final-update branches. -/
theorem original_search_arithmeticBits (P : Parameters) (fee : ℚ) (steps : ℕ) (inside : steps≤P.bisectionBudget fee) :
    StateArithmeticBits P fee (originalScalarScale P fee) (P.cachedMultiplierSearch P.endpointCache fee steps):=
  StateScalarInput.arithmetic (original_search_scalarInputBits P fee steps inside)

theorem original_final_arithmeticBits (P : Parameters) (fee : ℚ) :
    StateArithmeticBits P fee (originalScalarScale P fee) (P.buildCachedFrontend fee).state:=
  StateScalarInput.arithmetic (original_final_scalarInputBits P fee)

end PDCompute.CoreSearchBudget
