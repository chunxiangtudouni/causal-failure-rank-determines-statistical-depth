module
public import Paid.PDCompute_CoreSearch_Budget_PriceGrid_001
public import Paid.PDCompute_SolverFieldBits_151

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreSearchBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDLower.CoreSearch

/-- Stored root statistics reset to the exact original-table bound.
Their size is independent of the current multiplier and search depth. -/
theorem solutionGrid_record_bits (P : Parameters) (fee : ℚ) (D : ℕ) (solution : MultiplierSolve)
    (grid : SolutionGrid P fee D solution) :
    ratEncodingBits (P.solveRecord solution).observation≤solverStatsBits P fee P.certificate.stages ∧
    ratEncodingBits (P.solveRecord solution).repairs≤solverStatsBits P fee P.certificate.stages ∧
    ratEncodingBits (P.solveRisk solution)≤solverStatsBits P fee P.certificate.stages:=by
  have fields:=arbitraryTable_fieldBits P fee solution.multiplier P.certificate.stages P.tools P.certificate.stages P.tools (le_refl _)
  simpa only [Parameters.solveRecord,Parameters.solveRisk,grid.table_eq,solverStatsBits] using fields

def uniformScalarScale (P : Parameters) (fee : ℚ) (J : ℕ) : ℕ:=
  priceBudget P J+solverStatsBits P fee P.certificate.stages+ratEncodingBits P.certificate.risk+ratEncodingBits fee+1

theorem solutionGrids_scalarInputBits (P : Parameters) (fee : ℚ) (J steps : ℕ) (lower upper : MultiplierSolve)
    (inside : steps≤J+1)
    (lowerGrid : SolutionGrid P fee (2^steps*P.Lambda.den) lower)
    (upperGrid : SolutionGrid P fee (2^steps*P.Lambda.den) upper) :
    ScalarInputBits P fee lower upper (uniformScalarScale P fee J):=by
  have lowerPrice:=solutionGrid_price_uniform P fee J steps lower inside lowerGrid
  have upperPrice:=solutionGrid_price_uniform P fee J steps upper inside upperGrid
  obtain ⟨lowerObs,lowerRep,lowerRisk⟩:=solutionGrid_record_bits P fee _ lower lowerGrid
  obtain ⟨upperObs,upperRep,upperRisk⟩:=solutionGrid_record_bits P fee _ upper upperGrid
  constructor <;> unfold uniformScalarScale <;> omega

/-- Exact states reuse the same proven solution in both ABI positions;
they do not create a new solve or require a fresh statistics oracle. -/
def StateScalarInput (P : Parameters) (fee : ℚ) (scale : ℕ) : MultiplierState→Prop
  | .exact solution=>ScalarInputBits P fee solution solution scale
  | .bracket lower upper=>ScalarInputBits P fee lower upper scale

theorem stateGrid_scalarInputBits (P : Parameters) (fee : ℚ) (J steps : ℕ) (state : MultiplierState)
    (inside : steps≤J+1) (grid : StateGrid P fee (2^steps*P.Lambda.den) state) :
    StateScalarInput P fee (uniformScalarScale P fee J) state:=by
  cases state with
  | exact solution=>exact solutionGrids_scalarInputBits P fee J steps solution solution inside grid grid
  | bracket lower upper=>exact solutionGrids_scalarInputBits P fee J steps lower upper inside grid.1 grid.2

end PDCompute.CoreSearchBudget
