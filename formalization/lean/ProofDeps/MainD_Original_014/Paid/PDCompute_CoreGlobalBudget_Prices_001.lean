module
public import Paid.PDCompute_CoreSearch_Budget_CoreScale_005
public import Paid.PDCompute_CoreSearch_Budget_Arithmetic_006
public import Paid.RootD27Core_SearchRepresentation_056

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreGlobalBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits PDCompute.Solver PDCompute.CoreSearchBudget PDLower.CoreSearch

/-- Only original source solutions; the grid is derived, never supplied
as an extra qualification on an original input or a physical run. -/
def StatePriceBits (P : Parameters) (fee : ℚ) : MultiplierState → Prop
  | .exact solution => ratEncodingBits solution.multiplier≤16*coreOperandBound P fee
  | .bracket lower upper => ratEncodingBits lower.multiplier≤16*coreOperandBound P fee ∧
      ratEncodingBits upper.multiplier≤16*coreOperandBound P fee

theorem grid_price_core (P : Parameters) (fee : ℚ) (j : ℕ) (solution : MultiplierSolve)
    (inside : j≤P.bisectionBudget fee+1)
    (grid : SolutionGrid P fee (2^j*P.Lambda.den) solution) :
    ratEncodingBits solution.multiplier≤16*coreOperandBound P fee :=
  (solutionGrid_price_uniform P fee _ j solution inside grid).trans (original_priceBudget_le_core P fee)

theorem original_state_prices (P : Parameters) (fee : ℚ) (j : ℕ)
    (inside : j≤P.bisectionBudget fee+1) :
    StatePriceBits P fee (P.cachedMultiplierSearch P.endpointCache fee j) := by
  have grid:=cachedMultiplierSearch_grid P fee j
  generalize equality : P.cachedMultiplierSearch P.endpointCache fee j=state at grid ⊢
  cases state with
  | exact solution => exact grid_price_core P fee j solution inside grid
  | bracket lower upper => exact ⟨grid_price_core P fee j lower inside grid.1,
      grid_price_core P fee j upper inside grid.2⟩

theorem original_initial_prices (P : Parameters) (fee : ℚ) :
    ratEncodingBits (0:ℚ)≤16*coreOperandBound P fee ∧
      ratEncodingBits P.Lambda≤16*coreOperandBound P fee := by
  have grid:=cachedInitialState_grid P fee
  have lower : SolutionGrid P fee (2^0*P.Lambda.den)
      (P.cachedSolveMultiplier P.endpointCache fee 0) := by simpa using grid.1
  have upper : SolutionGrid P fee (2^0*P.Lambda.den)
      (P.cachedSolveMultiplier P.endpointCache fee P.Lambda) := by simpa using grid.2
  exact ⟨grid_price_core P fee 0 _ (by omega) lower,grid_price_core P fee 0 _ (by omega) upper⟩

theorem original_midpoint_price (P : Parameters) (fee : ℚ) (j : ℕ) (lower upper : MultiplierSolve)
    (inside : j≤P.bisectionBudget fee)
    (source : P.cachedMultiplierSearch P.endpointCache fee j=.bracket lower upper) :
    ratEncodingBits ((lower.multiplier+upper.multiplier)/2)≤16*coreOperandBound P fee := by
  have grid:=cachedMultiplierSearch_grid P fee j
  rw [source] at grid
  have middle:=midpoint_solutionGrid P fee (2^j*P.Lambda.den) lower upper grid.1 grid.2
  have denominator : 2*(2^j*P.Lambda.den)=2^(j+1)*P.Lambda.den := by ring
  rw [denominator] at middle
  exact grid_price_core P fee (j+1) _ (by omega) middle

/-- The physical OriginalSolved certificate matches the actual original
table. Its arbitrary penalty never enlarges the three root statistics. -/
theorem originalSolved_statistics (P : Parameters) (fee : ℚ) (solution : MultiplierSolve)
    (solved : RootD27.Core.OriginalSolved P fee solution) :
    ratEncodingBits (P.solveRecord solution).observation≤1280*coreOperandBound P fee ∧
    ratEncodingBits (P.solveRecord solution).repairs≤1280*coreOperandBound P fee ∧
    ratEncodingBits (P.solveRisk solution)≤1280*coreOperandBound P fee := by
  have fields:=arbitraryTable_fieldBits P fee solution.multiplier P.certificate.stages P.tools
    P.certificate.stages P.tools (le_refl _)
  have table : solution.table=P.cachedSolveMenuTable P.endpointCache fee solution.multiplier
      P.tools P.certificate.stages := by
    have same:=congrArg MultiplierSolve.table solved
    exact same
  have statistics : ratEncodingBits (P.solveRecord solution).observation≤solverStatsBits P fee P.certificate.stages ∧
      ratEncodingBits (P.solveRecord solution).repairs≤solverStatsBits P fee P.certificate.stages ∧
      ratEncodingBits (P.solveRisk solution)≤solverStatsBits P fee P.certificate.stages := by
    simpa only [Parameters.solveRecord,Parameters.solveRisk,table,solverStatsBits] using fields
  exact ⟨statistics.1.trans (original_stats_le_core P fee),
    statistics.2.1.trans (original_stats_le_core P fee),statistics.2.2.trans (original_stats_le_core P fee)⟩

end PDCompute.CoreGlobalBudget
