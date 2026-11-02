module
public import Paid.PDCompute_CoreSearch_Budget_Fields_002

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreSearchBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDLower.CoreSearch

/-- Every actual original search state, including zero and the final
updated state. Its grid certificate is DERIVED from the actual search. -/
theorem cached_search_scalarInputBits (P : Parameters) (fee : ℚ) (J steps : ℕ) (inside : steps≤J+1) :
    StateScalarInput P fee (uniformScalarScale P fee J) (P.cachedMultiplierSearch P.endpointCache fee steps):=
  stateGrid_scalarInputBits P fee J steps _ inside (cachedMultiplierSearch_grid P fee steps)

theorem cached_initial_scalarInputBits (P : Parameters) (fee : ℚ) (J : ℕ) :
    ScalarInputBits P fee (P.cachedSolveMultiplier P.endpointCache fee 0) (P.cachedSolveMultiplier P.endpointCache fee P.Lambda)
      (uniformScalarScale P fee J):=
  stateGrid_scalarInputBits P fee J 0 (P.cachedInitialState P.endpointCache fee) (Nat.zero_le _)
    (by simpa only [pow_zero,one_mul] using cachedInitialState_grid P fee)

theorem cached_next_scalarInputBits (P : Parameters) (fee : ℚ) (J steps : ℕ) (inside : steps≤J) :
    StateScalarInput P fee (uniformScalarScale P fee J)
      (P.cachedMultiplierStep P.endpointCache fee (P.cachedMultiplierSearch P.endpointCache fee steps)):=
  cached_search_scalarInputBits P fee J (steps+1) (Nat.add_le_add_right inside 1)

/-- This predicate observes the ORIGINAL next midpoint solve; exact
states retain their existing solution instead of inventing a solve. -/
def MidpointScalarInput (P : Parameters) (fee : ℚ) (scale : ℕ) : MultiplierState→Prop
  | .exact solution=>ScalarInputBits P fee solution solution scale
  | .bracket lower upper=>
      let middle:=P.cachedSolveMultiplier P.endpointCache fee ((lower.multiplier+upper.multiplier)/2)
      ScalarInputBits P fee middle middle scale

theorem cached_midpoint_scalarInputBits (P : Parameters) (fee : ℚ) (J steps : ℕ) (inside : steps≤J) :
    MidpointScalarInput P fee (uniformScalarScale P fee J) (P.cachedMultiplierSearch P.endpointCache fee steps):=by
  have grid:=cachedMultiplierSearch_grid P fee steps
  generalize equality : P.cachedMultiplierSearch P.endpointCache fee steps=state at grid ⊢
  cases state with
  | exact solution=>
    exact solutionGrids_scalarInputBits P fee J steps solution solution (by omega) grid grid
  | bracket lower upper=>
    have midpoint:=midpoint_solutionGrid P fee (2^steps*P.Lambda.den) lower upper grid.1 grid.2
    have denominator : 2*(2^steps*P.Lambda.den)=2^(steps+1)*P.Lambda.den:=by ring
    rw [denominator] at midpoint
    exact solutionGrids_scalarInputBits P fee J (steps+1) _ _ (Nat.add_le_add_right inside 1) midpoint midpoint

def originalScalarScale (P : Parameters) (fee : ℚ) : ℕ:=uniformScalarScale P fee (P.bisectionBudget fee)

theorem original_search_scalarInputBits (P : Parameters) (fee : ℚ) (steps : ℕ) (inside : steps≤P.bisectionBudget fee) :
    StateScalarInput P fee (originalScalarScale P fee) (P.cachedMultiplierSearch P.endpointCache fee steps):=
  cached_search_scalarInputBits P fee _ steps (by omega)

theorem original_final_scalarInputBits (P : Parameters) (fee : ℚ) :
    StateScalarInput P fee (originalScalarScale P fee) (P.buildCachedFrontend fee).state:=
  cached_search_scalarInputBits P fee _ (P.bisectionBudget fee) (by omega)

theorem original_midpoint_scalarInputBits (P : Parameters) (fee : ℚ) (steps : ℕ) (inside : steps≤P.bisectionBudget fee) :
    MidpointScalarInput P fee (originalScalarScale P fee) (P.cachedMultiplierSearch P.endpointCache fee steps):=
  cached_midpoint_scalarInputBits P fee _ steps inside

end PDCompute.CoreSearchBudget
