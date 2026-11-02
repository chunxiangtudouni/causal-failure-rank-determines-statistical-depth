module
public import Paid.PDCompute_CoreGlobalBudget_Geometry_003

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreGlobalBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits PDCompute.Solver PDCompute.CoreSearchBudget PDLower.CoreSearch

def StateSolverRoom (P : Parameters) (fee : ℚ) (B : ℕ) : MultiplierState → Prop
  | .exact solution => 4194304*solverBitScale P fee solution.multiplier P.certificate.stages P.tools≤B
  | .bracket lower upper =>
      4194304*solverBitScale P fee lower.multiplier P.certificate.stages P.tools≤B ∧
      4194304*solverBitScale P fee upper.multiplier P.certificate.stages P.tools≤B

theorem original_state_solver_room (P : Parameters) (fee : ℚ) (pcUpper j : ℕ)
    (inside : j≤P.bisectionBudget fee+1) :
    StateSolverRoom P fee (budget P fee pcUpper) (P.cachedMultiplierSearch P.endpointCache fee j) := by
  have prices:=original_state_prices P fee j inside
  generalize equality : P.cachedMultiplierSearch P.endpointCache fee j=state at prices ⊢
  cases state with
  | exact solution => exact budget_solver P fee solution.multiplier pcUpper prices
  | bracket lower upper => exact ⟨budget_solver P fee lower.multiplier pcUpper prices.1,
      budget_solver P fee upper.multiplier pcUpper prices.2⟩

/-- Covers the original initial state, every j through J, and the final
updated state. No reachability, optimality or physical-state oracle is a
hypothesis. Actual midpoint j+1 is paid by the same original B. -/
theorem original_search_rooms (P : Parameters) (fee : ℚ) (pcUpper j : ℕ)
    (inside : j≤P.bisectionBudget fee) :
    StateScalarInput P fee (originalScalarScale P fee) (P.cachedMultiplierSearch P.endpointCache fee j) ∧
    StateArithmeticBits P fee (originalScalarScale P fee) (P.cachedMultiplierSearch P.endpointCache fee j) ∧
    StateSolverRoom P fee (budget P fee pcUpper) (P.cachedMultiplierSearch P.endpointCache fee j) ∧
    (∀ lower upper,P.cachedMultiplierSearch P.endpointCache fee j=.bracket lower upper →
      4194304*solverBitScale P fee ((lower.multiplier+upper.multiplier)/2)
        P.certificate.stages P.tools≤budget P fee pcUpper) ∧
    1+scalarValueBudget (originalScalarScale P fee)≤budget P fee pcUpper :=
  ⟨original_search_scalarInputBits P fee j inside,original_search_arithmeticBits P fee j inside,
    original_state_solver_room P fee pcUpper j (by omega),
    fun lower upper source=>budget_midpoint_solver P fee pcUpper j lower upper inside source,
    budget_scalar P fee pcUpper⟩

theorem original_final_rooms (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    StateScalarInput P fee (originalScalarScale P fee) (P.buildCachedFrontend fee).state ∧
    StateArithmeticBits P fee (originalScalarScale P fee) (P.buildCachedFrontend fee).state ∧
    StateSolverRoom P fee (budget P fee pcUpper) (P.buildCachedFrontend fee).state ∧
    1+scalarValueBudget (originalScalarScale P fee)≤budget P fee pcUpper :=
  ⟨original_final_scalarInputBits P fee,original_final_arithmeticBits P fee,
    original_state_solver_room P fee pcUpper (P.bisectionBudget fee) (by omega),budget_scalar P fee pcUpper⟩

/-- The fixed program chooses pcUpper BEFORE all P and fee. Thus the
formal D27 linear core-operand constant is also chosen before all inputs. -/
theorem budget_le_core (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    budget P fee pcUpper≤(134217728+2*natBits pcUpper+256)*coreOperandBound P fee := by
  have positive:=coreOperandBound_positive P fee
  have static:=Nat.mul_le_mul_left (2*natBits pcUpper+256) positive
  simp only [Nat.mul_one] at static
  unfold budget
  nlinarith

theorem fixed_program_linear_bound (pcUpper : ℕ) :
    ∃ C : ℕ,0<C ∧ ∀ (P : Parameters) (fee : ℚ),budget P fee pcUpper≤C*coreOperandBound P fee :=
  ⟨134217728+2*natBits pcUpper+256,by omega,fun P fee=>budget_le_core P fee pcUpper⟩

end PDCompute.CoreGlobalBudget
