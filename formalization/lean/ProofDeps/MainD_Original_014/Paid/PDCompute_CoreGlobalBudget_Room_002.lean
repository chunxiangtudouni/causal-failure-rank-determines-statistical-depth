module
public import Paid.PDCompute_CoreGlobalBudget_Prices_001
public import Paid.PDLower_CoreRuntimeNumeric_SolverStub_005

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.CoreGlobalBudget
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.DataBits PDCompute.Solver PDCompute.CoreSearchBudget PDLower.CoreSearch
open PDLower.CoreRuntimeNumeric PDCompute.NatControl

/-- Chosen ONCE before the original run; no incoming dirty-state size,
search-round recurrence, table answer or execution witness occurs here. -/
def budget (P : Parameters) (fee : ℚ) (pcUpper : ℕ) : ℕ :=
  134217728*coreOperandBound P fee+2*natBits pcUpper+256

theorem budget_core (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    134217728*coreOperandBound P fee≤budget P fee pcUpper := by unfold budget;omega

theorem budget_small (P : Parameters) (fee : ℚ) (pcUpper : ℕ) : 7≤budget P fee pcUpper := by
  unfold budget
  omega

theorem budget_runtime (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    32*coreOperandBound P fee≤budget P fee pcUpper := by
  have room:=budget_core P fee pcUpper
  omega

theorem budget_solver (P : Parameters) (fee penalty : ℚ) (pcUpper : ℕ)
    (price : ratEncodingBits penalty≤16*coreOperandBound P fee) :
    4194304*solverBitScale P fee penalty P.certificate.stages P.tools≤budget P fee pcUpper := by
  have scalar:=solver_core_scalarRoom P fee penalty 16 price
  have room:=budget_core P fee pcUpper
  omega

theorem budget_initial_solvers (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    4194304*solverBitScale P fee 0 P.certificate.stages P.tools≤budget P fee pcUpper ∧
    4194304*solverBitScale P fee P.Lambda P.certificate.stages P.tools≤budget P fee pcUpper :=
  ⟨budget_solver P fee 0 pcUpper (original_initial_prices P fee).1,
    budget_solver P fee P.Lambda pcUpper (original_initial_prices P fee).2⟩

theorem budget_midpoint_solver (P : Parameters) (fee : ℚ) (pcUpper j : ℕ) (lower upper : MultiplierSolve)
    (inside : j≤P.bisectionBudget fee)
    (source : P.cachedMultiplierSearch P.endpointCache fee j=.bracket lower upper) :
    4194304*solverBitScale P fee ((lower.multiplier+upper.multiplier)/2)
      P.certificate.stages P.tools≤budget P fee pcUpper :=
  budget_solver P fee _ pcUpper (original_midpoint_price P fee j lower upper inside source)

theorem budget_scalar (P : Parameters) (fee : ℚ) (pcUpper : ℕ) :
    1+scalarValueBudget (originalScalarScale P fee)≤budget P fee pcUpper := by
  have scalar:=original_scalar_room_le_core P fee
  have room:=budget_core P fee pcUpper
  omega

theorem budget_pc_cell (P : Parameters) (fee : ℚ) (pcUpper value : ℕ) (inside : value≤pcUpper) :
    (Cell.natural value).bits≤budget P fee pcUpper := by
  have bits:=natBits_mono inside
  change 1+natBits value≤_
  unfold budget
  omega

theorem budget_pc (P : Parameters) (fee : ℚ) (pcUpper value : ℕ) (inside : value≤pcUpper) :
    natBits value≤budget P fee pcUpper := by
  have bits:=budget_pc_cell P fee pcUpper value inside
  change 1+natBits value≤_ at bits
  omega

theorem budget_runtime_control (P : Parameters) (fee : ℚ) (pcUpper origin : ℕ)
    (originBound : origin≤pcUpper)
    (lengthBound : (solverCalleeCode .liveHeap origin).length≤pcUpper) :
    runtimeControlRoom P origin≤budget P fee pcUpper := by
  have control:=runtime_control_room_le_core P fee origin
  have originBits:=natBits_mono originBound
  have lengthBits:=natBits_mono lengthBound
  unfold budget
  omega

theorem budget_control_context (P : Parameters) (fee : ℚ) (pcUpper origin : ℕ)
    (originBound : origin≤pcUpper)
    (lengthBound : (solverCalleeCode .liveHeap origin).length≤pcUpper) :
    SolverControlContext (controlAnchor (99+2*P.certificate.M)) (controlAnchorBits (99+2*P.certificate.M))
      (99+2*P.certificate.M) P.certificate.stages P.tools .liveHeap origin (budget P fee pcUpper) :=
  runtime_control_context P origin _ (budget_runtime_control P fee pcUpper origin originBound lengthBound)

end PDCompute.CoreGlobalBudget
