module

public import Paid.PDCompute_SolverPrologue_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (storeSlotResult writeCell)

def savedArguments (before : State) : List Cell :=
  [before.register .address,before.register .old,before.register .total,
    before.register .index,before.register .value,before.register .flag]

theorem solverPrologue_arguments (before : State) (base : ℕ) :
    HeapList (solverPrologueResult before base) base (savedArguments before) := by
  change PDLower.CalibrationCompute.HeapList _ _ _
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro index inside
    change index < 6 at inside
    have hcases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 := by omega
    rcases hcases with h|h|h|h|h|h <;> subst index <;>
      simp [solverPrologueResult,storeSlotResult,writeCell]
  · intro index inside
    change index < 6 at inside
    have hcases : index=0 ∨ index=1 ∨ index=2 ∨ index=3 ∨ index=4 ∨ index=5 := by omega
    rcases hcases with h|h|h|h|h|h <;> subst index <;>
      simp [solverPrologueResult,storeSlotResult,writeCell,savedArguments]

end PDCompute.Solver
