module

public import Paid.PDCompute_SolverHeaderLoads_038

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (loadSlotResult storeSlotResult)

/-- Projection lemmas keep callers from unfolding the full updated heap,
register function, and original parameter-dependent endpoint expression. -/
theorem endpointHeaderResult_fresh (before : State) (base address : ℕ) (error charge : ℚ) :
    (endpointHeaderResult before base address error charge).register .fresh=before.register .fresh := by
  simp only [endpointHeaderResult,storeSlotResult,endpointPairResult]
  rfl

theorem endpointHeaderResult_pc (before : State) (base address : ℕ) (error charge : ℚ) :
    (endpointHeaderResult before base address error charge).pc=before.pc+10 := by
  change before.pc+4+3+3=before.pc+10
  omega

theorem endpointHeaderResult_output (before : State) (base address : ℕ) (error charge : ℚ) :
    (endpointHeaderResult before base address error charge).output=before.output := rfl

theorem loadSlotResult_pc (before : State) (base slot : ℕ) (target : Register) :
    (loadSlotResult before base slot target).pc=before.pc+3 := rfl

theorem loadSlotResult_output (before : State) (base slot : ℕ) (target : Register) :
    (loadSlotResult before base slot target).output=before.output := rfl

end PDCompute.Solver
