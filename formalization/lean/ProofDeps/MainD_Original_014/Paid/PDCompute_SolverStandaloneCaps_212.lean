module

public import Paid.PDCompute_SolverStandaloneBudget_211

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame PDCompute.NatControl
attribute [local irreducible] fullCellCode cellFieldsCode matrixCode matrixPackCode solverCalleeCode solverOutputOrigin

theorem solver_loader_budget_uniform (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    solverLoaderBudget P fee penalty n k≤solverStandaloneBitConstant*solverBitScale P fee penalty n k := by
  have positive:=solverBitScale_positive P fee penalty n k
  have staticBound:=Nat.mul_le_mul_left (natBits solverOutputOrigin+32) positive
  simp only [Nat.mul_one] at staticBound
  unfold solverLoaderBudget solverStandaloneBitConstant
  nlinarith

theorem solver_standalone_pointer_bits (P : Parameters) (fee penalty : ℚ) (n k : ℕ) :
    1+natBits (resultBase 0 n k+(encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length)≤
      solverStandaloneBudget P fee penalty n k := by
  let loaded:=solverInputResult initial solverOutputOrigin n k fee penalty
  have context:=controlContext_originalScale loaded (PDCompute.Pack.initialBits loaded) 0 n k 11
    (solverCalleeCode .inputROM 11).length P fee penalty (PDCompute.Pack.initialBits_safe loaded) rfl
  have capacity:=PDCompute.Pack.encoding_capacity (P.cachedSolveMenuTable P.endpointCache fee penalty k n) n k
    (originalTable_rows P fee penalty n k) (originalTable_columns P fee penalty n k)
  have actual:=context.natural (resultBase 0 n k+(encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length) (by
    rw [←PDCompute.Pack.naturalCap_result_end 0 n k]
    omega)
  exact actual

end PDCompute.Solver
