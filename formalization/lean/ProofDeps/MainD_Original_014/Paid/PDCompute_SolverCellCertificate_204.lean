module

public import Paid.PDCompute_SolverCellOriginalBudget_203
public import Paid.PDCompute_Nat_Loop_CellCertificate_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame PDCompute.NatControl
attribute [local irreducible] fullCellCode cellFieldsCode solverCalleeCode

/-- Construct the internal matrix-loop certificate from the COMPLETE
actual original cell implementation203. No cell oracle remains. -/
theorem fullCell_original_certificate (mode : ReaderMode) (rootOrigin matrixOrigin : ℕ) (input : List Cell)
    (P : Parameters) (fee penalty : ℚ) (caller : State) (base n k source : ℕ)
    (callerFresh : caller.register .fresh=.natural base) (callerSource : caller.register .address=.natural source) :
    PDCompute.NatLoop.FullCellSameB mode rootOrigin matrixOrigin input P fee penalty base n k source
      (originalControlBudget (PDCompute.Pack.initialBits caller) P fee penalty n k rootOrigin (solverCalleeCode mode rootOrigin).length) := by
  intro row column before values hpc header fresh hsource avoids hsourceValue hpenalty hk hfee last hrow hcolumn rowBound columnBound prior safe fetch
  exact fullCell_trace_original_budget mode rootOrigin input (matrixCellPC matrixOrigin) P fee penalty row column caller before base n k source values
    callerFresh callerSource hpc header fresh hsource avoids hsourceValue hpenalty hk hfee last hrow hcolumn rowBound columnBound prior safe fetch

end PDCompute.Solver
