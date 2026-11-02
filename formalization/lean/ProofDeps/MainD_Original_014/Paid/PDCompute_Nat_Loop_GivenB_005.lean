module
public import Paid.PDCompute_Nat_Loop_CellCertificate_001
public import Paid.PDCompute_SolverFullCellBits_200

set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.NatLoop
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame PDCompute.NatControl
attribute [local irreducible] fullCellCode cellFieldsCode

/-- Construct the actual200 cell certificate at an ALREADY CHOSEN B.
The fixed control caller/incoming remain independent of every current
cell state. Dirty scratch stays at B, without adding another I+scalar. -/
theorem fullCellSameB_of_givenB (mode : ReaderMode) (rootOrigin matrixOrigin : ℕ) (input : List Cell)
    (P : Parameters) (fee penalty : ℚ) (caller : State) (incoming base n k source budget : ℕ)
    (context : SolverControlContext caller incoming base n k mode rootOrigin budget)
    (scalarRoom : 4194304*solverBitScale P fee penalty n k≤budget)
    (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget) :
    FullCellSameB mode rootOrigin matrixOrigin input P fee penalty base n k source budget:=by
  intro row column before values hpc header hbase hsource avoids hsourceValue hpenalty hk hfee last hrow hcolumn rowBound columnBound prior safe fetch
  have nonempty : 0<(fullCellCode mode (matrixCellPC matrixOrigin)).length:=by
    simp only [fullCellCode,List.length_append]
    have firstPositive : 0<rowPointerSetupCode.length:=by
      simp only [rowPointerSetupCode,List.length_append,PDLower.CalibrationCompute.storeSlot,List.length_cons,List.length_nil]
      omega
    omega
  have actualFetch : FetchesCode (solverLocatedProgram mode rootOrigin) before.pc (fullCellCode mode (matrixCellPC matrixOrigin)):=by
    rw [hpc]
    exact fetch
  have pcBits : natBits (matrixCellPC matrixOrigin+(fullCellCode mode (matrixCellPC matrixOrigin)).length)≤budget:=by
    simpa only [hpc] using SolverControlContext.block (before:=before) context (fullCellCode mode (matrixCellPC matrixOrigin)) nonempty actualFetch
  exact fullCell_trace_bits mode (solverLocatedProgram mode rootOrigin) input (matrixCellPC matrixOrigin) P fee penalty row column before base n k source budget values
    hpc header hbase hsource avoids hsourceValue hpenalty hk hfee last hrow hcolumn rowBound columnBound prior safe scalarRoom
    (fun value bounded=>context.natural value bounded) context.header indexBits sourceBits pcBits fetch

end PDCompute.NatLoop
