module
public import Paid.PDCompute_Nat_Loop_GivenB_005
public import Paid.PDCompute_Nat_Loop_Runtime_004
set_option autoImplicit false
set_option warningAsError true
@[expose] public section
namespace PDCompute.NatLoop
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame PDCompute.NatControl
/-- Whole original matrix at one GIVEN budget, from actual200 and the
frozen real-loop composition. No cell/row run or table oracle remains.
The fixed control caller is independent of the current actual state. -/
theorem matrix_trace_givenB (mode : ReaderMode) (rootOrigin : ℕ) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode (solverLocatedProgram mode rootOrigin) origin (matrixPackCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source : ℕ)
    (caller : State) (incoming budget : ℕ)
    (context : SolverControlContext caller incoming base n k mode rootOrigin budget)
    (scalarRoom : 4194304*solverBitScale P fee penalty n k≤budget)
    (indexBits : 1+natBits (P.certificate.M+1)≤budget)
    (sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (hfee : values 5=.rational fee)
    (last : values 6=.natural P.certificate.M)
    (safe : RootD27.Bits.SafeBits before budget) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step (solverLocatedProgram mode rootOrigin) input first=some later) ∧
      time (solverLocatedProgram mode rootOrigin) trace ≤ 30000*(P.certificate.M+1)*entryCount n k ∧ Header after base afterValues ∧
      DenseOriginalTable after P fee penalty base n k ∧ SavedInputValues values afterValues ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(matrixCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,RegionMemory before state (workspace base n k)) ∧
      peakCells trace ≤ workingCells before+62*entryCount n k ∧ peakOperandBits trace≤budget ∧
      ∀ state∈trace,RootD27.Bits.SafeBits state budget := by
  exact matrix_trace_resources mode rootOrigin input origin fetch P fee penalty before base n k source caller incoming budget context
    (fullCellSameB_of_givenB mode rootOrigin origin input P fee penalty caller incoming base n k source budget context scalarRoom indexBits sourceBits)
    values hpc header hbase hsource avoids hsourceValue hpenalty hn hk hfee last safe

end PDCompute.NatLoop
