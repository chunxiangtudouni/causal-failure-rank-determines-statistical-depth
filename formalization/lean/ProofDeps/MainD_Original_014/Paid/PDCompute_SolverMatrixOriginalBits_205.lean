module

public import Paid.PDCompute_SolverCellCertificate_204
public import Paid.PDCompute_Nat_Loop_Runtime_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame PDCompute.NatControl
attribute [local irreducible] fullCellCode cellFieldsCode matrixCode matrixPackCode solverCalleeCode

/-- COMPLETE original matrix resources. The fullcell internal callback
is CONSTRUCTED by the actual original200/203 implementation, so neither
a row nor a cell computation is assumed in this theorem. -/
theorem matrix_trace_original_budget (mode : ReaderMode) (rootOrigin : ℕ) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode (solverLocatedProgram mode rootOrigin) origin (matrixPackCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source : ℕ)
    (caller : State) (values : ℕ → Cell)
    (callerFresh : caller.register .fresh=.natural base) (callerSource : caller.register .address=.natural source)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (hfee : values 5=.rational fee)
    (last : values 6=.natural P.certificate.M)
    (safe : RootD27.Bits.SafeBits before (originalControlBudget (PDCompute.Pack.initialBits caller) P fee penalty n k rootOrigin (solverCalleeCode mode rootOrigin).length)) :
    let budget:=originalControlBudget (PDCompute.Pack.initialBits caller) P fee penalty n k rootOrigin (solverCalleeCode mode rootOrigin).length
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
  let budget:=originalControlBudget (PDCompute.Pack.initialBits caller) P fee penalty n k rootOrigin (solverCalleeCode mode rootOrigin).length
  have context:=controlContext_originalScale caller (PDCompute.Pack.initialBits caller) base n k rootOrigin (solverCalleeCode mode rootOrigin).length P fee penalty
    (PDCompute.Pack.initialBits_safe caller) callerFresh
  have cells:=fullCell_original_certificate mode rootOrigin origin input P fee penalty caller base n k source callerFresh callerSource
  exact PDCompute.NatLoop.matrix_trace_resources mode rootOrigin input origin fetch P fee penalty before base n k source caller (PDCompute.Pack.initialBits caller)
    budget context cells values hpc header hbase hsource avoids hsourceValue hpenalty hn hk hfee last safe

end PDCompute.Solver
