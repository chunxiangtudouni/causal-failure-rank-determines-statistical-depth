module

public import Paid.PDCompute_SolverFullCellBits_200
public import Paid.PDCompute_Nat_Resources_017

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame PDCompute.NatControl
attribute [local irreducible] fullCellCode cellFieldsCode solverCalleeCode

/-- Actual complete cell at the ONE original caller-carried budget.
All scalar, natural, source-cursor and actual located-PC premises of200
are discharged here, not retained as extra original implementation inputs. -/
theorem fullCell_trace_original_budget (mode : ReaderMode) (rootOrigin : ℕ) (input : List Cell)
    (origin : ℕ) (P : Parameters) (fee penalty : ℚ) (row column : ℕ)
    (caller before : State) (base n k source : ℕ) (values : ℕ → Cell)
    (callerFresh : caller.register .fresh=.natural base) (callerSource : caller.register .address=.natural source)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty) (hk : values 4=.natural k)
    (hfee : values 5=.rational fee) (last : values 6=.natural P.certificate.M)
    (hrow : values 19=.natural row) (hcolumn : values 20=.natural column) (rowBound : row ≤ n) (columnBound : column ≤ k)
    (prior : DensePrefix before base k (solverEntry P fee penalty k) (row*(k+1)+column))
    (safe : RootD27.Bits.SafeBits before (PDCompute.NatControl.originalControlBudget (PDCompute.Pack.initialBits caller) P fee penalty n k rootOrigin (solverCalleeCode mode rootOrigin).length))
    (fetch : FetchesCode (solverLocatedProgram mode rootOrigin) origin (fullCellCode mode origin)) :
    let budget:=PDCompute.NatControl.originalControlBudget (PDCompute.Pack.initialBits caller) P fee penalty n k rootOrigin (solverCalleeCode mode rootOrigin).length
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step (solverLocatedProgram mode rootOrigin) input first=some later) ∧
      time (solverLocatedProgram mode rootOrigin) trace ≤ 2500*(P.certificate.M+1)+23400 ∧ Header after base afterValues ∧
      DensePrefix after base k (solverEntry P fee penalty k) (row*(k+1)+column+1) ∧
      (∀ slot,MatrixInputSlot slot → afterValues slot=values slot) ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(fullCellCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,RegionMemory before state (cellRegion base headerWords ∪ cellRegion (cellBase base k row column) 6)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let budget:=originalControlBudget (PDCompute.Pack.initialBits caller) P fee penalty n k rootOrigin (solverCalleeCode mode rootOrigin).length
  have context:=controlContext_originalScale caller (PDCompute.Pack.initialBits caller) base n k rootOrigin (solverCalleeCode mode rootOrigin).length P fee penalty
    (PDCompute.Pack.initialBits_safe caller) callerFresh
  have scalarRoom : 4194304*solverBitScale P fee penalty n k≤budget := by unfold budget originalControlBudget;omega
  have indexBits : 1+natBits (P.certificate.M+1)≤budget := originalControlBudget_count _ P fee penalty n k rootOrigin _
  have sourceBits : 1+natBits (source+(1+2*(P.certificate.M+1)))≤budget := by
    simpa only [Nat.add_zero] using originalControlBudget_cursor caller (PDCompute.Pack.initialBits caller) source P fee penalty n k rootOrigin
      (solverCalleeCode mode rootOrigin).length (P.certificate.M+1) 0 (PDCompute.Pack.initialBits_safe caller) callerSource (le_refl _) (by decide)
  have nonempty : 0<(fullCellCode mode origin).length := by
    simp only [fullCellCode,List.length_append]
    have firstPositive : 0<rowPointerSetupCode.length := by
      simp only [rowPointerSetupCode,List.length_append,PDLower.CalibrationCompute.storeSlot,List.length_cons,List.length_nil]
      omega
    omega
  have actualFetch : FetchesCode (solverLocatedProgram mode rootOrigin) before.pc (fullCellCode mode origin) := by rw [hpc];exact fetch
  have pcBits : natBits (origin+(fullCellCode mode origin).length)≤budget := by
    simpa only [hpc] using SolverControlContext.block (before:=before) context (fullCellCode mode origin) nonempty actualFetch
  exact fullCell_trace_bits mode (solverLocatedProgram mode rootOrigin) input origin P fee penalty row column before base n k source budget values
    hpc header hbase hsource avoids hsourceValue hpenalty hk hfee last hrow hcolumn rowBound columnBound prior safe scalarRoom
    (fun value bound=>context.natural value bound) context.header indexBits sourceBits pcBits fetch

end PDCompute.Solver
