module
public import Paid.PDCompute_Nat_Loop_Rows_003
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000
@[expose] public section
namespace PDCompute.NatLoop
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame PDCompute.NatControl
attribute [local irreducible] fullCellCode

/-- Original130 actual matrix and every-prefix physical/numeric resources on ONE composed witness; fullcell certificate is explicitly internal. -/
theorem matrix_trace_resources (mode : ReaderMode) (rootOrigin : ℕ) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode (solverLocatedProgram mode rootOrigin) origin (matrixPackCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source : ℕ)
    (caller : State) (incoming budget : ℕ)
    (context : SolverControlContext caller incoming base n k mode rootOrigin budget)
    (cells : FullCellSameB mode rootOrigin origin input P fee penalty base n k source budget) (values : ℕ → Cell)
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
  let program:=solverLocatedProgram mode rootOrigin
  let rowValues:=Function.update values 19 (.natural 0)
  obtain ⟨initTrace,initialized,initHead,initLast,initChain,initTime,initializedHeader,initializedBase,initializedPC,
    initFrame,initOutput,initResources⟩:=
    matrix_row_initialize_trace_context mode rootOrigin origin input caller before incoming base n k budget values
      context header hbase safe hpc fetch
  have initMemory : ∀ state∈initTrace,HeaderMemory before state base:=fun state member=>(initResources state member).1
  have initBits : ∀ state∈initTrace,RootD27.Bits.SafeBits state budget:=fun state member=>(initResources state member).2
  have initBound : time program initTrace ≤ 330 := initTime
  have atRows : initialized.pc=matrixRowTestPC origin := initializedPC
  have initializedContents : MatrixRowContents P rowValues fee penalty n k source 0 :=
    ⟨hsourceValue,hpenalty,hn,hk,hfee,last,rfl⟩
  have initializedSource:=EndpointSource.frame_of_avoids mode input P source base n k before initialized hsource avoids initFrame
  have empty : DensePrefix initialized base k (solverEntry P fee penalty k) (0*(k+1)) := by
    simpa only [Nat.zero_mul] using DensePrefix.empty initialized base k (solverEntry P fee penalty k)
  obtain ⟨rowsTrace,after,afterValues,rowsHead,rowsLast,rowsChain,rowsTime,afterHeader,_,complete,rowsInputs,
    afterBase,afterPC,rowsFrame,rowsOutput,rowsMemory,rowsBits⟩:=matrix_rows_trace_resources mode rootOrigin input origin fetch P fee penalty
      base n k source (n+1) caller incoming budget context cells avoids initialized rowValues 0 (Nat.zero_add _) atRows initializedHeader initializedContents initializedBase initializedSource empty (initBits initialized (List.mem_of_getLast? initLast))
  have joined:=joinTrace_spec program input initTrace rowsTrace before initialized after 330 (matrixRowCost P k*(n+1)+135)
    initHead initLast rowsHead rowsLast initChain rowsChain initBound rowsTime
  have allMemory : ∀ state ∈ joinTrace initTrace rowsTrace,RegionMemory before state (workspace base n k) :=
    RegionMemory.join_trace initTrace rowsTrace before initialized _ initLast
      (fun state member => (initMemory state member).region _ (headerRegion_subset_workspace base n k)) rowsMemory
  have allBits:=PDCompute.Pack.joinTrace_invariant initTrace rowsTrace (fun state=>RootD27.Bits.SafeBits state budget) initBits rowsBits
  refine ⟨joinTrace initTrace rowsTrace,after,afterValues,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,
    DensePrefix.original_table after P fee penalty base n k complete,
    (SavedInputValues.update values 19 _ (by decide)).trans rowsInputs,afterBase,?_,
    initFrame.trans rowsFrame,rowsOutput.trans initOutput,allMemory,?_,PDCompute.Pack.safeBits_peak _ budget allBits,allBits⟩
  · calc
      _ ≤ 330+(matrixRowCost P k*(n+1)+135) := joined.2.2.2
      _ = matrixRowCost P k*(n+1)+465 := by ring
      _ ≤ _ := matrix_runtime_time_le P n k
  · exact afterPC.trans (matrixCode_end mode origin).symm
  · exact PDLower.CalibrationCompute.peakCells_le_of_forall _ _
      (fun state member => (allMemory state member).workspace_workingCells)

end PDCompute.NatLoop
