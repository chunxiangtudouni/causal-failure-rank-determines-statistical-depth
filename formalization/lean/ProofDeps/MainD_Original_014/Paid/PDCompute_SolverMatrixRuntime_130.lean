module

public import Paid.PDCompute_SolverRowLoop_129
public import Paid.PDLower_CalibrationCompute_Space_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 900000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode

theorem matrix_runtime_time_le (P : Parameters) (n k : ℕ) :
    matrixRowCost P k*(n+1)+465 ≤ 30000*(P.certificate.M+1)*entryCount n k := by
  let product:=(P.certificate.M+1)*entryCount n k
  have entriesPositive : 0 < entryCount n k := by unfold entryCount; exact Nat.mul_pos (Nat.succ_pos _) (Nat.succ_pos _)
  have entriesBound : entryCount n k ≤ product := by
    dsimp only [product]
    nlinarith [Nat.zero_le (P.certificate.M*entryCount n k)]
  have nBound : n+1 ≤ entryCount n k := by
    unfold entryCount
    nlinarith [Nat.zero_le ((n+1)*k)]
  have oneBound : 1 ≤ product := (Nat.succ_le_of_lt entriesPositive).trans entriesBound
  have stagesBound : n+1 ≤ product := nBound.trans entriesBound
  calc
    _ = 2500*product+23685*entryCount n k+750*(n+1)+465 := by
      unfold matrixRowCost matrixStepCost product entryCount
      ring
    _ ≤ 2500*product+23685*product+750*product+465*product := by omega
    _ = 27400*product := by ring
    _ ≤ 30000*product := Nat.mul_le_mul_right _ (by decide : 27400 ≤ 30000)
    _ = _ := by dsimp only [product]; ring

/-- The COMPLETE actual dense matrix from original live Header inputs.
Both row/tool loops and every original cell are executed; the initial
dense workspace may contain arbitrary old live data. -/
theorem matrix_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode program origin (matrixCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (hpenalty : values 2=.rational penalty)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (hfee : values 5=.rational fee)
    (last : values 6=.natural P.certificate.M) :
    ∃ trace : List State, ∃ after : State, ∃ afterValues : ℕ → Cell,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 30000*(P.certificate.M+1)*entryCount n k ∧ Header after base afterValues ∧
      DenseOriginalTable after P fee penalty base n k ∧ SavedInputValues values afterValues ∧
      after.register .fresh=.natural base ∧ after.pc=origin+(matrixCode mode origin).length ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state ∈ trace,RegionMemory before state (workspace base n k)) ∧
      peakCells trace ≤ workingCells before+62*entryCount n k := by
  let rowValues:=Function.update values 19 (.natural 0)
  have initFetch : FetchesCode program before.pc (headerCode [.constant 19 (.natural 0)]) := by
    rw [hpc]
    exact matrix_row_init_fetch mode program origin fetch
  obtain ⟨initTrace,initialized,initHead,initLast,initChain,initTime,initializedHeader,initializedBase,initializedPC,
    initFrame,initOutput,initMemory⟩:=
    headerCode_trace_memory [.constant 19 (.natural 0)] program input before base n k values rowValues
      (by intro command member; have same:=List.mem_singleton.mp member; subst command; dsimp only [HeaderCommand.Valid,headerWords]; decide)
      header hbase rfl initFetch
  have initBound : time program initTrace ≤ 330 := initTime
  have atRows : initialized.pc=matrixRowTestPC origin := by rw [initializedPC,hpc]; rfl
  have initializedContents : MatrixRowContents P rowValues fee penalty n k source 0 :=
    ⟨hsourceValue,hpenalty,hn,hk,hfee,last,rfl⟩
  have initializedSource:=EndpointSource.frame_of_avoids mode input P source base n k before initialized hsource avoids initFrame
  have empty : DensePrefix initialized base k (solverEntry P fee penalty k) (0*(k+1)) := by
    simpa only [Nat.zero_mul] using DensePrefix.empty initialized base k (solverEntry P fee penalty k)
  obtain ⟨rowsTrace,after,afterValues,rowsHead,rowsLast,rowsChain,rowsTime,afterHeader,_,complete,rowsInputs,
    afterBase,afterPC,rowsFrame,rowsOutput,rowsMemory⟩:=matrix_rows_trace_memory mode program input origin fetch P fee penalty
      base n k source (n+1) avoids initialized rowValues 0 (Nat.zero_add _) atRows initializedHeader initializedContents initializedBase initializedSource empty
  have joined:=joinTrace_spec program input initTrace rowsTrace before initialized after 330 (matrixRowCost P k*(n+1)+135)
    initHead initLast rowsHead rowsLast initChain rowsChain initBound rowsTime
  have allMemory : ∀ state ∈ joinTrace initTrace rowsTrace,RegionMemory before state (workspace base n k) :=
    RegionMemory.join_trace initTrace rowsTrace before initialized _ initLast
      (fun state member => (initMemory state member).region _ (headerRegion_subset_workspace base n k)) rowsMemory
  refine ⟨joinTrace initTrace rowsTrace,after,afterValues,joined.1,joined.2.1,joined.2.2.1,?_,afterHeader,
    DensePrefix.original_table after P fee penalty base n k complete,
    (SavedInputValues.update values 19 _ (by decide)).trans rowsInputs,afterBase,?_,
    initFrame.trans rowsFrame,rowsOutput.trans initOutput,allMemory,?_⟩
  · calc
      _ ≤ 330+(matrixRowCost P k*(n+1)+135) := joined.2.2.2
      _ = matrixRowCost P k*(n+1)+465 := by ring
      _ ≤ _ := matrix_runtime_time_le P n k
  · exact afterPC.trans (matrixCode_end mode origin).symm
  · exact PDLower.CalibrationCompute.peakCells_le_of_forall _ _
      (fun state member => (allMemory state member).workspace_workingCells)

end PDCompute.Solver
