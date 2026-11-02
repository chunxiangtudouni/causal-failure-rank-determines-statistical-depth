module

public import Paid.PDCompute_SolverPackBridge_141

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

attribute [local irreducible] fullCellCode matrixCode

def matrixPackCode (mode : ReaderMode) (origin : ℕ) : List Instruction :=
  matrixCode mode origin++PDCompute.Pack.serializerCode (origin+(matrixCode mode origin).length)

/-- One actual dense-DP plus original4/6-encoding trace. It executes
all rows/cells, then the actual233-op serializer and indirect return.
Old live cells inside the workspace are allowed throughout. -/
theorem matrix_pack_trace (mode : ReaderMode) (program : Program) (input : List Cell)
    (origin : ℕ) (fetch : FetchesCode program origin (matrixPackCode mode origin))
    (P : Parameters) (fee penalty : ℚ) (before : State) (base n k source returnPC : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin) (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hsource : EndpointSource mode input P source before) (avoids : EndpointAvoids mode P source base n k)
    (hsourceValue : values 0=.natural source) (savedReturn : values 1=.natural returnPC)
    (hpenalty : values 2=.rational penalty) (hn : values 3=.natural n) (hk : values 4=.natural k)
    (hfee : values 5=.rational fee) (last : values 6=.natural P.certificate.M) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace ≤ 35000*(P.certificate.M+1)*entryCount n k ∧
      PDLower.CalibrationCompute.HeapList after (resultBase base n k)
        (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural (resultBase base n k) ∧
      after.register .index=.natural (encodeTable (P.cachedSolveMenuTable P.endpointCache fee penalty k n)).length ∧
      after.pc=returnPC ∧ after.output=before.output ∧ Frame before after base n k ∧
      (∀ state∈trace,RegionMemory before state (workspace base n k)) ∧
      peakCells trace ≤ workingCells before+62*entryCount n k := by
  have matrixFetch : FetchesCode program origin (matrixCode mode origin) := fetch.append_left
  have packFetch : FetchesCode program (origin+(matrixCode mode origin).length)
      (PDCompute.Pack.serializerCode (origin+(matrixCode mode origin).length)) := fetch.append_right
  obtain ⟨matrix,middle,middleValues,matrixHead,matrixLast,matrixChain,matrixTime,middleHeader,dense,inputs,
    middleBase,middlePC,_,_,matrixMemory,_⟩:=matrix_trace_memory mode program input origin matrixFetch P fee penalty before base n k source values
      hpc header hbase hsource avoids hsourceValue hpenalty hn hk hfee last
  have middleN : middleValues 3=.natural n := (inputs 3 (by decide)).trans hn
  have middleK : middleValues 4=.natural k := (inputs 4 (by decide)).trans hk
  have middleReturn : middleValues 1=.natural returnPC := (inputs 1 (by decide)).trans savedReturn
  obtain ⟨packed,after,packHead,packLast,packChain,packTime,heap,afterBase,afterOld,afterAddress,afterIndex,
    afterPC,_,_,packMemory⟩:=PDCompute.Pack.serializer_cells_trace program input (origin+(matrixCode mode origin).length)
      (P.cachedSolveMenuTable P.endpointCache fee penalty k n) middle base n k returnPC middleValues packFetch middlePC middleHeader
      middleBase middleN middleK middleReturn (originalTable_rows P fee penalty n k) (originalTable_columns P fee penalty n k) dense.pack_cells
  have joined:=joinTrace_spec program input matrix packed before middle after
    (30000*(P.certificate.M+1)*entryCount n k) (4096*(n+1)*(k+1))
    matrixHead matrixLast packHead packLast matrixChain packChain matrixTime packTime
  have allMemory:=RegionMemory.join_trace matrix packed before middle (workspace base n k) matrixLast matrixMemory
    (fun state member=>(packMemory state member).enlarge (pack_writeRegion_subset_workspace base n k))
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  refine ⟨joinTrace matrix packed,after,joined.1,joined.2.1,joined.2.2.1,?_,heap,afterBase,afterOld,afterAddress,
    afterIndex,afterPC,finalMemory.2.2.2,finalMemory.frame (Finset.Subset.refl _),allMemory,?_⟩
  · calc
      _ ≤ 30000*(P.certificate.M+1)*entryCount n k+4096*(n+1)*(k+1) := joined.2.2.2
      _ ≤ 35000*(P.certificate.M+1)*entryCount n k := by unfold entryCount; nlinarith [Nat.zero_le (P.certificate.M*((n+1)*(k+1)))]
  · exact PDLower.CalibrationCompute.peakCells_le_of_forall _ _
      (fun state member=>(allMemory state member).workspace_workingCells)

end PDCompute.Solver
