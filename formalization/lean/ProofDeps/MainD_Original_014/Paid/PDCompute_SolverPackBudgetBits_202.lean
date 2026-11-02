module
public import Paid.PDCompute_SolverPackInitBits_201
public import Paid.PDCompute_Pack_RowsBits_091
public import Paid.PDCompute_Pack_ReturnBits_093
public import Paid.PDCompute_Pack_Run_052

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
@[expose] public section
namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Pack

/-- Original233-op serializer at the SAME supplied global budget. Only
real finite new natural values and actual static code PCs need bounds;
arbitrary prior caller cells are carried without adding or doubling I. -/
theorem solver_pack_trace_same_budget (program : Program) (input : List Cell) (origin : ℕ) (table : MenuTable)
    (before : State) (base n k returnPC budget : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hn : values 3=.natural n) (hk : values 4=.natural k) (hreturn : values 1=.natural returnPC)
    (rows : table.size=n+1) (columns : ∀ row∈table,row.size=k+1)
    (dense : PDLower.CalibrationCompute.HeapList before (tableBase base) (denseRows table.toList))
    (safe : SafeBits before budget) (naturalBound : ∀ value≤naturalCap base n k,1+natBits value≤budget)
    (pcBits : ∀ counter≤origin+233,natBits counter≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 4096*(n+1)*(k+1) ∧
      PDLower.CalibrationCompute.HeapList after (resultBase base n k) (encodeTable table) ∧
      after.register .fresh=.natural base ∧ after.register .old=.natural returnPC ∧
      after.register .address=.natural (resultBase base n k) ∧ after.register .index=.natural (encodeTable table).length ∧
      after.pc=returnPC ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (writeRegion base n k)) ∧
      (∀ state∈trace,SafeBits state budget) := by
  have addressBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot) ≤ budget:=
    naturalBound _ (naturalCap_header_address base n k slot inside)
  have tableLength : (encodeTable table).length=1+(encodedRows table.toList).length:=by rw [encodeTable_eq];simp only [List.length_cons];omega
  have capacity:=encoding_capacity table n k rows columns
  have width : ∀ row∈table.toList,row.size=k+1:=by simpa only [Array.mem_toList_iff] using columns
  have rowCount : table.toList.length=n+1 := by simpa only [Array.length_toList] using rows
  have denseLength : (denseRows table.toList).length=6*(n+1)*(k+1) := by
    rw [denseRows_length table.toList (k+1) width,rowCount]
  obtain ⟨initTrace,initialized,initHead,initLast,initChain,initTime,initHeader,tableWord,initBase,initPC,initOutput,initMemory,initBits⟩:=
    solver_pack_initialize_trace_same_budget program input origin before base n k budget values code pc header hbase hn hk safe naturalBound pcBits
  let initValues:=initializedValues values base n k
  have initSource : initValues sourceCursor=.natural (tableBase base) := by
    simp [initValues,initializedValues,initializeHeaderValues,pointerValues,sourceCursor,outputCursor,tableBase,headerWords]
  have initPointer : initValues outputCursor=.natural (resultBase base n k+1) := by
    simp only [initValues,initializedValues,Function.update_self]
  have initCount : initValues rowRemaining=.natural table.toList.length := by
    rw [rowCount]
    simp [initValues,initializedValues,initializeHeaderValues,pointerValues,counterValues,
      rowRemaining,columnsPerRow,sourceCursor,outputCursor,outputStart]
  have initColumns : initValues columnsPerRow=.natural (k+1) := by
    simp [initValues,initializedValues,initializeHeaderValues,pointerValues,counterValues,
      rowRemaining,columnsPerRow,sourceCursor,outputCursor,outputStart]
  have initialDenseOutside : ∀ offset<(denseRows table.toList).length,tableBase base+offset∉writeRegion base n k := by
    intro offset bound
    rw [denseLength] at bound
    rw [Nat.mul_assoc] at bound
    intro member
    rcases Finset.mem_union.mp member with headerMember|resultMember
    · rw [headerRegion_eq,mem_cellRegion_iff] at headerMember
      unfold tableBase at headerMember
      omega
    · rw [resultRegion_eq,mem_cellRegion_iff] at resultMember
      unfold resultBase PDCompute.Solver.entryCount entryWords at resultMember
      omega
  have initFinal:=RegionMemory.trace_last initMemory initLast
  have initDense : PDLower.CalibrationCompute.HeapList initialized (tableBase base) (denseRows table.toList):=dense.regionMemory initFinal initialDenseOutside
  have sourceUpper : tableBase base+6*table.toList.length*(k+1) ≤ resultBase base n k := by
    rw [rowCount]
    unfold resultBase entryWords PDCompute.Solver.entryCount
    rw [Nat.mul_assoc]
  have initializedSafe : SafeBits initialized budget:=initBits initialized (List.mem_of_getLast? initLast)
  have rowsUpper : resultBase base n k+1+(encodedRows table.toList).length ≤ naturalCap base n k:=by
    rw [←naturalCap_result_end]
    rw [tableLength] at capacity
    omega
  obtain ⟨rowsTrace,completed,finalValues,rowsHead,rowsLast,rowsChain,rowsTime,completedHeader,rowsHeap,completedSource,completedPointer,completedCount,completedStable,completedBase,completedPC,completedOutput,rowsMemory,rowsBits⟩:=
    rows_trace_safe program input origin table.toList initialized base (tableBase base) (resultBase base n k+1) (k+1) n k budget initValues
      code initPC initHeader initBase initSource initPointer initCount initColumns width initDense
      (le_refl _) sourceUpper (by omega) rowsUpper initializedSafe naturalBound pcBits
  have completedReturn : finalValues 1=.natural returnPC := by
    rw [completedStable 1 returnPC_tableStable]
    simpa only [initValues,initializedValues,Function.update_of_ne (by decide : (1:ℕ)≠outputCursor),
      initializeHeaderValues_arguments values base n k 1 (by decide)] using hreturn
  have completedStart : finalValues outputStart=.natural (resultBase base n k) := by
    rw [completedStable outputStart outputStart_tableStable]
    simp [initValues,initializedValues,initializeHeaderValues,pointerValues,outputStart,outputCursor,sourceCursor]
  have completedSafe : SafeBits completed budget:=rowsBits completed (List.mem_of_getLast? rowsLast)
  obtain ⟨returnTrace,returnHead,returnLast,returnChain,returnTime,returnHeader,returnBase,returnOld,returnAddress,returnIndex,returnPCFact,returnOutput,returnMemory,returnBits⟩:=
    return_trace_safe program input origin completed base returnPC (resultBase base n k)
      (resultBase base n k+1+(encodedRows table.toList).length) budget finalValues code completedPC completedHeader completedBase
      completedReturn completedStart completedPointer completedSafe addressBits (pcBits _ (by rw [completedPC];omega))
  let after:=serializerReturnResult completed returnPC (resultBase base n k) (resultBase base n k+1+(encodedRows table.toList).length)
  have rowsFinal:=RegionMemory.trace_last rowsMemory rowsLast
  have keptWord : PDLower.CalibrationCompute.HeapList completed (resultBase base n k) [.natural (n+1)]:=tableWord.regionMemory rowsFinal (by
    intro offset bound
    exact localRegion_outside_earlier base (resultBase base n k) 1 (encodedRows table.toList).length
      (result_after_header base n k) offset bound)
  have completedTable : PDLower.CalibrationCompute.HeapList completed (resultBase base n k) (encodeTable table) := by
    rw [encodeTable_eq,rows]
    exact keptWord.append rowsHeap
  have returnFinal:=HeaderMemory.trace_last returnMemory returnLast
  have finalTable : PDLower.CalibrationCompute.HeapList after (resultBase base n k) (encodeTable table):=completedTable.headerMemory returnFinal (by
    intro offset _bound
    exact Or.inr (by have lower:=result_after_header base n k;omega))
  have rowsRegion : ∀ state∈rowsTrace,RegionMemory initialized state (writeRegion base n k) := by
    intro state member
    apply (rowsMemory state member).enlarge
    apply localRegion_write_subset base n k (resultBase base n k+1) (encodedRows table.toList).length (by omega)
    rw [tableLength] at capacity
    omega
  have returnRegion : ∀ state∈returnTrace,RegionMemory completed state (writeRegion base n k):=
    fun state member=>headerMemory_region base n k (returnMemory state member)
  have firstJoin:=joinTrace_spec program input initTrace rowsTrace before initialized completed 1020
    ((n+1)*(1830*(k+1)+645)+75) initHead initLast rowsHead rowsLast initChain rowsChain initTime
    (by simpa only [rowCount] using rowsTime)
  have lastJoin:=joinTrace_spec program input (joinTrace initTrace rowsTrace) returnTrace before completed after
    (1020+((n+1)*(1830*(k+1)+645)+75)) 180 firstJoin.1 firstJoin.2.1 returnHead returnLast
    firstJoin.2.2.1 returnChain firstJoin.2.2.2 returnTime
  refine ⟨joinTrace (joinTrace initTrace rowsTrace) returnTrace,after,lastJoin.1,lastJoin.2.1,lastJoin.2.2.1,?_,
    finalTable,returnBase,returnOld,returnAddress,?_,returnPCFact,returnOutput.trans (completedOutput.trans initOutput),
    RegionMemory.join_trace (joinTrace initTrace rowsTrace) returnTrace before completed _ firstJoin.2.1
      (RegionMemory.join_trace initTrace rowsTrace before initialized _ initLast initMemory rowsRegion) returnRegion,
    joinTrace_invariant (joinTrace initTrace rowsTrace) returnTrace (fun state=>SafeBits state budget)
      (joinTrace_invariant initTrace rowsTrace (fun state=>SafeBits state budget) initBits rowsBits) returnBits⟩
  · have bound:=lastJoin.2.2.2
    nlinarith
  · rw [returnIndex,tableLength]
    congr 1
    omega


end PDCompute.Solver
