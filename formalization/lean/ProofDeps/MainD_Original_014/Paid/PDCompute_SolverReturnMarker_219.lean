module
public import Paid.PDCompute_SolverCallerGivenBudget_217
public import Common.ROOT_ActualTrace_Resources_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000
@[expose] public section
namespace PDCompute.Solver
open PaperProofs.Paid.Computation PDMenu.ComputeFrame

/-- A real final instruction boundary, on the very same callee list.
The marker is immediately before the real jumpIndirect.old. -/
def ReturnMarker (program : Program) (input : List Cell) (trace : List State)
    (after : State) (markerPC : ℕ) : Prop :=
  ∃ front : List State, ∃ marker : State,
    trace=front++[marker,after] ∧ marker.pc=markerPC ∧
    marker.register=after.register ∧ marker.heap=after.heap ∧
    marker.live=after.live ∧ marker.output=after.output ∧
    step program input marker=some after

theorem ReturnMarker.join_left {program : Program} {input : List Cell}
    {later : List State} {after : State} {markerPC : ℕ}
    (marked : ReturnMarker program input later after markerPC) (first : List State) :
    ReturnMarker program input (joinTrace first later) after markerPC := by
  obtain ⟨front,marker,equal,pc,register,heap,live,output,jump⟩:=marked
  refine ⟨first.dropLast++front,marker,?_,pc,register,heap,live,output,jump⟩
  simp only [joinTrace,equal,List.append_assoc]

theorem ReturnMarker.in_program {program other : Program} {input : List Cell}
    {trace : List State} {after : State} {markerPC : ℕ}
    (marked : ReturnMarker program input trace after markerPC)
    (chain : trace.IsChain (fun before later=>step other input before=some later)) :
    ReturnMarker other input trace after markerPC := by
  obtain ⟨front,marker,equal,pc,register,heap,live,output,_⟩:=marked
  refine ⟨front,marker,equal,pc,register,heap,live,output,?_⟩
  rw [equal] at chain
  have tail : [marker,after].IsChain (fun before later=>step other input before=some later) :=
    chain.right_of_append
  exact (List.isChain_cons_cons.mp tail).1

/-- Determinism transports the marker to an already constructed caller
fragment only after genuine first-return identity has been proved. -/
theorem ReturnMarker.identify {program : Program} {input : List Cell}
    {canonical actual : List State} {before after actualAfter : State} {markerPC returnPC : ℕ}
    (marked : ReturnMarker program input canonical after markerPC)
    (canonicalHead : canonical.head?=some before) (actualHead : actual.head?=some before)
    (canonicalChain : canonical.IsChain (fun first later=>step program input first=some later))
    (actualChain : actual.IsChain (fun first later=>step program input first=some later))
    (canonicalLast : canonical.getLast?=some after) (actualLast : actual.getLast?=some actualAfter)
    (canonicalPC : after.pc=returnPC) (actualPC : actualAfter.pc=returnPC)
    (canonicalProper : ∀ state∈canonical.dropLast,¬state.pc=returnPC)
    (actualProper : ∀ state∈actual.dropLast,¬state.pc=returnPC) :
    ReturnMarker program input actual actualAfter markerPC := by
  have same:=ROOT.ActualTrace.firstExit_unique_of_endpoints (fun state=>step program input state)
    (fun state=>state.pc=returnPC) before after actualAfter canonical actual
    canonicalHead actualHead canonicalChain actualChain canonicalLast actualLast
    canonicalPC actualPC canonicalProper actualProper
  rw [←same.1,←same.2]
  exact marked

/-- The physical table and address are present at the fixed marker,
before the real return to whichever caller continuation was saved. -/
theorem ReturnMarker.physical {program : Program} {input : List Cell}
    {trace : List State} {after : State} {markerPC address count : ℕ} {cells : List Cell}
    (marked : ReturnMarker program input trace after markerPC)
    (table : PDLower.CalibrationCompute.HeapList after address cells)
    (pointer : after.register .address=.natural address)
    (length : after.register .index=.natural count) :
    ∃ front : List State, ∃ marker : State,
      trace=front++[marker,after] ∧ marker.pc=markerPC ∧
      marker.register .address=.natural address ∧ marker.register .index=.natural count ∧
      PDLower.CalibrationCompute.HeapList marker address cells ∧ step program input marker=some after := by
  obtain ⟨front,marker,equal,pc,register,heap,live,_,jump⟩:=marked
  refine ⟨front,marker,equal,pc,by rw [register];exact pointer,by rw [register];exact length,?_,jump⟩
  apply PDLower.CalibrationCompute.HeapList.of_values
  · intro offset inside
    rw [live]
    exact table.1 offset inside
  · intro offset inside
    rw [heap]
    exact PDLower.CalibrationCompute.HeapList.value table offset inside

end PDCompute.Solver
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem return_trace_safe_marker (program : Program) (input : List Cell) (origin : ℕ) (before : State)
    (base returnPC start cursor budget : ℕ) (values : ℕ → Cell)
    (code : FetchesCode program origin (serializerCode origin)) (pc : before.pc=origin+222)
    (header : Header before base values) (hbase : before.register .fresh=.natural base)
    (hreturn : values 1=.natural returnPC) (hstart : values outputStart=.natural start)
    (hcursor : values outputCursor=.natural cursor)
    (safe : SafeBits before budget) (addressBits : ∀ slot<headerWords,1+natBits (base+slot) ≤ budget)
    (counter : natBits (before.pc+10) ≤ budget) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (serializerReturnResult before returnPC start cursor) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace ≤ 180 ∧
      Header (serializerReturnResult before returnPC start cursor) base values ∧
      (serializerReturnResult before returnPC start cursor).register .fresh=.natural base ∧
      (serializerReturnResult before returnPC start cursor).register .old=.natural returnPC ∧
      (serializerReturnResult before returnPC start cursor).register .address=.natural start ∧
      (serializerReturnResult before returnPC start cursor).register .index=.natural (cursor-start) ∧
      (serializerReturnResult before returnPC start cursor).pc=returnPC ∧
      (serializerReturnResult before returnPC start cursor).output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) ∧
      ReturnMarker program input trace (serializerReturnResult before returnPC start cursor) (origin+232) := by
  have fetchReturn : FetchesCode program before.pc (returnStraightCode++[.jumpIndirect .old]) := by
    rw [pc,←returnCode_decompose]
    exact fetch_return program origin code
  have run:=returnStraight_execute input before base returnPC start cursor values header hbase hreturn hstart hcursor
  obtain ⟨straightTrace,hh,hl,hchain,ht,invariant⟩:=linearExecute_trace_invariant program input returnStraightCode
    returnStraight_straight before _ fetchReturn.append_left run (fun state=>HeaderMemory before state base ∧ SafeBits state budget) (by
      intro count bound state execute
      have countBound : count ≤ 10:=bound
      exact ⟨returnStraight_prefix_memory input before state base count execute,
        returnStraight_prefix_safe input before state base returnPC start cursor budget count values header hbase hreturn hstart hcursor
          safe addressBits counter countBound execute⟩)
  have memory : ∀ state∈straightTrace,HeaderMemory before state base:=fun state member=>(invariant state member).1
  have bits : ∀ state∈straightTrace,SafeBits state budget:=fun state member=>(invariant state member).2
  let prepared:=returnStraightResult before returnPC start cursor
  have preparedPC : prepared.pc=origin+232 := by change before.pc+10=origin+232;omega
  have returnFetch : program[prepared.pc]?=some (.jumpIndirect .old) := by
    rw [preparedPC]
    exact indirect_return_fetch program origin code
  have jump : step program input prepared=some (serializerReturnResult before returnPC start cursor) := by
    simp only [step,returnFetch]
    simp [Instruction.execute,prepared,returnStraightResult,serializerReturnResult,Cell.nat?]
  have joined:=chain_append_control program input straightTrace prepared _ hchain hl jump
  have nonempty : straightTrace≠[] := by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at hh
  have lastMemory:=HeaderMemory.trace_last memory hl
  have preparedSafe : SafeBits prepared budget:=bits prepared (List.mem_of_getLast? hl)
  have returnBits : natBits returnPC ≤ budget:=by
    have represented:=preparedSafe.register .old
    have oldValue : prepared.register .old=.natural returnPC:=by simp [prepared,returnStraightResult]
    rw [oldValue] at represented
    change 1+natBits returnPC ≤ budget at represented
    omega
  have finalSafe : SafeBits (serializerReturnResult before returnPC start cursor) budget:=preparedSafe.withPC returnPC returnBits
  refine ⟨straightTrace++[_],?_,by simp,joined.1,by change time program straightTrace ≤ 165 at ht;omega,
    header,?_,?_,?_,?_,rfl,rfl,?_,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil straightTrace nonempty] using hh
  · simp [serializerReturnResult,returnStraightResult,hbase]
  · simp [serializerReturnResult,returnStraightResult]
  · simp [serializerReturnResult,returnStraightResult]
  · simp [serializerReturnResult,returnStraightResult]
  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact memory state earlier
    · have same : state=serializerReturnResult before returnPC start cursor := by simpa only [List.mem_singleton] using last
      subst state
      exact lastMemory

  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact bits state earlier
    · have same : state=serializerReturnResult before returnPC start cursor:=by simpa only [List.mem_singleton] using last
      subst state
      exact finalSafe

  · refine ⟨straightTrace.dropLast,prepared,?_,preparedPC,rfl,rfl,rfl,rfl,jump⟩
    have split:=List.dropLast_append_getLast? prepared (by rw [hl];simp [prepared])
    simpa only [List.append_assoc,List.singleton_append] using
      (congrArg (fun states : List State=>states++[serializerReturnResult before returnPC start cursor]) split).symm

end PDCompute.Pack

namespace PDCompute.Solver
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDMenu.ComputeFrame
open PDCompute.Pack

/-- Original233-op serializer at the SAME supplied global budget. Only
real finite new natural values and actual static code PCs need bounds;
arbitrary prior caller cells are carried without adding or doubling I. -/
theorem solver_pack_trace_same_budget_marker (program : Program) (input : List Cell) (origin : ℕ) (table : MenuTable)
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
      (∀ state∈trace,SafeBits state budget) ∧ ReturnMarker program input trace after (origin+232) := by
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
  obtain ⟨returnTrace,returnHead,returnLast,returnChain,returnTime,returnHeader,returnBase,returnOld,returnAddress,returnIndex,returnPCFact,returnOutput,returnMemory,returnBits,returnMarker⟩:=
    return_trace_safe_marker program input origin completed base returnPC (resultBase base n k)
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
      (joinTrace_invariant initTrace rowsTrace (fun state=>SafeBits state budget) initBits rowsBits) returnBits,returnMarker.join_left (joinTrace initTrace rowsTrace)⟩
  · have bound:=lastJoin.2.2.2
    nlinarith
  · rw [returnIndex,tableLength]
    congr 1
    omega


end PDCompute.Solver


