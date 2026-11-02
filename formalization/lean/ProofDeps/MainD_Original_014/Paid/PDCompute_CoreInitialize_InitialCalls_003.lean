module
public import Paid.PDCompute_CoreInitialize_SolvedBuffer_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
@[expose] public section

namespace PDCompute.CoreInitialize
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDROC.DataBits
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList loadSlot loadSlotResult)
open RootD27.Core RootD27.Bits PDLower.CoreRuntimeNumeric

/-- A physical heap penalty load and the complete original solve/retain
call are ONE actual trace. There is no penalty-register input premise. -/
theorem header_solved_resources (P : Parameters) (fee penalty : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (values : ℕ→Cell) (upper : Bool) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0)
    (lambdaValue : values (multiplierSlot upper)=.rational penalty)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (fetched : FetchesCode program before.pc (headerSolvedCallCode before.pc labels.solveEntry upper))
    (belowEntry : before.pc+72<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1)))
    (budget : ℕ) (safe : SafeBits before budget) (small : 7≤budget)
    (limitBits : (Cell.natural ((99+2*P.certificate.M)+78*PDCompute.Solver.entryCount P.certificate.stages P.tools)).bits≤budget)
    (endBits : (Cell.natural (before.pc+72)).bits≤budget)
    (controlRoom : runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (scalarRoom : 4194304*solverBitScale P fee penalty P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=commonSolverMarkerPC labels) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤42000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=before.pc+72 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ SolvedBuffer P fee penalty upper after ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+78*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      (∀ state∈trace,RegionMemory before state (solvedBufferCallRegion P fee penalty upper)) ∧
      actualSolveRequests labels trace=[penalty] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      (∀ state∈trace,SafeBits state budget) ∧ SolverCallRefinement program labels P fee 40000 trace ∧
      (∀ state∈trace,ClosedPC labels before.pc (before.pc+72) state) ∧
      (∀ state∈trace.dropLast,ProperPC labels before.pc (before.pc+72) state) := by
  let loaded:=loadSlotResult before 0 (multiplierSlot upper) .total
  let region:=solvedBufferCallRegion P fee penalty upper
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  change FetchesCode program before.pc
    (loadSlot (multiplierSlot upper) .total++solvedBufferCallCode (before.pc+3) labels.solveEntry upper) at fetched
  have inside : multiplierSlot upper<headerWords:=by cases upper <;> decide
  obtain ⟨load,lh,ll,lc,lt,penaltyLoaded,freshLoaded,loadMemory,loadScope,loadSafe,loadProper⟩:=
    penalty_load_resources program input before values (multiplierSlot upper) penalty budget header inside fresh
      lambdaValue safe small
      ((natBits_mono (by omega : before.pc+3≤before.pc+72)).trans (by change 1+natBits (before.pc+72)≤budget at endBits;omega))
      fetched.append_left
  have loadedPC : loaded.pc=before.pc+3:=rfl
  have callFetch : FetchesCode program loaded.pc (solvedBufferCallCode loaded.pc labels.solveEntry upper) := by
    change FetchesCode program (before.pc+3) (solvedBufferCallCode (before.pc+3) labels.solveEntry upper)
    exact fetched.append_right
  obtain ⟨call,after,ch,cl,cc,ct,afterPC,afterFresh,afterHeader,represented,preparedAfter,cacheAfter,
    output,callPeak,callMemory,requests,count,callSafe,callCalls,callScope,callProper⟩:=
    solved_buffer_resources P fee penalty program labels input loaded values upper
      (header.loadSlot_preserves (multiplierSlot upper) .total) lambdaValue penaltyLoaded prepared stored
      callFetch (by omega) stubFetch bodyFetch
      budget (loadSafe loaded (List.mem_of_getLast? ll)) small limitBits
      (by simpa only [loadedPC,Nat.add_assoc] using endBits) controlRoom scalarRoom markerLabel
  change peakCells call≤workingCells before+78*entries at callPeak
  have joined:=joinTrace_spec program input load call before loaded after 60
    (41000*(P.certificate.M+1)*entries) lh ll ch cl lc cc lt ct
  have loadedMemory : RegionMemory before loaded region:=RegionMemory.refl before region
  have allMemory : ∀ state∈joinTrace load call,RegionMemory before state region := by
    intro state member
    rcases joinTrace_member member with loadMember|callMember
    · have fields:=loadMemory state loadMember
      refine ⟨fun address _outside=>congrFun fields.1 address,?_,?_,fields.2.2⟩
      · rw [fields.2.1]
        exact Finset.subset_union_left
      · rw [fields.2.1]
    · exact loadedMemory.trans (callMemory state callMember)
  have allSpace : ∀ state∈joinTrace load call,workingCells state≤workingCells before+78*entries := by
    intro state member
    rcases joinTrace_member member with loadMember|callMember
    · have fields:=loadMemory state loadMember
      have same : workingCells state=workingCells before:=by
        unfold workingCells
        rw [fields.2.1,fields.2.2]
      omega
    · exact (workingCells_le_peak_of_member call state callMember).trans callPeak
  have noLoad:=no_solve_entry labels load.dropLast (by
    intro state member
    have scope:=loadScope state (List.mem_of_mem_dropLast member)
    omega)
  have positive : 0<entries:=retained_capacity_positive P.certificate.stages P.tools
  have factor : entries≤(P.certificate.M+1)*entries:=by nlinarith
  have timeBudget : 60+41000*(P.certificate.M+1)*entries≤42000*(P.certificate.M+1)*entries := by
    simp only [Nat.mul_assoc]
    omega
  have loadClosed : ∀ state∈load,ClosedPC labels before.pc (before.pc+3) state :=
    fun state member=>Or.inl (loadScope state member)
  have callClosed : ∀ state∈call,ClosedPC labels (before.pc+3) (before.pc+72) state := by
    simpa only [loadedPC,Nat.add_assoc] using callScope
  have callStrict : ∀ state∈call.dropLast,ProperPC labels (before.pc+3) (before.pc+72) state := by
    simpa only [loadedPC,Nat.add_assoc] using callProper
  have scopes:=join_scope labels load call before.pc (before.pc+3) (before.pc+72)
    (by intro empty;rw [empty] at ch;cases ch) (by omega) (by omega) loadClosed callClosed callStrict
  have loadCalls : SolverCallRefinement program labels P fee 40000 load :=
    PDCompute.CoreSearchLoop.refinement_of_no_entry program labels P fee 40000 load (by
      intro state member
      have scope:=loadScope state member
      omega)
  have joinedCalls:=PDCompute.CoreSearchLoop.refinement_join program labels P fee 40000 load call loaded ll ch loadCalls callCalls
  have joinedSafe:=PDCompute.Pack.joinTrace_invariant load call (fun state=>SafeBits state budget) loadSafe callSafe
  refine ⟨joinTrace load call,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans timeBudget,
    by omega,afterFresh,afterHeader,represented,preparedAfter,cacheAfter,output,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,?_,?_,joinedSafe,joinedCalls,scopes.1,scopes.2⟩
  · change actualSolveRequests labels (load.dropLast++call)=[penalty]
    rw [solveRequests_append,noLoad.1,requests,List.nil_append]
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry (load.dropLast++call)=1
    rw [solveEntries_append,noLoad.2,count,Nat.zero_add]


/-- Both source-initial solves run, return and physically retain their
actual tables. The high call preserves the low table/metadata. This
constructs the ORIGINAL cachedInitialState representation, without
supplying solved tables or a pre-existing search representation. -/
theorem initial_solved_resources (P : Parameters) (fee : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (values : ℕ→Cell) (header : Header before 0 values)
    (fresh : before.register .fresh=.natural 0)
    (tagValue : values 13=.natural 1) (zeroValue : values 14=.rational 0)
    (lambdaValue : values 15=.rational P.Lambda)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (fetched : FetchesCode program before.pc (initialSolvedCallsCode before.pc labels.solveEntry))
    (belowEntry : before.pc+144<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1)))
    (budget : ℕ) (safe : SafeBits before budget) (small : 7≤budget)
    (limitBits : (Cell.natural ((99+2*P.certificate.M)+78*PDCompute.Solver.entryCount P.certificate.stages P.tools)).bits≤budget)
    (endBits : (Cell.natural (before.pc+144)).bits≤budget)
    (controlRoom : runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (zeroRoom : 4194304*solverBitScale P fee 0 P.certificate.stages P.tools≤budget)
    (lambdaRoom : 4194304*solverBitScale P fee P.Lambda P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=commonSolverMarkerPC labels) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤84000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=before.pc+144 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧
      SearchStateRep P fee after (P.cachedInitialState P.endpointCache fee) ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+156*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      (∀ state∈trace,RegionMemory before state (initialSolvedCallsRegion P fee)) ∧
      actualSolveRequests labels trace=[0,P.Lambda] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=2 ∧
      (∀ state∈trace,SafeBits state budget) ∧ SolverCallRefinement program labels P fee 40000 trace ∧
      (∀ state∈trace,ClosedPC labels before.pc (before.pc+144) state) ∧
      (∀ state∈trace.dropLast,ProperPC labels before.pc (before.pc+144) state) := by
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  let region:=initialSolvedCallsRegion P fee
  change FetchesCode program before.pc
    (headerSolvedCallCode before.pc labels.solveEntry false++
      headerSolvedCallCode (before.pc+72) labels.solveEntry true) at fetched
  have lowerValue : values (multiplierSlot false)=.rational 0:=zeroValue
  obtain ⟨low,middle,lh,ll,lc,lt,middlePC,middleFresh,middleHeader,lowRep,preparedMiddle,cacheMiddle,
    middleOutput,lowPeak,lowMemory,lowRequests,lowCount,lowSafe,lowCalls,lowScope,lowProper⟩:=
    header_solved_resources P fee 0 program labels input before values false header fresh lowerValue
      prepared stored fetched.append_left (by omega) stubFetch bodyFetch
      budget safe small limitBits
      ((Nat.add_le_add_left (natBits_mono (by omega : before.pc+72≤before.pc+144)) 1).trans endBits)
      controlRoom zeroRoom markerLabel
  have middleMemory:=RegionMemory.trace_last lowMemory ll
  have upperOutside : 15∉solvedBufferCallRegion P fee 0 false :=
    solvedCall_small_outside P fee 0 false 15 (by decide) (by decide) (by decide)
  have upperValue : (fun slot=>middle.heap slot) (multiplierSlot true)=.rational P.Lambda :=
    (middleMemory.1 15 upperOutside).trans ((header.value 15 (by decide)).trans lambdaValue)
  have upperFetch : FetchesCode program middle.pc (headerSolvedCallCode middle.pc labels.solveEntry true) := by
    rw [middlePC]
    simpa only [headerSolvedCall_length] using fetched.append_right
  obtain ⟨high,after,hh,hl,hc,ht,afterPC,afterFresh,afterHeader,highRep,preparedAfter,cacheAfter,
    output,highPeak,highMemory,highRequests,highCount,highSafe,highCalls,highScope,highProper⟩:=
    header_solved_resources P fee P.Lambda program labels input middle (fun slot=>middle.heap slot) true
      middleHeader middleFresh upperValue preparedMiddle cacheMiddle upperFetch (by omega) stubFetch bodyFetch
      budget (lowSafe middle (List.mem_of_getLast? ll)) small limitBits
      (by simpa only [middlePC,Nat.add_assoc] using endBits) controlRoom lambdaRoom markerLabel
  have highFinalMemory:=RegionMemory.trace_last highMemory hl
  have lowAfter:=lowRep.preserve_other_call (by decide : (true : Bool)≠false) highFinalMemory
  have joined:=joinTrace_spec program input low high before middle after
    (42000*(P.certificate.M+1)*entries) (42000*(P.certificate.M+1)*entries) lh ll hh hl lc hc lt ht
  have allMemory : ∀ state∈joinTrace low high,RegionMemory before state region := by
    intro state member
    rcases joinTrace_member member with lowMember|highMember
    · exact (lowMemory state lowMember).enlarge Finset.subset_union_left
    · exact (middleMemory.enlarge Finset.subset_union_left).trans
        ((highMemory state highMember).enlarge Finset.subset_union_right)
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  have tagBefore : HeapList before 13 [.natural 1] := by
    apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simpa only [Nat.zero_add,Nat.add_zero] using header.live 13 (by decide)
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      simpa only [Nat.zero_add,Nat.add_zero,List.getElem_cons_zero] using
        (header.value 13 (by decide)).trans tagValue
  have tagAfter : HeapList after 13 [.natural 1] := by
    apply finalMemory.heapList tagBefore
    intro offset inside
    have zero : offset=0:=by change offset<1 at inside;omega
    subst offset
    simp only [Nat.add_zero]
    intro member
    rcases Finset.mem_union.mp member with lowRegion|highRegion
    · exact solvedCall_tag_outside P fee 0 false lowRegion
    · exact solvedCall_tag_outside P fee P.Lambda true highRegion
  have represented : SearchStateRep P fee after (P.cachedInitialState P.endpointCache fee) :=
    ⟨originalSolved_cached P fee 0,originalSolved_cached P fee P.Lambda,tagAfter,lowAfter,highRep⟩
  have counter : after.heap 28=before.heap 28 := by
    apply finalMemory.1
    intro member
    rcases Finset.mem_union.mp member with lowRegion|highRegion
    · exact solvedCall_counter_outside P fee 0 false lowRegion
    · exact solvedCall_counter_outside P fee P.Lambda true highRegion
  change peakCells low≤workingCells before+78*entries at lowPeak
  change peakCells high≤workingCells middle+78*entries at highPeak
  have middleBound:=(workingCells_le_peak_of_member low middle (List.mem_of_getLast? ll)).trans lowPeak
  have allSpace : ∀ state∈joinTrace low high,workingCells state≤workingCells before+156*entries := by
    intro state member
    rcases joinTrace_member member with lowMember|highMember
    · have bound:=(workingCells_le_peak_of_member low state lowMember).trans lowPeak
      omega
    · have bound:=(workingCells_le_peak_of_member high state highMember).trans highPeak
      omega
  have noLast:=no_solve_entry labels [middle] (by
    intro state member
    have same : state=middle:=List.mem_singleton.mp member
    subst state
    omega)
  have split:=List.dropLast_append_getLast? middle (by rw [ll];simp)
  have droppedRequests : actualSolveRequests labels low.dropLast=[0] := by
    rw [←split,solveRequests_append,noLast.1,List.append_nil] at lowRequests
    exact lowRequests
  have droppedCount : PaperProofs.Paid.Computation.entryCount labels.solveEntry low.dropLast=1 := by
    rw [←split,solveEntries_append,noLast.2,Nat.add_zero] at lowCount
    exact lowCount
  have finalPC : after.pc=before.pc+144:=by omega
  have timeBudget : 42000*(P.certificate.M+1)*entries+42000*(P.certificate.M+1)*entries≤
      84000*(P.certificate.M+1)*entries:=by
    simp only [Nat.mul_assoc]
    omega
  have highClosed : ∀ state∈high,ClosedPC labels (before.pc+72) (before.pc+144) state := by
    simpa only [middlePC,Nat.add_assoc] using highScope
  have highStrict : ∀ state∈high.dropLast,ProperPC labels (before.pc+72) (before.pc+144) state := by
    simpa only [middlePC,Nat.add_assoc] using highProper
  have scopes:=join_scope labels low high before.pc (before.pc+72) (before.pc+144)
    (by intro empty;rw [empty] at hh;cases hh) (by omega) (by omega) lowScope highClosed highStrict
  have joinedCalls:=PDCompute.CoreSearchLoop.refinement_join program labels P fee 40000 low high middle ll hh lowCalls highCalls
  have joinedSafe:=PDCompute.Pack.joinTrace_invariant low high (fun state=>SafeBits state budget) lowSafe highSafe
  refine ⟨joinTrace low high,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans timeBudget,
    finalPC,afterFresh,afterHeader,represented,preparedAfter,cacheAfter,counter,output.trans middleOutput,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,?_,?_,joinedSafe,joinedCalls,scopes.1,scopes.2⟩
  · change actualSolveRequests labels (low.dropLast++high)=[0,P.Lambda]
    rw [solveRequests_append,droppedRequests,highRequests]
    rfl
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry (low.dropLast++high)=2
    rw [solveEntries_append,droppedCount,highCount]


end PDCompute.CoreInitialize
