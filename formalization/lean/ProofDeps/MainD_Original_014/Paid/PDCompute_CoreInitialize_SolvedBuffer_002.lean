module
public import Paid.PDCompute_CoreInitialize_Metadata_001
public import Paid.PDLower_CoreRuntimeNumeric_RuntimeMarked_013
public import Paid.PDLower_CoreRuntimeNumeric_CopySaved_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
@[expose] public section

namespace PDCompute.CoreInitialize
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame PDROC.DataBits
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open RootD27.Core RootD27.Bits PDLower.CoreRuntimeNumeric

/-- Actual trace concatenation retains the inline/callee geometry; only
the actual final inline PC is dropped from the proper-prefix predicate. -/
theorem join_scope (labels : RoutineLabels) (first later : List State) (low middle high : ℕ)
    (nonempty : later≠[]) (ordered : low≤middle) (strict : middle<high)
    (left : ∀ state∈first,ClosedPC labels low middle state)
    (right : ∀ state∈later,ClosedPC labels middle high state)
    (proper : ∀ state∈later.dropLast,ProperPC labels middle high state) :
    (∀ state∈joinTrace first later,ClosedPC labels low high state) ∧
      (∀ state∈(joinTrace first later).dropLast,ProperPC labels low high state) := by
  constructor
  · intro state member
    rcases joinTrace_member member with earlier|following
    · rcases left state earlier with inline|callee
      · exact Or.inl ⟨inline.1,by omega⟩
      · exact Or.inr callee
    · rcases right state following with inline|callee
      · exact Or.inl ⟨by omega,inline.2⟩
      · exact Or.inr callee
  · intro state member
    change state∈(first.dropLast++later).dropLast at member
    rw [List.dropLast_append_of_ne_nil nonempty] at member
    rcases List.mem_append.mp member with earlier|following
    · rcases left state (List.mem_of_mem_dropLast earlier) with inline|callee
      · exact Or.inl ⟨inline.1,by omega⟩
      · exact Or.inr callee
    · rcases proper state following with inline|callee
      · exact Or.inl ⟨by omega,inline.2⟩
      · exact Or.inr callee

private theorem small_outside_workspace (base n k address : ℕ) (below : address<base) :
    address∉workspace base n k := by
  intro member
  obtain ⟨index,_bound,equal⟩:=Finset.mem_image.mp member
  omega

private theorem small_outside_commit (base n k count address : ℕ) (upper : Bool)
    (small : address<46) (different : address≠tableLengthSlot upper) :
    address∉(retainedCopyRegion base n k count upper∪{tableLengthSlot upper}) := by
  have lower : 48≤retainedTableBase base n k upper := by
    have bound:=retained_base_above_workspace base n k upper
    unfold workspaceSize headerWords at bound
    omega
  intro member
  rcases Finset.mem_union.mp member with oldRegion|slot
  · rcases Finset.mem_union.mp oldRegion with scratch|destination
    · simp only [Finset.mem_insert,Finset.mem_singleton] at scratch
      omega
    · have bounds:=(mem_cellRegion_iff _ _ _).mp destination
      omega
  · exact different (Finset.mem_singleton.mp slot)

/-- A single fixed69-op inline call site constructs the actual original
solved buffer, starting without a table or statistics. The real solver,
true return, physical copy, saved-length load and metadata commit share
ONE trace; all original cache/input/header liveness is retained. -/
theorem solved_buffer_resources (P : Parameters) (fee penalty : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (values : ℕ→Cell) (upper : Bool) (header : Header before 0 values)
    (lambdaValue : values (multiplierSlot upper)=.rational penalty)
    (penaltyValue : before.register .total=.rational penalty)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (fetched : FetchesCode program before.pc (solvedBufferCallCode before.pc labels.solveEntry upper))
    (belowEntry : before.pc+69<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1)))
    (budget : ℕ) (safe : SafeBits before budget) (small : 7≤budget)
    (limitBits : (Cell.natural ((99+2*P.certificate.M)+78*PDCompute.Solver.entryCount P.certificate.stages P.tools)).bits≤budget)
    (endBits : (Cell.natural (before.pc+69)).bits≤budget)
    (controlRoom : runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (scalarRoom : 4194304*solverBitScale P fee penalty P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=commonSolverMarkerPC labels) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤41000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=before.pc+69 ∧ after.register .fresh=.natural 0 ∧
      Header after 0 (fun slot=>after.heap slot) ∧ SolvedBuffer P fee penalty upper after ∧
      HeapList after 0 (preparedInput P fee) ∧
      HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+78*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      (∀ state∈trace,RegionMemory before state (solvedBufferCallRegion P fee penalty upper)) ∧
      actualSolveRequests labels trace=[penalty] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      (∀ state∈trace,SafeBits state budget) ∧ SolverCallRefinement program labels P fee 40000 trace ∧
      (∀ state∈trace,ClosedPC labels before.pc (before.pc+69) state) ∧
      (∀ state∈trace.dropLast,ProperPC labels before.pc (before.pc+69) state) := by
  let base:=99+2*P.certificate.M
  let n:=P.certificate.stages
  let k:=P.tools
  let entries:=PDCompute.Solver.entryCount n k
  let cells:=originalSolveEncoding P fee penalty
  let region:=solvedBufferCallRegion P fee penalty upper
  change FetchesCode program before.pc
    (solverRuntimeDispatchCode (before.pc+15) labels.solveEntry++rootStatisticsCode (statisticsSlot upper)++
      retainedCommitBlockCode (before.pc+35) upper) at fetched
  simp only [List.append_assoc] at fetched
  have statisticsFetch : FetchesCode program (before.pc+15) (rootStatisticsCode (statisticsSlot upper)) := by
    simpa only [solverRuntimeDispatch_length] using fetched.append_right.append_left
  obtain ⟨solver,computed,sh,sl,sc,st,computedPC,computedFresh,_computedOld,address,index,table,
    preparedComputed,statistics,solverOutput,solverPeak,solverMemory,requests,count,solverSafe,solverScope,solverProper,_computedReturn,solverCalls,_cache,_untouched,_bitPeak⟩:=
    runtime_statistics_marked_resources P fee penalty program labels input before (statisticsSlot upper) (before.pc+15)
      (statisticsSlot_bounds upper).1 (statisticsSlot_bounds upper).2 penaltyValue prepared stored
      fetched.append_left (by omega) (by omega) stubFetch bodyFetch statisticsFetch
      budget safe small
      ((Nat.add_le_add_left (natBits_mono (by omega : 99+2*P.certificate.M≤(99+2*P.certificate.M)+78*PDCompute.Solver.entryCount P.certificate.stages P.tools)) 1).trans limitBits)
      ((Nat.add_le_add_left (natBits_mono (by omega : before.pc+15≤before.pc+69)) 1).trans endBits)
      ((natBits_mono (by omega : before.pc+14≤before.pc+69)).trans (by change 1+natBits (before.pc+69)≤budget at endBits;omega))
      controlRoom scalarRoom markerLabel
      ((natBits_mono (by omega : before.pc+15+20≤before.pc+69)).trans (by change 1+natBits (before.pc+69)≤budget at endBits;omega))
  change time program solver≤38800*(P.certificate.M+1)*entries at st
  change peakCells solver≤workingCells before+65*entries at solverPeak
  change HeapList computed (statisticsSlot upper) (originalStatistics P fee penalty) at statistics
  have bufferFetch : FetchesCode program computed.pc (retainedCommitBlockCode computed.pc upper) := by
    have pc : computed.pc=before.pc+35:=by omega
    rw [pc]
    simpa only [solverRuntimeDispatch_length,rootStatistics_length,Nat.add_assoc] using fetched.append_right.append_right
  obtain ⟨buffer,after,bh,bl,bc,bt,bufferPC,fresh,_index,retained,preparedAfter,lengthAfter,
    bufferOutput,bufferPeak,bufferMemory,bufferScope,bufferSafe,bufferProper⟩:=
    commit_block_resources P fee penalty program input computed base upper preparedComputed
      computedFresh address index table bufferFetch
      budget (solverSafe computed (List.mem_of_getLast? sl)) small (by unfold base;omega) limitBits
      (by have position : computed.pc=before.pc+35:=by omega
          simpa only [position,Nat.add_assoc] using endBits)
  change peakCells buffer≤workingCells computed+cells.length+3 at bufferPeak
  change time program buffer≤150*cells.length+465 at bt
  have computedMemory:=solverMemory computed (List.mem_of_getLast? sl)
  have finalBufferMemory:=bufferMemory after (List.mem_of_getLast? bl)
  have lambdaBefore : HeapList before (multiplierSlot upper) [.rational penalty] := by
    apply PDLower.CalibrationCompute.HeapList.of_values
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      have bound : multiplierSlot upper<headerWords:=by cases upper <;> decide
      simpa only [Nat.zero_add,Nat.add_zero] using header.live (multiplierSlot upper) bound
    · intro offset inside
      have zero : offset=0:=by change offset<1 at inside;omega
      subst offset
      have bound : multiplierSlot upper<headerWords:=by cases upper <;> decide
      simpa only [Nat.zero_add,Nat.add_zero,List.getElem_cons_zero] using
        (header.value (multiplierSlot upper) bound).trans lambdaValue
  have lambdaComputed : HeapList computed (multiplierSlot upper) [.rational penalty] := by
    apply computedMemory.heapList lambdaBefore
    intro offset inside
    have zero : offset=0:=by change offset<1 at inside;omega
    subst offset
    simp only [Nat.add_zero]
    intro member
    rcases Finset.mem_union.mp member with work|metadata
    · apply small_outside_workspace base n k (multiplierSlot upper) ?_ work
      cases upper <;> simp only [multiplierSlot,Bool.false_eq_true,ite_false,ite_true] <;>
        unfold base <;> omega
    · cases upper <;> simp only [multiplierSlot,statisticsSlot,Finset.mem_insert,Finset.mem_singleton,
        Bool.false_eq_true,ite_false,ite_true] at metadata <;> omega
  have lambdaAfter : HeapList after (multiplierSlot upper) [.rational penalty] := by
    apply finalBufferMemory.heapList lambdaComputed
    intro offset inside
    have zero : offset=0:=by change offset<1 at inside;omega
    subst offset
    simp only [Nat.add_zero]
    apply small_outside_commit
    · cases upper <;> decide
    · cases upper <;> decide
  have statisticsAfter : HeapList after (statisticsSlot upper) (originalStatistics P fee penalty) := by
    apply finalBufferMemory.heapList statistics
    intro offset inside
    change offset<3 at inside
    apply small_outside_commit
    · cases upper <;> simp only [statisticsSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
    · cases upper <;> simp only [statisticsSlot,tableLengthSlot,Bool.false_eq_true,ite_false,ite_true] <;> omega
  have solved : SolvedBuffer P fee penalty upper after:=⟨lambdaAfter,statisticsAfter,lengthAfter,retained⟩
  have joined:=joinTrace_spec program input solver buffer before computed after
    (38800*(P.certificate.M+1)*entries) (150*cells.length+465) sh sl bh bl sc bc st bt
  have allMemory : ∀ state∈joinTrace solver buffer,RegionMemory before state region := by
    intro state member
    rcases joinTrace_member member with solverMember|bufferMember
    · exact (solverMemory state solverMember).enlarge Finset.subset_union_left
    · exact (computedMemory.enlarge Finset.subset_union_left).trans
        ((bufferMemory state bufferMember).enlarge Finset.subset_union_right)
  have finalMemory:=RegionMemory.trace_last allMemory joined.2.1
  have finalHeader : Header after 0 (fun slot=>after.heap slot) := by
    intro slot inside
    refine ⟨finalMemory.2.2.1 (header.live slot inside),by simp only [Nat.zero_add]⟩
  have cacheComputed : HeapList computed 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
    apply computedMemory.heapList stored
    intro offset inside member
    rcases Finset.mem_union.mp member with work|metadata
    · exact original_endpoint_avoids_solver P n k offset inside work
    · cases upper <;> simp only [statisticsSlot,Finset.mem_insert,Finset.mem_singleton,
        Bool.false_eq_true,ite_false,ite_true] at metadata <;> omega
  have cacheAfter : HeapList after 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
    apply finalBufferMemory.heapList cacheComputed
    intro offset inside member
    have below:=original_endpoint_below_solver P offset inside
    have slotUpper:=(tableLengthSlot_bounds upper).2
    rcases Finset.mem_union.mp member with copyRegion|lengthRegion
    · rcases Finset.mem_union.mp copyRegion with scratch|destination
      · simp only [Finset.mem_insert,Finset.mem_singleton] at scratch
        omega
      · have bounds:=(mem_cellRegion_iff _ _ _).mp destination
        have start:=retained_base_above_workspace base n k upper
        change base+workspaceSize P.certificate.stages P.tools≤
          retainedTableBase base P.certificate.stages P.tools upper at start
        change 96+offset<base at below
        omega
    · have equal:=Finset.mem_singleton.mp lengthRegion
      omega
  have encodedBound : cells.length≤8*entries :=
    (original_table_capacity P fee penalty n k).trans (retained_capacity_enough n k)
  have positive : 0<entries:=retained_capacity_positive n k
  have computedBound:=(workingCells_le_peak_of_member solver computed (List.mem_of_getLast? sl)).trans solverPeak
  have allSpace : ∀ state∈joinTrace solver buffer,workingCells state≤workingCells before+78*entries := by
    intro state member
    rcases joinTrace_member member with solverMember|bufferMember
    · have bound:=(workingCells_le_peak_of_member solver state solverMember).trans solverPeak
      omega
    · have bound:=(workingCells_le_peak_of_member buffer state bufferMember).trans bufferPeak
      omega
  have noBuffer:=no_solve_entry labels buffer (by
    intro state member
    have bound:=(bufferScope state member).2
    omega)
  have noLast:=no_solve_entry labels [computed] (by
    intro state member
    have same : state=computed:=List.mem_singleton.mp member
    subst state
    omega)
  have split:=List.dropLast_append_getLast? computed (by rw [sl];simp)
  have droppedRequests : actualSolveRequests labels solver.dropLast=[penalty] := by
    rw [←split,solveRequests_append,noLast.1,List.append_nil] at requests
    exact requests
  have droppedCount : PaperProofs.Paid.Computation.entryCount labels.solveEntry solver.dropLast=1 := by
    rw [←split,solveEntries_append,noLast.2,Nat.add_zero] at count
    exact count
  have finalPC : after.pc=before.pc+69:=by omega
  have factor : entries≤(P.certificate.M+1)*entries:=by nlinarith
  have timeBudget : 38800*(P.certificate.M+1)*entries+(150*cells.length+465)≤
      41000*(P.certificate.M+1)*entries := by
    simp only [Nat.mul_assoc]
    omega
  have solverClosed : ∀ state∈solver,ClosedPC labels before.pc (before.pc+35) state := by
    intro state member
    rcases solverScope state member with setup|callee|statistics
    · exact Or.inl ⟨setup.1,by omega⟩
    · exact Or.inr callee
    · exact Or.inl ⟨by omega,by omega⟩
  have bufferClosed : ∀ state∈buffer,ClosedPC labels (before.pc+35) (before.pc+69) state := by
    intro state member
    have scope:=bufferScope state member
    exact Or.inl ⟨by omega,by omega⟩
  have bufferStrict : ∀ state∈buffer.dropLast,ProperPC labels (before.pc+35) (before.pc+69) state := by
    intro state member
    have scope:=bufferProper state member
    exact Or.inl ⟨by omega,by omega⟩
  have scopes:=join_scope labels solver buffer before.pc (before.pc+35) (before.pc+69)
    (by intro empty;rw [empty] at bh;cases bh) (by omega) (by omega) solverClosed bufferClosed bufferStrict
  have bufferCalls : SolverCallRefinement program labels P fee 40000 buffer :=
    PDCompute.CoreSearchLoop.refinement_of_no_entry program labels P fee 40000 buffer (by
      intro state member
      have scope:=bufferScope state member
      omega)
  have joinedCalls:=PDCompute.CoreSearchLoop.refinement_join program labels P fee 40000 solver buffer computed sl bh solverCalls bufferCalls
  have joinedSafe:=PDCompute.Pack.joinTrace_invariant solver buffer (fun state=>SafeBits state budget) solverSafe bufferSafe
  refine ⟨joinTrace solver buffer,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans timeBudget,
    finalPC,fresh,finalHeader,solved,preparedAfter,cacheAfter,bufferOutput.trans solverOutput,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,?_,?_,joinedSafe,joinedCalls,scopes.1,scopes.2⟩
  · change actualSolveRequests labels (solver.dropLast++buffer)=[penalty]
    rw [solveRequests_append,droppedRequests,noBuffer.1,List.append_nil]
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry (solver.dropLast++buffer)=1
    rw [solveEntries_append,droppedCount,noBuffer.2,Nat.add_zero]


end PDCompute.CoreInitialize
