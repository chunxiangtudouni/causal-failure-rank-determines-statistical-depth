module

public import Paid.RootD27Core_RetainedCommitBlock_057

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)

def solvedBufferCallCode (origin entry : ℕ) (upper : Bool) : List Instruction :=
  solverRuntimeDispatchCode (origin+15) entry++rootStatisticsCode (statisticsSlot upper)++
    retainedCommitBlockCode (origin+35) upper

theorem solverRuntimeDispatch_length (returnPC entry : ℕ) :
    (solverRuntimeDispatchCode returnPC entry).length=15 := rfl

theorem solvedBufferCall_length (origin entry : ℕ) (upper : Bool) :
    (solvedBufferCallCode origin entry upper).length=69 := by
  simp only [solvedBufferCallCode,List.length_append,solverRuntimeDispatch_length,
    rootStatistics_length,retainedCommitBlock_length]

def solvedBufferCallRegion (P : Parameters) (fee penalty : ℚ) (upper : Bool) : Finset ℕ :=
  (workspace (99+2*P.certificate.M) P.certificate.stages P.tools∪
    {statisticsSlot upper,statisticsSlot upper+1,statisticsSlot upper+2})∪
  (retainedCopyRegion (99+2*P.certificate.M) P.certificate.stages P.tools
    (originalSolveEncoding P fee penalty).length upper∪{tableLengthSlot upper})

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
theorem solved_buffer_call_actual (P : Parameters) (fee penalty : ℚ)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (values : ℕ→Cell) (upper : Bool) (header : Header before 0 values)
    (lambdaValue : values (multiplierSlot upper)=.rational penalty)
    (penaltyValue : before.register .total=.rational penalty)
    (prepared : HeapList before 0 (preparedInput P fee))
    (stored : HeapList before 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (fetched : FetchesCode program before.pc (solvedBufferCallCode before.pc labels.solveEntry upper))
    (belowEntry : before.pc+69<labels.solveEntry)
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
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
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 := by
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
    preparedComputed,statistics,solverOutput,solverPeak,solverMemory,requests,count⟩:=
    solver_runtime_statistics_actual P fee penalty program labels input before (statisticsSlot upper) (before.pc+15)
      (statisticsSlot_bounds upper).1 (statisticsSlot_bounds upper).2 penaltyValue prepared stored
      fetched.append_left (by omega) (by omega) stubFetch bodyFetch statisticsFetch
  change time program solver≤38800*(P.certificate.M+1)*entries at st
  change peakCells solver≤workingCells before+65*entries at solverPeak
  change HeapList computed (statisticsSlot upper) (originalStatistics P fee penalty) at statistics
  have bufferFetch : FetchesCode program computed.pc (retainedCommitBlockCode computed.pc upper) := by
    have pc : computed.pc=before.pc+35:=by omega
    rw [pc]
    simpa only [solverRuntimeDispatch_length,rootStatistics_length,Nat.add_assoc] using fetched.append_right.append_right
  obtain ⟨buffer,after,bh,bl,bc,bt,bufferPC,fresh,_index,retained,preparedAfter,lengthAfter,
    bufferOutput,bufferPeak,bufferMemory,bufferScope⟩:=
    retained_commit_block_actual P fee penalty program input computed base upper preparedComputed
      computedFresh address index table bufferFetch
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
  refine ⟨joinTrace solver buffer,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans timeBudget,
    finalPC,fresh,finalHeader,solved,preparedAfter,cacheAfter,bufferOutput.trans solverOutput,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,?_,?_⟩
  · change actualSolveRequests labels (solver.dropLast++buffer)=[penalty]
    rw [solveRequests_append,droppedRequests,noBuffer.1,List.append_nil]
  · change PaperProofs.Paid.Computation.entryCount labels.solveEntry (solver.dropLast++buffer)=1
    rw [solveEntries_append,droppedCount,noBuffer.2,Nat.add_zero]

end RootD27.Core
