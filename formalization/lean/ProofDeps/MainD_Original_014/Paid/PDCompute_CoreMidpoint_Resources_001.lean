module

public import Paid.RootD27Core_SavedMidpoint_081
public import Paid.PDLower_CoreRuntimeNumeric_RuntimeMarked_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDCompute.CoreMidpoint

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open RootD27.Core RootD27.Bits PDLower.CoreSearch PDLower.CoreRuntimeNumeric PDCompute.CoreSearchLoop

def midpointRegion (P : Parameters) : Finset ℕ :=
  (scalarRegion∪midpointStatisticsRegion P)∪{46,47}

/-- Decode the original literal64 without supplying any per-phase fetch oracle. -/
theorem midpoint_fetch_parts (program : Program) (origin entry : ℕ)
    (fetched : FetchesCode program origin (midpointSaveCode origin entry)) :
    FetchesCode program origin (headerCode midpointCommands) ∧
    FetchesCode program (origin+24) (solverRuntimeDispatchCode (origin+39) entry) ∧
    FetchesCode program (origin+39) (rootStatisticsCode 25) ∧
    FetchesCode program (origin+59) saveSolverResultCode := by
  change FetchesCode program origin
    (headerCode midpointCommands++solverRuntimeDispatchCode (origin+39) entry++
      rootStatisticsCode 25++saveSolverResultCode) at fetched
  simp only [List.append_assoc] at fetched
  refine ⟨fetched.append_left,?_,?_,?_⟩
  · simpa only [midpointCode_length] using fetched.append_right.append_left
  · simpa only [midpointCode_length,solverRuntimeDispatch_length,Nat.add_assoc] using
      fetched.append_right.append_right.append_left
  · simpa only [midpointCode_length,solverRuntimeDispatch_length,rootStatistics_length,Nat.add_assoc] using
      fetched.append_right.append_right.append_right

/-- The actual original midpoint24, dispatch15, complete solver, physical
statistics20 and save5 share ONE trace and ONE caller-carried bit budget.
The midpoint, table, statistics and descriptor are computed outputs. -/
theorem midpoint_save_resources (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (scale budget : ℕ) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (safe : SafeBits before budget) (small : 7≤budget)
    (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (endBits : (Cell.natural (before.pc+64)).bits≤budget)
    (controlRoom : runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (scalarRoom : 4194304*solverBitScale P fee ((lower.multiplier+upper.multiplier)/2)
      P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=commonSolverMarkerPC labels)
    (belowEntry : before.pc+64<labels.solveEntry)
    (fetched : FetchesCode program before.pc (midpointSaveCode before.pc labels.solveEntry))
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤39500*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=before.pc+64 ∧ Ready P fee after ∧
      SearchStateRep P fee after (.bracket lower upper) ∧
      after.heap 24=.rational ((lower.multiplier+upper.multiplier)/2) ∧
      HeapList after 25 (originalStatistics P fee ((lower.multiplier+upper.multiplier)/2)) ∧
      HeapList after (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
        (originalSolveEncoding P fee ((lower.multiplier+upper.multiplier)/2)) ∧
      HeapList after 46 [.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools),
        .natural (originalSolveEncoding P fee ((lower.multiplier+upper.multiplier)/2)).length] ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+65*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      (∀ state∈trace,RegionMemory before state (midpointRegion P)) ∧
      (∀ state∈trace,SafeBits state budget) ∧
      actualSolveRequests labels trace=[(lower.multiplier+upper.multiplier)/2] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      SolverCallRefinement program labels P fee 40000 trace ∧
      (∀ state∈trace,HeapList state 96 (encodeList encodeEndpoint P.endpointCache.toList)) ∧
      (∀ state∈trace,(before.pc≤state.pc ∧ state.pc≤before.pc+64) ∨
        (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length)) ∧
      (∀ state∈trace.dropLast,(before.pc≤state.pc ∧ state.pc<before.pc+64) ∨
        (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length)) ∧
      peakOperandBits trace≤budget := by
  let penalty:=(lower.multiplier+upper.multiplier)/2
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  let region:=midpointRegion P
  have parts:=midpoint_fetch_parts program before.pc labels.solveEntry fetched
  have endNat : natBits (before.pc+64)≤budget := by
    change 1+natBits (before.pc+64)≤budget at endBits
    omega
  obtain ⟨mid,middle,mh,ml,mc,mt,midPC,midFresh,midHeader,midRep,midPrepared,midCache,
    midTotal,midPrice,midCounter,midOutput,midPeak,midFinal,midProperties,midScope,_midProper,midRequests,_midCount⟩:=
    represented_midpoint_actual P fee lower upper program labels input before scale budget ready.header ready.fresh
      ready.prepared ready.cache represented safe intrinsic room addressBits
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+24≤before.pc+64)).trans endNat)
      (by omega) parts.1
  have dispatchFetch : FetchesCode program middle.pc (solverRuntimeDispatchCode (before.pc+39) labels.solveEntry) := by
    rw [midPC]
    exact parts.2.1
  obtain ⟨solver,computed,sh,sl,sc,st,computedPC,_computedFresh,_old,address,index,table,
    computedPrepared,statistics,solverOutput,solverPeak,solverMemory,solverRequests,_solverCount,
    solverSafe,solverScope,_solverProper,_computedReturn,solverCalls,solverCache,priceFrame,_solverBits⟩:=
    runtime_statistics_marked_resources P fee penalty program labels input middle 25 (before.pc+39)
      (by decide) (by decide) midTotal midPrepared midCache dispatchFetch (by omega) (by omega)
      stubFetch bodyFetch parts.2.2.1 budget (midProperties middle (List.mem_of_getLast? ml)).2 small
      baseBits ((Nat.add_le_add_left (PDROC.DataBits.natBits_mono (by omega : before.pc+39≤before.pc+64)) 1).trans endBits)
      ((PDROC.DataBits.natBits_mono (by omega : middle.pc+14≤before.pc+64)).trans endNat)
      controlRoom scalarRoom markerLabel
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+39+20≤before.pc+64)).trans endNat)
  change time program solver≤38800*(P.certificate.M+1)*entries at st
  change peakCells solver≤workingCells middle+65*entries at solverPeak
  change HeapList computed 25 (originalStatistics P fee penalty) at statistics
  change HeapList computed (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
    (originalSolveEncoding P fee penalty) at table
  change computed.register .index=.natural (originalSolveEncoding P fee penalty).length at index
  have computedMemory : RegionMemory middle computed (midpointStatisticsRegion P) :=
    solverMemory computed (List.mem_of_getLast? sl)
  have computedHeader : Header computed 0 (fun slot=>computed.heap slot) := by
    intro slot inside
    exact ⟨computedMemory.2.2.1 (midHeader.live slot inside),by simp only [Nat.zero_add]⟩
  have computedRep:=midRep.preserve_midpoint_statistics computedMemory
  have computedPrice : computed.heap 24=.rational penalty :=
    (priceFrame (by decide)).trans midPrice
  have saveFetch : FetchesCode program computed.pc saveSolverResultCode := by
    have position : computed.pc=before.pc+59:=by omega
    rw [position]
    exact parts.2.2.2
  obtain ⟨save,after,vh,vl,vc,vt,savePC,saveFresh,saveHeader,saveRep,savePrepared,saveCache,
    savePrice,saveStatistics,saveTable,descriptor,saveCounter,saveOutput,saveProperties,
    saveScope,saveProper,savePeak,saveRequests,_saveCount⟩:=
    saved_midpoint_actual P fee penalty (.bracket lower upper) program labels input computed budget
      computedHeader computedPrepared (solverCache computed (List.mem_of_getLast? sl)) computedRep computedPrice
      statistics address index table (solverSafe computed (List.mem_of_getLast? sl)) small
      ((PDROC.DataBits.natBits_mono (by omega : computed.pc+5≤before.pc+64)).trans endNat)
      (by omega) saveFetch
  have first:=joinTrace_spec program input mid solver before middle computed
    375 (38800*(P.certificate.M+1)*entries) mh ml sh sl mc sc mt st
  have joined:=joinTrace_spec program input (joinTrace mid solver) save before computed after
    (375+38800*(P.certificate.M+1)*entries) 90 first.1 first.2.1 vh vl first.2.2.1 vc first.2.2.2 vt
  have midSubset : scalarRegion⊆region:=Finset.subset_union_left.trans Finset.subset_union_left
  have solverSubset : midpointStatisticsRegion P⊆region:=Finset.subset_union_right.trans Finset.subset_union_left
  have saveSubset : ({46,47}:Finset ℕ)⊆region:=Finset.subset_union_right
  have firstMemory:=RegionMemory.join_trace mid solver before middle region ml
    (fun state member=>((midProperties state member).1).enlarge midSubset)
    (fun state member=>(solverMemory state member).enlarge solverSubset)
  have allMemory:=RegionMemory.join_trace (joinTrace mid solver) save before computed region first.2.1
    firstMemory (fun state member=>((saveProperties state member).1).enlarge saveSubset)
  have allSafe:=PDCompute.Pack.joinTrace_invariant (joinTrace mid solver) save (fun state=>SafeBits state budget)
    (PDCompute.Pack.joinTrace_invariant mid solver (fun state=>SafeBits state budget)
      (fun state member=>(midProperties state member).2) solverSafe)
    (fun state member=>(saveProperties state member).2)
  have middleSpace:=(workingCells_le_peak_of_member mid middle (List.mem_of_getLast? ml)).trans midPeak
  have computedSpace:=(workingCells_le_peak_of_member solver computed (List.mem_of_getLast? sl)).trans solverPeak
  have allSpace : ∀ state∈joinTrace (joinTrace mid solver) save,workingCells state≤workingCells before+65*entries := by
    intro state member
    rcases joinTrace_member member with earlier|saved
    · rcases joinTrace_member earlier with midpoint|solved
      · exact ((workingCells_le_peak_of_member mid state midpoint).trans midPeak).trans (by omega)
      · have bound:=(workingCells_le_peak_of_member solver state solved).trans solverPeak
        omega
    · have bound:=(workingCells_le_peak_of_member save state saved).trans savePeak
      omega
  have counterOutside : 28∉midpointStatisticsRegion P := by
    intro member
    rcases Finset.mem_union.mp member with work|stats
    · obtain ⟨offset,_inside,equal⟩:=Finset.mem_image.mp work
      omega
    · simp only [Finset.mem_insert,Finset.mem_singleton] at stats
      omega
  have counter : after.heap 28=before.heap 28:=
    saveCounter.trans ((computedMemory.1 28 counterOutside).trans midCounter)
  have midExcluded : ∀ state∈mid,state.pc≠labels.solveEntry := by
    intro state member
    have bounds:=midScope state member
    omega
  have saveExcluded : ∀ state∈save,state.pc≠labels.solveEntry := by
    intro state member
    have bounds:=saveScope state member
    omega
  have midCalls:=refinement_of_no_entry program labels P fee 40000 mid midExcluded
  have saveCalls:=refinement_of_no_entry program labels P fee 40000 save saveExcluded
  have firstCalls:=refinement_join program labels P fee 40000 mid solver middle ml sh midCalls solverCalls
  have calls:=refinement_join program labels P fee 40000 (joinTrace mid solver) save computed first.2.1 vh firstCalls saveCalls
  have requests : actualSolveRequests labels (joinTrace (joinTrace mid solver) save)=[penalty] := by
    rw [requests_join labels (joinTrace mid solver) save computed first.2.1 (by omega),
      requests_join labels mid solver middle ml (by omega),midRequests,solverRequests,saveRequests,
      List.nil_append,List.append_nil]
  have count : PaperProofs.Paid.Computation.entryCount labels.solveEntry (joinTrace (joinTrace mid solver) save)=1 := by
    rw [entries_eq_requests program labels P fee 40000 _ calls,requests]
    rfl
  have midCacheAll : ∀ state∈mid,HeapList state 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
    intro state member
    apply ((midProperties state member).1).heapList ready.cache
    intro offset _inside member
    change 96+offset∈Finset.Icc 13 42 at member
    have bound:=Finset.mem_Icc.mp member
    omega
  have saveCacheAll : ∀ state∈save,HeapList state 96 (encodeList encodeEndpoint P.endpointCache.toList) := by
    intro state member
    apply ((saveProperties state member).1).heapList (solverCache computed (List.mem_of_getLast? sl))
    intro offset _inside member
    simp only [Finset.mem_insert,Finset.mem_singleton] at member
    omega
  have allCache:=PDCompute.Pack.joinTrace_invariant (joinTrace mid solver) save
    (fun state=>HeapList state 96 (encodeList encodeEndpoint P.endpointCache.toList))
    (PDCompute.Pack.joinTrace_invariant mid solver _ midCacheAll solverCache) saveCacheAll
  have closed : ∀ state∈joinTrace (joinTrace mid solver) save,
      (before.pc≤state.pc ∧ state.pc≤before.pc+64) ∨
      (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length) := by
    intro state member
    rcases joinTrace_member member with earlier|saved
    · rcases joinTrace_member earlier with midpoint|solved
      · have bounds:=midScope state midpoint
        exact Or.inl ⟨bounds.1,by omega⟩
      · rcases solverScope state solved with setup|callee|stats
        · exact Or.inl ⟨by omega,by omega⟩
        · exact Or.inr callee
        · exact Or.inl ⟨by omega,by omega⟩
    · have bounds:=saveScope state saved
      exact Or.inl ⟨by omega,by omega⟩
  have nonempty : save≠[]:=by intro empty;rw [empty] at vh;cases vh
  have proper : ∀ state∈(joinTrace (joinTrace mid solver) save).dropLast,
      (before.pc≤state.pc ∧ state.pc<before.pc+64) ∨
      (labels.solveEntry≤state.pc ∧ state.pc<labels.solveEntry+1+(solverCalleeCode .liveHeap (labels.solveEntry+1)).length) := by
    intro state member
    change state∈((joinTrace mid solver).dropLast++save).dropLast at member
    rw [List.dropLast_append_of_ne_nil nonempty] at member
    rcases List.mem_append.mp member with earlier|saved
    · rcases joinTrace_member (List.mem_of_mem_dropLast earlier) with midpoint|solved
      · have bounds:=midScope state midpoint
        exact Or.inl ⟨bounds.1,by omega⟩
      · rcases solverScope state solved with setup|callee|stats
        · exact Or.inl ⟨by omega,by omega⟩
        · exact Or.inr callee
        · exact Or.inl ⟨by omega,by omega⟩
    · have low:=(saveScope state (List.mem_of_mem_dropLast saved)).1
      have high:=saveProper state saved
      exact Or.inl ⟨by omega,by omega⟩
  have positive : 0<(P.certificate.M+1)*entries := by
    unfold entries PDCompute.Solver.entryCount
    positivity
  have cost : 375+38800*(P.certificate.M+1)*entries+90≤39500*(P.certificate.M+1)*entries := by
    simp only [Nat.mul_assoc]
    omega
  exact ⟨joinTrace (joinTrace mid solver) save,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans cost,by omega,⟨saveHeader,saveFresh,savePrepared,saveCache⟩,saveRep,
    savePrice,saveStatistics,saveTable,descriptor,counter,saveOutput.trans (solverOutput.trans midOutput),
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,allMemory,allSafe,requests,count,calls,allCache,
    closed,proper,safe_trace_peak _ budget allSafe⟩

end PDCompute.CoreMidpoint
