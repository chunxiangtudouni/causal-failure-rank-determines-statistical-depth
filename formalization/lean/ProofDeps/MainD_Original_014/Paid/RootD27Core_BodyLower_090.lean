module

public import Paid.RootD27Core_OriginalLoop_089

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch PDCompute.CoreSearchLoop

/-- The live branch executes the actual tag4, stopping183 and midpoint64
prefix of the original516 body. The returned table, statistics and saved
descriptor are physical results of its ONE actual solver call. -/
theorem bisection_live_prefix_lower_actual (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (decrementPC scale budget : ℕ) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (running : ¬P.searchStopped fee (.bracket lower upper))
    (safe : RootD27.Bits.SafeBits before budget) (small : 7≤budget)
    (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (endBits : (Cell.natural (before.pc+516)).bits≤budget)
    (decrementBits : natBits decrementPC≤budget)
    (controlRoom : PDLower.CoreRuntimeNumeric.runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (scalarRoom : 4194304*solverBitScale P fee ((lower.multiplier+upper.multiplier)/2)
      P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=PDLower.CoreRuntimeNumeric.commonSolverMarkerPC labels)
    (belowEntry : before.pc+516<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (fetched : FetchesCode program before.pc (bisectionBodyCode before.pc labels.solveEntry decrementPC))
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤43000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=before.pc+251 ∧ Ready P fee after ∧
      SearchStateRep P fee after (.bracket lower upper) ∧
      after.heap 24=.rational ((lower.multiplier+upper.multiplier)/2) ∧
      HeapList after 25 (originalStatistics P fee ((lower.multiplier+upper.multiplier)/2)) ∧
      HeapList after (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools)
        (originalSolveEncoding P fee ((lower.multiplier+upper.multiplier)/2)) ∧
      HeapList after 46 [.natural (resultBase (99+2*P.certificate.M) P.certificate.stages P.tools),
        .natural (originalSolveEncoding P fee ((lower.multiplier+upper.multiplier)/2)).length] ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      peakCells trace≤workingCells before+65*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      (∀ state∈trace,RegionMemory before state (PDCompute.CoreMidpoint.midpointRegion P)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      actualSolveRequests labels trace=[(lower.multiplier+upper.multiplier)/2] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      SolverCallRefinement program labels P fee 40000 trace ∧
      (∀ state∈trace,before.pc≤state.pc) := by
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  let region:=PDCompute.CoreMidpoint.midpointRegion P
  have endNat : natBits (before.pc+516)≤budget := by
    change 1+natBits (before.pc+516)≤budget at endBits
    omega
  have parts:=bisectionBody_fetch_parts program before.pc labels.solveEntry decrementPC fetched
  obtain ⟨tag,th,tl,tc,tt,tagHeader,tagFresh,tagRep,tagProperties,tagScope,_tagProper,tagPeak,tagRequests,_tagCount⟩:=
    represented_tag_actual P fee (.bracket lower upper) program labels input before decrementPC budget
      ready.header ready.fresh represented safe small
      ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+516)).trans endNat)
      decrementBits (by omega) decrementBelow parts.1
  let tagged:=tagDecisionResult before (.bracket lower upper) decrementPC
  have taggedPC : tagged.pc=before.pc+4:=rfl
  have stopFetch : FetchesCode program tagged.pc (stopDecisionCode tagged.pc (tagged.pc+183) decrementPC) := by
    simpa only [taggedPC,Nat.add_assoc] using parts.2.1
  obtain ⟨stop,middle,sh,sl,sc,st,middleTarget,middleFresh,middleHeader,middleRep,
    middlePrepared,middleCache,middleCounter,middleOutput,stopPeak,stopProperties,stopScope,
    _stopProper,stopRequests,_stopCount⟩:=
    represented_stop_decision_actual P fee lower upper program labels input tagged decrementPC scale budget
      tagHeader tagFresh ready.prepared ready.cache tagRep (tagProperties tagged (List.mem_of_getLast? tl)).2
      intrinsic room addressBits
      ((PDROC.DataBits.natBits_mono (by rw [taggedPC];omega : tagged.pc+183≤before.pc+516)).trans endNat)
      decrementBits (by rw [taggedPC];omega) decrementBelow stopFetch
  have middlePC : middle.pc=before.pc+187 := by
    simpa only [stopDecisionTarget,ite_eq_right running,taggedPC,Nat.add_assoc] using middleTarget
  have middleReady : Ready P fee middle:=⟨middleHeader,middleFresh,middlePrepared,middleCache⟩
  have midpointFetch : FetchesCode program middle.pc (midpointSaveCode middle.pc labels.solveEntry) := by
    have complete:=parts.2.2.1
    change FetchesCode program (before.pc+187)
      (midpointSaveCode (before.pc+187) labels.solveEntry++
        comparisonStoredCode .equal 27 3++[.branchZero .flag (before.pc+262) (before.pc+273)]) at complete
    rw [middlePC]
    exact complete.append_left.append_left
  obtain ⟨mid,after,mh,ml,mc,mt,afterPC,afterReady,afterRep,price,statistics,table,descriptor,
    counter,output,midPeak,midMemory,midSafe,midRequests,_midCount,midCalls,_midCache,midScope,
    _midProper,_midBits⟩:=
    PDCompute.CoreMidpoint.midpoint_save_resources P fee lower upper program labels input middle scale budget
      middleReady middleRep (stopProperties middle (List.mem_of_getLast? sl)).2 small intrinsic room addressBits
      baseBits ((Nat.add_le_add_left (PDROC.DataBits.natBits_mono
        (by rw [middlePC];omega : middle.pc+64≤before.pc+516)) 1).trans endBits)
      controlRoom scalarRoom markerLabel (by rw [middlePC];omega) midpointFetch stubFetch bodyFetch
  have first:=joinTrace_spec program input tag stop before tagged middle 75 3015 th tl sh sl tc sc tt st
  have joined:=joinTrace_spec program input (joinTrace tag stop) mid before middle after
    (75+3015) (39500*(P.certificate.M+1)*entries) first.1 first.2.1 mh ml first.2.2.1 mc first.2.2.2 mt
  have tagExcluded : ∀ state∈tag,state.pc≠labels.solveEntry := by
    intro state member
    rcases tagScope state member with inline|terminal
    · omega
    · change state.pc=before.pc+4 at terminal
      omega
  have stopExcluded : ∀ state∈stop,state.pc≠labels.solveEntry := by
    intro state member
    rcases stopScope state member with inline|terminal
    · rw [taggedPC] at inline
      omega
    · have target : stopDecisionTarget P fee lower upper tagged decrementPC=before.pc+187 := by
        simp only [stopDecisionTarget,ite_eq_right running,taggedPC,Nat.add_assoc]
      rw [target] at terminal
      omega
  have tagCalls:=refinement_of_no_entry program labels P fee 40000 tag tagExcluded
  have stopCalls:=refinement_of_no_entry program labels P fee 40000 stop stopExcluded
  have firstCalls:=refinement_join program labels P fee 40000 tag stop tagged tl sh tagCalls stopCalls
  have calls:=refinement_join program labels P fee 40000 (joinTrace tag stop) mid middle first.2.1 mh firstCalls midCalls
  have requests : actualSolveRequests labels (joinTrace (joinTrace tag stop) mid)=
      [(lower.multiplier+upper.multiplier)/2] := by
    rw [requests_join labels (joinTrace tag stop) mid middle first.2.1 (by omega),
      requests_join labels tag stop tagged tl (by rw [taggedPC];omega),tagRequests,stopRequests,midRequests]
    rfl
  have count : PaperProofs.Paid.Computation.entryCount labels.solveEntry (joinTrace (joinTrace tag stop) mid)=1 := by
    rw [entries_eq_requests program labels P fee 40000 _ calls,requests]
    rfl
  have scalarSubset : scalarRegion⊆region:=by
    exact Finset.subset_union_left.trans Finset.subset_union_left
  have firstMemory:=RegionMemory.join_trace tag stop before tagged region tl
    (fun state member=>((tagProperties state member).1).enlarge (Finset.empty_subset _))
    (fun state member=>((stopProperties state member).1).enlarge scalarSubset)
  have memory:=RegionMemory.join_trace (joinTrace tag stop) mid before middle region first.2.1 firstMemory midMemory
  have bits:=PDCompute.Pack.joinTrace_invariant (joinTrace tag stop) mid
    (fun state=>RootD27.Bits.SafeBits state budget)
    (PDCompute.Pack.joinTrace_invariant tag stop _
      (fun state member=>(tagProperties state member).2) (fun state member=>(stopProperties state member).2)) midSafe
  have taggedSpace : workingCells tagged=workingCells before:=rfl
  have middleSpace : workingCells middle≤workingCells before := by
    have bound:=(workingCells_le_peak_of_member stop middle (List.mem_of_getLast? sl)).trans stopPeak
    rw [taggedSpace] at bound
    exact bound
  have space : ∀ state∈joinTrace (joinTrace tag stop) mid,workingCells state≤workingCells before+65*entries := by
    intro state member
    rcases joinTrace_member member with earlier|current
    · rcases joinTrace_member earlier with taggedMember|stoppedMember
      · have bound:=(workingCells_le_peak_of_member tag state taggedMember).trans tagPeak
        omega
      · have bound:=(workingCells_le_peak_of_member stop state stoppedMember).trans stopPeak
        rw [taggedSpace] at bound
        omega
    · have bound:=(workingCells_le_peak_of_member mid state current).trans midPeak
      omega
  have positive : 0<(P.certificate.M+1)*entries := by
    unfold entries PDCompute.Solver.entryCount
    positivity
  have cost : 75+3015+39500*(P.certificate.M+1)*entries≤43000*(P.certificate.M+1)*entries := by
    simp only [Nat.mul_assoc]
    omega
  have allLower : ∀ state∈joinTrace (joinTrace tag stop) mid,before.pc≤state.pc := by
    intro state member
    rcases joinTrace_member member with earlier|solved
    · rcases joinTrace_member earlier with taggedMember|stoppedMember
      · rcases tagScope state taggedMember with inline|terminal
        · exact inline.1
        · change state.pc=before.pc+4 at terminal
          omega
      · rcases stopScope state stoppedMember with inline|terminal
        · rw [taggedPC] at inline
          omega
        · have target : stopDecisionTarget P fee lower upper tagged decrementPC=before.pc+187 := by
            simp only [stopDecisionTarget,ite_eq_right running,taggedPC,Nat.add_assoc]
          rw [target] at terminal
          omega
    · rcases midScope state solved with inline|callee
      · rw [middlePC] at inline
        omega
      · omega
  exact ⟨joinTrace (joinTrace tag stop) mid,after,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2.trans cost,by omega,afterReady,afterRep,price,statistics,table,descriptor,
    counter.trans middleCounter,output.trans middleOutput,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ space,memory,bits,requests,count,calls,allLower⟩


/-- The complete ORIGINAL516 body on a nonstopped bracket. The true
251 prefix is joined to the true equality/less/update suffix. Its one
solver call, fixed return-marker window and all bit/space bounds concern
this SAME trace; the update direction is computed from physical risk. -/
theorem bisection_live_lower_actual (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (decrementPC scale budget : ℕ) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (running : ¬P.searchStopped fee (.bracket lower upper))
    (safe : RootD27.Bits.SafeBits before budget) (small : 7≤budget)
    (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (baseBits : (Cell.natural (99+2*P.certificate.M)).bits≤budget)
    (endBits : (Cell.natural (before.pc+516)).bits≤budget)
    (decrementBits : natBits decrementPC≤budget)
    (naturalRoom : 32*coreOperandBound P fee≤budget)
    (controlRoom : PDLower.CoreRuntimeNumeric.runtimeControlRoom P (labels.solveEntry+1)≤budget)
    (scalarRoom : 4194304*solverBitScale P fee ((lower.multiplier+upper.multiplier)/2)
      P.certificate.stages P.tools≤budget)
    (markerLabel : labels.solveReturn=PDLower.CoreRuntimeNumeric.commonSolverMarkerPC labels)
    (belowEntry : before.pc+516<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (decrementAbove : before.pc≤decrementPC)
    (fetched : FetchesCode program before.pc (bisectionBodyCode before.pc labels.solveEntry decrementPC))
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤50000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=decrementPC ∧ Ready P fee after ∧
      SearchStateRep P fee after (P.cachedMultiplierStep P.endpointCache fee (.bracket lower upper)) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (coreSearchRegion P)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      peakCells trace≤workingCells before+(coreSearchRegion P).card ∧
      actualSolveRequests labels trace=[(lower.multiplier+upper.multiplier)/2] ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=1 ∧
      SolverCallRefinement program labels P fee 40000 trace ∧
      (∀ state∈trace,before.pc≤state.pc) := by
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  obtain ⟨front,middle,fh,fl,fc,ft,middlePC,middleReady,middleRep,price,statistics,table,descriptor,
    middleCounter,middleOutput,_frontSpace,frontMemory,frontSafe,frontRequests,_frontCount,frontCalls,frontLower⟩:=
    bisection_live_prefix_lower_actual P fee lower upper program labels input before decrementPC scale budget ready
      represented running safe small intrinsic room addressBits baseBits endBits decrementBits controlRoom scalarRoom
      markerLabel belowEntry decrementBelow fetched stubFetch bodyFetch
  have data : PDCompute.CoreBranch.MidpointData P fee
      (PDCompute.CoreBranch.midpointPenalty lower upper) middle := ⟨price,statistics,descriptor,table⟩
  obtain ⟨back,after,bh,bl,bc,bt,afterPC,afterReady,afterRep,counter,output,backMemory,backSafe,
    _backSpace,backScope,_backProper,backRequests,_backCount,backCalls⟩:=
    PDCompute.CoreBranch.suffix_actual P fee lower upper program labels input before.pc decrementPC middle budget
      middlePC middleReady middleRep data (frontSafe middle (List.mem_of_getLast? fl)) small naturalRoom
      endBits decrementBits belowEntry decrementBelow fetched
  have joined:=joinTrace_spec program input front back before middle after
    (43000*(P.certificate.M+1)*entries) (5000*entries+2000) fh fl bh bl fc bc ft bt
  have memory:=RegionMemory.join_trace front back before middle (coreSearchRegion P) fl
    (fun state member=>(frontMemory state member).enlarge (midpoint_subset_coreSearch P))
    (fun state member=>(backMemory state member).enlarge (branch_subset_coreSearch P))
  have bits:=PDCompute.Pack.joinTrace_invariant front back (fun state=>RootD27.Bits.SafeBits state budget)
    frontSafe backSafe
  have calls:=refinement_join program labels P fee 40000 front back middle fl bh frontCalls backCalls
  have requests : actualSolveRequests labels (joinTrace front back)=[(lower.multiplier+upper.multiplier)/2] := by
    rw [requests_join labels front back middle fl (by omega),frontRequests,backRequests,List.append_nil]
  have count : PaperProofs.Paid.Computation.entryCount labels.solveEntry (joinTrace front back)=1 := by
    rw [entries_eq_requests program labels P fee 40000 _ calls,requests]
    rfl
  have finalRep : SearchStateRep P fee after
      (P.cachedMultiplierStep P.endpointCache fee (.bracket lower upper)) := by
    simp only [cachedMultiplierStep,ite_eq_right running]
    exact afterRep
  have positive : 0<entries := by unfold entries PDCompute.Solver.entryCount;positivity
  have entriesBound : entries≤(P.certificate.M+1)*entries := by nlinarith
  have cost : 43000*(P.certificate.M+1)*entries+(5000*entries+2000)≤
      50000*(P.certificate.M+1)*entries := by
    simp only [Nat.mul_assoc]
    omega
  have allLower : ∀ state∈joinTrace front back,before.pc≤state.pc := by
    intro state member
    rcases joinTrace_member member with earlier|later
    · exact frontLower state earlier
    · rcases backScope state later with inline|terminal
      · omega
      · omega
  refine ⟨joinTrace front back,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2.trans cost,
    afterPC,afterReady,finalRep,counter.trans middleCounter,output.trans middleOutput,memory,bits,?_,
    requests,count,calls,allLower⟩
  exact PDLower.CalibrationCompute.peakCells_le_of_forall _ _
    (fun state member=>(memory state member).workingCells_le)


end RootD27.Core
