module

public import Paid.RootD27Core_UpdateMetadata_079
public import Paid.PDCompute_CoreSearchLoop_BodyCalls_008

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch
open PDCompute.CoreSearchLoop (Ready)

/-- Complete fetched516-op body in its exact-source case. The actual
four-step tag path skips all solves and reaches the real decrement. -/
theorem bisection_exact_actual (P : Parameters) (fee : ℚ) (solution : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (decrementPC budget callConstant : ℕ) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (.exact solution))
    (safe : RootD27.Bits.SafeBits before budget) (small : 7≤budget)
    (pcBits : natBits (before.pc+516)≤budget) (decrementBits : natBits decrementPC≤budget)
    (belowEntry : before.pc+516<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (fetched : FetchesCode program before.pc (bisectionBodyCode before.pc labels.solveEntry decrementPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤75 ∧
      after.pc=decrementPC ∧ Ready P fee after ∧
      SearchStateRep P fee after (P.cachedMultiplierStep P.endpointCache fee (.exact solution)) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state ∅) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧ peakCells trace≤workingCells before ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+516) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 ∧
      SolverCallRefinement program labels P fee callConstant trace := by
  have parts:=bisectionBody_fetch_parts program before.pc labels.solveEntry decrementPC fetched
  obtain ⟨trace,head,last,chain,cost,afterHeader,afterFresh,afterRep,properties,scope,proper,space,requests,count⟩:=
    represented_tag_actual P fee (.exact solution) program labels input before decrementPC budget ready.header ready.fresh
      represented safe small ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+516)).trans pcBits)
      decrementBits (by omega) decrementBelow parts.1
  let after:=tagDecisionResult before (.exact solution) decrementPC
  have afterReady : Ready P fee after:=⟨afterHeader,afterFresh,ready.prepared,ready.cache⟩
  have nextRep : SearchStateRep P fee after (P.cachedMultiplierStep P.endpointCache fee (.exact solution)) := by
    rw [exact_step_fixed]
    exact afterRep
  have excluded : ∀ state∈trace,state.pc≠labels.solveEntry := by
    intro state member
    rcases scope state member with inline|terminal
    · omega
    · change state.pc=decrementPC at terminal
      omega
  have refinement:=PDCompute.CoreSearchLoop.refinement_of_no_entry program labels P fee callConstant trace excluded
  exact ⟨trace,after,head,last,chain,cost,rfl,afterReady,nextRep,rfl,rfl,
    (fun state member=>(properties state member).1),(fun state member=>(properties state member).2),space,
    (fun state member=>by have bounds:=proper state member;omega),requests,count,refinement⟩

/-- Complete fetched516-op body in its stopped-bracket case. Both tag
and source stopping test execute, then really branch to the decrement;
all unused midpoint/solve/update instructions remain unexecuted. -/
theorem bisection_stopped_actual (P : Parameters) (fee : ℚ) (lower upper : MultiplierSolve)
    (program : Program) (labels : RoutineLabels) (input : List Cell) (before : State)
    (decrementPC scale budget callConstant : ℕ) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (.bracket lower upper))
    (stopped : P.searchStopped fee (.bracket lower upper))
    (safe : RootD27.Bits.SafeBits before budget) (small : 7≤budget)
    (intrinsic : ScalarInputBits P fee lower upper scale)
    (room : 1+scalarValueBudget scale≤budget) (addressBits : 1+natBits headerWords≤budget)
    (pcBits : natBits (before.pc+516)≤budget) (decrementBits : natBits decrementPC≤budget)
    (belowEntry : before.pc+516<labels.solveEntry) (decrementBelow : decrementPC<labels.solveEntry)
    (fetched : FetchesCode program before.pc (bisectionBodyCode before.pc labels.solveEntry decrementPC)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤3090 ∧
      after.pc=decrementPC ∧ Ready P fee after ∧
      SearchStateRep P fee after (P.cachedMultiplierStep P.endpointCache fee (.bracket lower upper)) ∧
      after.heap 28=before.heap 28 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state scalarRegion) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧ peakCells trace≤workingCells before ∧
      (∀ state∈trace.dropLast,before.pc≤state.pc ∧ state.pc<before.pc+516) ∧
      actualSolveRequests labels trace=[] ∧ PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=0 ∧
      SolverCallRefinement program labels P fee callConstant trace := by
  have parts:=bisectionBody_fetch_parts program before.pc labels.solveEntry decrementPC fetched
  obtain ⟨tag,head,last,chain,cost,middleHeader,middleFresh,middleRep,tagProperties,tagScope,tagProper,tagSpace,_tagRequests,_tagCount⟩:=
    represented_tag_actual P fee (.bracket lower upper) program labels input before decrementPC budget ready.header ready.fresh
      represented safe small ((PDROC.DataBits.natBits_mono (by omega : before.pc+4≤before.pc+516)).trans pcBits)
      decrementBits (by omega) decrementBelow parts.1
  let middle:=tagDecisionResult before (.bracket lower upper) decrementPC
  have middlePC : middle.pc=before.pc+4:=rfl
  have stopFetch : FetchesCode program middle.pc (stopDecisionCode middle.pc (middle.pc+183) decrementPC) := by
    simpa only [middlePC,Nat.add_assoc] using parts.2.1
  have middleSafe : RootD27.Bits.SafeBits middle budget:=(tagProperties middle (List.mem_of_getLast? last)).2
  obtain ⟨stop,after,stopHead,stopLast,stopChain,stopCost,afterPC,afterFresh,afterHeader,afterRep,
    afterPrepared,afterCache,counter,output,stopSpace,stopProperties,stopScope,stopProper,_stopRequests,_stopCount⟩:=
    represented_stop_decision_actual P fee lower upper program labels input middle decrementPC scale budget
      middleHeader middleFresh ready.prepared ready.cache middleRep middleSafe intrinsic room addressBits
      ((PDROC.DataBits.natBits_mono (by rw [middlePC];omega : middle.pc+183≤before.pc+516)).trans pcBits)
      decrementBits (by rw [middlePC];omega) decrementBelow stopFetch
  have finalPC : after.pc=decrementPC:=by simpa only [stopDecisionTarget,ite_eq_left stopped] using afterPC
  have joined:=joinTrace_spec program input tag stop before middle after 75 3015
    head last stopHead stopLast chain stopChain cost stopCost
  have allMemory : ∀ state∈joinTrace tag stop,RegionMemory before state scalarRegion := by
    intro state member
    rcases joinTrace_member member with tagMember|stopMember
    · exact ((tagProperties state tagMember).1).enlarge (Finset.empty_subset _)
    · exact (stopProperties state stopMember).1
  have allSafe:=PDCompute.Pack.joinTrace_invariant tag stop (fun state=>RootD27.Bits.SafeBits state budget)
    (fun state member=>(tagProperties state member).2) (fun state member=>(stopProperties state member).2)
  have allSpace : ∀ state∈joinTrace tag stop,workingCells state≤workingCells before := by
    intro state member
    rcases joinTrace_member member with tagMember|stopMember
    · exact (workingCells_le_peak_of_member tag state tagMember).trans tagSpace
    · exact (workingCells_le_peak_of_member stop state stopMember).trans stopSpace
  have excluded : ∀ state∈joinTrace tag stop,state.pc≠labels.solveEntry := by
    intro state member
    rcases joinTrace_member member with tagMember|stopMember
    · rcases tagScope state tagMember with inline|terminal
      · omega
      · change state.pc=before.pc+4 at terminal
        omega
    · rcases stopScope state stopMember with inline|terminal
      · rw [middlePC] at inline
        omega
      · have target : stopDecisionTarget P fee lower upper middle decrementPC=decrementPC:=by
          simp only [stopDecisionTarget,ite_eq_left stopped]
        rw [target] at terminal
        omega
  have noCalls:=no_solve_entry labels (joinTrace tag stop) excluded
  have refinement:=PDCompute.CoreSearchLoop.refinement_of_no_entry program labels P fee callConstant
    (joinTrace tag stop) excluded
  have nonempty : stop≠[]:=by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at stopHead
  have proper : ∀ state∈(joinTrace tag stop).dropLast,before.pc≤state.pc ∧ state.pc<before.pc+516 := by
    intro state member
    change state∈(tag.dropLast++stop).dropLast at member
    rw [List.dropLast_append_of_ne_nil nonempty] at member
    rcases List.mem_append.mp member with tagMember|stopMember
    · have bounds:=tagProper state tagMember
      omega
    · have bounds:=stopProper state stopMember
      rw [middlePC] at bounds
      omega
  have nextRep : SearchStateRep P fee after
      (P.cachedMultiplierStep P.endpointCache fee (.bracket lower upper)) := by
    rw [stopped_step_fixed P fee _ stopped]
    exact afterRep
  exact ⟨joinTrace tag stop,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,finalPC,
    ⟨afterHeader,afterFresh,afterPrepared,afterCache⟩,nextRep,counter,output,allMemory,allSafe,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,proper,noCalls.1,noCalls.2,refinement⟩

end RootD27.Core
