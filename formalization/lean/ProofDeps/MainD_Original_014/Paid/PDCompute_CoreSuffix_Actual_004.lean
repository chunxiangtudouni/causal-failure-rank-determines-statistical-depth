module
public import Paid.PDCompute_CoreSuffix_Search_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 4096
@[expose] public section
namespace PDCompute.CoreSuffix
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

def emittedCells (P : Parameters) (fee : ℚ) : List Cell :=
  encodeState (P.buildCachedFrontend fee).state++[.rational (selectorWeightRat P fee (P.buildCachedFrontend fee))]

def cost (P : Parameters) (fee : ℚ) : ℕ :=
  searchCost P fee+32768*PDCompute.Solver.entryCount P.certificate.stages P.tools

/-- All fields concern the same actual945 execution. The heap is allowed
to change in the real global region, and output is its actual prefix.
The common solver marker remains labels.solveReturn throughout. -/
structure Result (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin pcUpper : ℕ) (before : State) where
  trace : List State
  after : State
  selected : State
  selectedMember : selected∈trace
  head : trace.head?=some before
  last : trace.getLast?=some after
  chain : trace.IsChain (fun first later=>step program input first=some later)
  timeBound : time program trace≤cost P fee
  selectedPC : selected.pc=origin+873
  selectedWeight : selected.heap 29=.rational (selectorWeightRat P fee (P.buildCachedFrontend fee))
  heap : after.heap=selected.heap
  live : after.live=selected.live
  counter : after.heap 28=.natural 0
  output : after.output=before.output++emittedCells P fee
  pc : after.pc=origin+944
  halt : program[after.pc]?=some .halt
  stopped : step program input after=none
  frames : ∀ state∈trace,OutputRegion P before (emittedCells P fee) state
  safe : ∀ state∈trace,RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee pcUpper)
  space : peakCells trace≤workingCells before+156*PDCompute.Solver.entryCount P.certificate.stages P.tools+
    PDCompute.CoreMemory.globalSpan P.certificate.M P.certificate.stages P.tools+
      16*PDCompute.Solver.entryCount P.certificate.stages P.tools+4
  bits : peakOperandBits trace≤PDCompute.CoreGlobalBudget.budget P fee pcUpper
  outputBound : ∀ state∈trace,state.output.length≤before.output.length+16*PDCompute.Solver.entryCount P.certificate.stages P.tools+4
  requests : actualSolveRequests labels trace=(P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2
  count : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace≤P.bisectionBudget fee+2
  countExact : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=(actualSolveRequests labels trace).length
  logLength : (P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2.length≤P.bisectionBudget fee+2
  refinement : SolverCallRefinement program labels P fee 40000 trace
  lower : ∀ state∈trace,origin≤state.pc

/-- Ready and the carried SAME globalB suffice. Initial source data,
two solved tables, all J updates, current selector and physical payload
are constructed by the actual fetched945. No source/answer oracle is an
input, and final end945 may be exactly the shared solver entry. -/
theorem actual (P : Parameters) (fee : ℚ) (program : Program) (labels : RoutineLabels)
    (input : List Cell) (origin pcUpper : ℕ) (before : State) (position : before.pc=origin)
    (ready : Ready P fee before)
    (safe : RootD27.Bits.SafeBits before (PDCompute.CoreGlobalBudget.budget P fee pcUpper))
    (endBound : origin+945≤pcUpper) (belowEntry : origin+945≤labels.solveEntry)
    (solverOrigin : labels.solveEntry+1≤pcUpper)
    (solverLength : (solverCalleeCode .liveHeap (labels.solveEntry+1)).length≤pcUpper)
    (markerLabel : labels.solveReturn=PDLower.CoreRuntimeNumeric.commonSolverMarkerPC labels)
    (fetched : FetchesCode program origin (code origin labels))
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1))) :
    Nonempty (Result program labels input P fee origin pcUpper before) := by
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  let span:=PDCompute.CoreMemory.globalSpan P.certificate.M P.certificate.stages P.tools
  obtain ⟨searching⟩:=search P fee program labels input origin pcUpper before position ready safe
    endBound belowEntry solverOrigin solverLength markerLabel fetched stubFetch bodyFetch
  obtain ⟨finalizing,selected,after,fh,fl,fc,ft,selectedMember,selectedPC,selectedWeight,heap,live,finalLive,
    counter,output,pc,halt,stopped,frames,bits,space,_peakBits,_outputBound,_scope,_proper,_below,
    requests,_count,refinement⟩:=PDCompute.CoreFinalization.original_actual P fee program labels input
      (origin+693) pcUpper searching.after searching.pc searching.ready searching.represented
      (searching.safe searching.after (List.mem_of_getLast? searching.last)) (by omega) (by omega)
      (fetch_parts program origin labels fetched).2.2
  have joined:=joinTrace_spec program input searching.trace finalizing before searching.after after
    (searchCost P fee) (32768*entries) searching.head searching.last fh fl searching.chain fc searching.timeBound ft
  have searchMemory:=RegionMemory.trace_last searching.memory searching.last
  have allFrames : ∀ state∈joinTrace searching.trace finalizing,OutputRegion P before (emittedCells P fee) state := by
    intro state member
    rcases joinTrace_member member with firstMember|laterMember
    · exact OutputRegion.of_memory _ (searching.memory state firstMember)
    · exact OutputRegion.after_memory searchMemory (frames state laterMember)
  have allBits:=PDCompute.Pack.joinTrace_invariant searching.trace finalizing
    (fun state=>RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee pcUpper)) searching.safe bits
  have searchBound:=(workingCells_le_peak_of_member searching.trace searching.after
    (List.mem_of_getLast? searching.last)).trans searching.space
  have allSpace : ∀ state∈joinTrace searching.trace finalizing,
      workingCells state≤workingCells before+156*entries+span+16*entries+4 := by
    intro state member
    rcases joinTrace_member member with firstMember|laterMember
    · have bound:=(workingCells_le_peak_of_member searching.trace state firstMember).trans searching.space
      omega
    · have bound:=(workingCells_le_peak_of_member finalizing state laterMember).trans space
      change workingCells state≤workingCells searching.after+16*entries+4 at bound
      omega
  have actualRequests:=requests_join labels searching.trace finalizing searching.after searching.last
    (by have current:=searching.pc;omega)
  rw [searching.requests,requests,List.append_nil] at actualRequests
  have calls:=refinement_join program labels P fee 40000 searching.trace finalizing searching.after
    searching.last fh searching.refinement refinement
  have countExact:=entries_eq_requests program labels P fee 40000 _ calls
  have countJoined:=RootD27.Core.entryCount_join_ne labels.solveEntry searching.trace finalizing searching.after searching.last
    (by have current:=searching.pc;omega)
  rw [_count,Nat.add_zero] at countJoined
  have countBound:=countJoined.le.trans searching.count
  have tablesLength:=PDCompute.CoreFinalization.represented_state_length P fee _ searching.after searching.represented
  have cellsLength : (emittedCells P fee).length≤16*entries+4 := by
    simp only [emittedCells,List.length_append,List.length_cons,List.length_nil]
    omega
  refine ⟨⟨joinTrace searching.trace finalizing,after,selected,?_,joined.1,joined.2.1,joined.2.2.1,
    joined.2.2.2,by omega,selectedWeight,heap,live,counter.trans searching.counter,?_,by omega,halt,stopped,
    allFrames,allBits,PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,
    PDCompute.Pack.safeBits_peak _ _ allBits,?_,actualRequests,countBound,countExact,?_,calls,?_⟩⟩
  · exact List.mem_append.mpr (Or.inr selectedMember)
  · simpa only [searching.output,emittedCells] using output
  · intro state member
    have bound:=(allFrames state member).output_length
    change state.output.length≤before.output.length+(emittedCells P fee).length at bound
    omega
  · rw [←actualRequests,←countExact]
    exact countBound
  · intro state member
    rcases joinTrace_member member with firstMember|laterMember
    · exact searching.lower state firstMember
    · have current:=(_scope state laterMember).1
      omega

/-- Every earlier endpoint/calibration phase entry is excluded from the
entire suffix, including its terminal HALT, by the actual all-PC bound. -/
theorem Result.no_earlier_entry {program : Program} {labels : RoutineLabels} {input : List Cell}
    {P : Parameters} {fee : ℚ} {origin pcUpper : ℕ} {before : State}
    (result : Result program labels input P fee origin pcUpper before) (entry : ℕ) (earlier : entry<origin) :
    PaperProofs.Paid.Computation.entryCount entry result.trace=0 :=
  RootD27.Core.entryCount_zero_of_lower entry origin result.trace earlier result.lower

end PDCompute.CoreSuffix
