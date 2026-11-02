module
public import Paid.PDCompute_CoreSuffix_Initialize_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000
set_option maxRecDepth 4096
@[expose] public section
namespace PDCompute.CoreSuffix
open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open RootD27.Core PDLower.CoreSearch PDCompute.CoreSearchLoop

def searchCost (P : Parameters) (fee : ℚ) : ℕ :=
  85000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools+
    51000*(P.bisectionBudget fee+1)*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools

structure SearchResult (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin pcUpper : ℕ) (before : State) where
  trace : List State
  after : State
  head : trace.head?=some before
  last : trace.getLast?=some after
  chain : trace.IsChain (fun first later=>step program input first=some later)
  timeBound : time program trace≤searchCost P fee
  pc : after.pc=origin+693
  ready : Ready P fee after
  represented : SearchStateRep P fee after (P.buildCachedFrontend fee).state
  counter : after.heap 28=.natural 0
  output : after.output=before.output
  memory : ∀ state∈trace,RegionMemory before state (coreSearchRegion P)
  safe : ∀ state∈trace,RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee pcUpper)
  space : peakCells trace≤workingCells before+156*PDCompute.Solver.entryCount P.certificate.stages P.tools+
    PDCompute.CoreMemory.globalSpan P.certificate.M P.certificate.stages P.tools
  requests : actualSolveRequests labels trace=(P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2
  count : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace≤P.bisectionBudget fee+2
  countExact : PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=(actualSolveRequests labels trace).length
  refinement : SolverCallRefinement program labels P fee 40000 trace
  lower : ∀ state∈trace,origin≤state.pc

/-- The original init and all J real rounds on one trace. The two entry
solves and the loop's entire source log are identified in order. -/
theorem search (P : Parameters) (fee : ℚ) (program : Program) (labels : RoutineLabels)
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
    Nonempty (SearchResult program labels input P fee origin pcUpper before) := by
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  let span:=PDCompute.CoreMemory.globalSpan P.certificate.M P.certificate.stages P.tools
  have parts:=fetch_parts program origin labels fetched
  obtain ⟨initial⟩:=initialize_actual P fee program labels input origin pcUpper before position ready safe
    endBound belowEntry solverOrigin solverLength markerLabel parts.1 stubFetch bodyFetch
  obtain ⟨loop,after,lh,ll,lc,lt,pc,afterReady,represented,counter,output,memory,bits,space,_peakBits,
    count,requests,refinement,_countExact,lower⟩:=original_search_loop_lower_actual program labels input P fee
      (origin+164) pcUpper (by omega) (by omega) solverOrigin solverLength markerLabel parts.2.1
      stubFetch bodyFetch initial.after initial.pc initial.ready initial.represented initial.counter
      (initial.safe initial.after (List.mem_of_getLast? initial.last))
  have joined:=joinTrace_spec program input initial.trace loop before initial.after after
    (85000*(P.certificate.M+1)*entries) (51000*(P.bisectionBudget fee+1)*(P.certificate.M+1)*entries)
    initial.head initial.last lh ll initial.chain lc initial.timeBound lt
  have initialBound:=(workingCells_le_peak_of_member initial.trace initial.after
    (List.mem_of_getLast? initial.last)).trans initial.space
  have allSpace : ∀ state∈joinTrace initial.trace loop,workingCells state≤workingCells before+156*entries+span := by
    intro state member
    rcases joinTrace_member member with firstMember|laterMember
    · have bound:=(workingCells_le_peak_of_member initial.trace state firstMember).trans initial.space
      omega
    · have bound:=(workingCells_le_peak_of_member loop state laterMember).trans space
      change workingCells state≤workingCells initial.after+span at bound
      omega
  have boundary : initial.after.pc≠labels.solveEntry := by have current:=initial.pc;omega
  have actualRequests:=requests_join labels initial.trace loop initial.after initial.last boundary
  rw [initial.requests] at actualRequests
  have allCalls:=refinement_join program labels P fee 40000 initial.trace loop initial.after
    initial.last lh initial.refinement refinement
  have allCount:=RootD27.Core.entryCount_join_ne labels.solveEntry initial.trace loop initial.after initial.last boundary
  rw [initial.count] at allCount
  refine ⟨⟨joinTrace initial.trace loop,after,joined.1,joined.2.1,joined.2.2.1,joined.2.2.2,
    by omega,afterReady,represented,counter,output.trans initial.output,
    RegionMemory.join_trace initial.trace loop before initial.after (coreSearchRegion P) initial.last
      initial.memory memory,
    PDCompute.Pack.joinTrace_invariant initial.trace loop (fun state=>RootD27.Bits.SafeBits state
      (PDCompute.CoreGlobalBudget.budget P fee pcUpper)) initial.safe bits,
    PDLower.CalibrationCompute.peakCells_le_of_forall _ _ allSpace,actualRequests.trans requests,
    by omega,entries_eq_requests program labels P fee 40000 _ allCalls,allCalls,?_⟩⟩
  intro state member
  rcases joinTrace_member member with firstMember|laterMember
  · exact initial.lower state firstMember
  · have bound:=lower state laterMember
    omega

end PDCompute.CoreSuffix
