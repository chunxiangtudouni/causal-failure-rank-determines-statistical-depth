module

public import Paid.RootD27Core_OriginalBody_088
public import Paid.PDCompute_CoreSearchLoop_Calls_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CoreSearch PDCompute.CoreSearchLoop

/-- The original J-loop now consumes the ACTUAL fully proved516 body,
not a pending BodySpec. One region and B serve every real iteration.
The original log, entry count and fixed return-marker windows concern
the SAME fetched execution. -/
theorem original_search_loop_actual (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin pcUpper : ℕ)
    (endBound : origin+529≤pcUpper) (belowEntry : origin+529<labels.solveEntry)
    (solverOrigin : labels.solveEntry+1≤pcUpper)
    (solverLength : (solverCalleeCode .liveHeap (labels.solveEntry+1)).length≤pcUpper)
    (markerLabel : labels.solveReturn=PDLower.CoreRuntimeNumeric.commonSolverMarkerPC labels)
    (fetched : FetchesCode program origin (PDCompute.CoreSearchLoop.code origin (originalSearchBody origin labels)))
    (stubFetch : program[labels.solveEntry]?=some (.jump (labels.solveEntry+1)))
    (bodyFetch : FetchesCode program (labels.solveEntry+1) (solverCalleeCode .liveHeap (labels.solveEntry+1)))
    (before : State) (position : before.pc=origin) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (P.cachedInitialState P.endpointCache fee))
    (counter : before.heap 28=.natural (P.bisectionBudget fee))
    (safe : RootD27.Bits.SafeBits before (PDCompute.CoreGlobalBudget.budget P fee pcUpper)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤51000*(P.bisectionBudget fee+1)*(P.certificate.M+1)*
        PDCompute.Solver.entryCount P.certificate.stages P.tools ∧
      after.pc=origin+529 ∧ Ready P fee after ∧
      SearchStateRep P fee after (P.buildCachedFrontend fee).state ∧
      after.heap 28=.natural 0 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state (coreSearchRegion P)) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state (PDCompute.CoreGlobalBudget.budget P fee pcUpper)) ∧
      peakCells trace≤workingCells before+PDCompute.CoreMemory.globalSpan
        P.certificate.M P.certificate.stages P.tools ∧
      peakOperandBits trace≤PDCompute.CoreGlobalBudget.budget P fee pcUpper ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace≤P.bisectionBudget fee ∧
      [0,P.Lambda]++actualSolveRequests labels trace=
        (P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2 ∧
      SolverCallRefinement program labels P fee 40000 trace ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=(actualSolveRequests labels trace).length := by
  let entries:=PDCompute.Solver.entryCount P.certificate.stages P.tools
  have actualBody:=original_body_calls program labels input P fee origin pcUpper endBound belowEntry
    solverOrigin solverLength markerLabel stubFetch bodyFetch
  have exitIdentity : exitPC origin (originalSearchBody origin labels)=origin+529 := by
    simp only [exitPC,originalSearchBody_length,Nat.add_assoc]
  have counterInside : 28∈coreSearchRegion P:=scalar_subset_coreSearch P (by decide)
  have pcBits : natBits (exitPC origin (originalSearchBody origin labels))≤
      PDCompute.CoreGlobalBudget.budget P fee pcUpper := by
    rw [exitIdentity]
    exact PDCompute.CoreGlobalBudget.budget_pc P fee pcUpper _ endBound
  obtain ⟨trace,after,head,last,chain,cost,pc,afterReady,afterRep,afterCounter,output,memory,bits,
    count,space,requests,calls,countExact⟩:=
    search_loop_calls_trace program labels input P fee origin (originalSearchBody origin labels)
      (PDCompute.CoreGlobalBudget.budget P fee pcUpper) (coreSearchRegion P)
      (50000*(P.certificate.M+1)*entries) 40000 fetched actualBody counterInside
      (PDCompute.CoreGlobalBudget.budget_small P fee pcUpper) pcBits (by rw [exitIdentity];exact belowEntry)
      before position ready represented counter safe
  have positive : 0<(P.certificate.M+1)*entries := by unfold entries PDCompute.Solver.entryCount;positivity
  have perRound : 50000*(P.certificate.M+1)*entries+300≤51000*((P.certificate.M+1)*entries) := by
    simp only [Nat.mul_assoc]
    omega
  have totalCost:=cost.trans (Nat.mul_le_mul_left (P.bisectionBudget fee+1) perRound)
  rw [exitIdentity] at pc
  refine ⟨trace,after,head,last,chain,?_,pc,afterReady,afterRep,afterCounter,output,memory,bits,?_,
    PDCompute.Pack.safeBits_peak _ _ bits,count,requests,calls,countExact⟩
  · convert totalCost using 1; ring
  · simpa only [coreSearchRegion,PDCompute.CoreMemory.globalRegion_card] using space

end RootD27.Core
