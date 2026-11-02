module

public import Paid.PDCompute_CoreLoopScope_Iteration_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDCompute.CoreLoopScope

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDMenu.ComputeFrame RootD27.Core PDCompute.CoreSearchLoop

/-- Actual remaining-counter induction, not an unrolled synthetic source
trace. The single physical region and numerical budget do not grow. -/
theorem remaining_calls_trace (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin : ℕ) (body : List Instruction)
    (budget : ℕ) (region : Finset ℕ) (bodyCost callConstant : ℕ)
    (fetched : FetchesCode program origin (code origin body))
    (bodySpec : CallBodyLowerSpec program labels input P fee origin body budget region bodyCost callConstant)
    (counterInside : 28∈region) (room : 7≤budget) (pcBits : natBits (exitPC origin body)≤budget)
    (belowEntry : exitPC origin body<labels.solveEntry)
    (remaining j : ℕ) (finish : j+remaining=P.bisectionBudget fee)
    (before : State) (position : before.pc=origin) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (source P fee j))
    (counter : before.heap 28=.natural remaining) (safe : RootD27.Bits.SafeBits before budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤remaining*(bodyCost+300)+90 ∧
      after.pc=exitPC origin body ∧ Ready P fee after ∧
      SearchStateRep P fee after (source P fee (P.bisectionBudget fee)) ∧
      after.heap 28=.natural 0 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state region) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace≤remaining ∧
      actualSolveRequests labels trace=tailRequests P fee j remaining ∧
      SolverCallRefinement program labels P fee callConstant trace ∧
      (∀ state∈trace,origin≤state.pc) := by
  induction remaining generalizing j before with
  | zero =>
    let after:=guardResult before origin body 0
    obtain ⟨trace,head,last,chain,cost,memory,bits,scope⟩:=guard_lower_trace program input before origin body 0 budget
      ready.header ready.fresh counter position safe room pcBits fetched
    have unchanged:=guard_result_memory before origin body 0
    have afterRep : SearchStateRep P fee after (source P fee (P.bisectionBudget fee)):=by
      have same : j=P.bisectionBudget fee:=by omega
      rw [←same]
      exact representation_unchanged represented unchanged.1 unchanged.2.1
    have count:=(no_solve_entry labels trace
      (fun state member=>Nat.ne_of_lt (((scope state member).2).trans_lt belowEntry))).2
    exact ⟨trace,after,head,last,chain,by simpa only [Nat.zero_mul,Nat.zero_add] using cost,
      by simp [after,guardResult],guard_result_ready ready origin body 0,afterRep,
      counter,rfl,fun state member=>(memory state member).enlarge (Finset.empty_subset _),bits,by omega,
      (no_solve_entry labels trace (fun state member=>Nat.ne_of_lt (((scope state member).2).trans_lt belowEntry))).1,
      refinement_of_no_entry program labels P fee callConstant trace
        (fun state member=>Nat.ne_of_lt (((scope state member).2).trans_lt belowEntry)),
      fun state member=>(scope state member).1⟩
  | succ remaining ih =>
    obtain ⟨first,next,fh,fl,fc,ft,nextPC,nextReady,nextRep,nextCounter,nextOutput,fm,fb,fcount,frequests,frefinement,fLower⟩:=
      iteration_calls_trace program labels input P fee origin body budget region bodyCost callConstant fetched bodySpec
        counterInside room pcBits belowEntry j remaining finish before position ready represented counter safe
    obtain ⟨later,after,lh,ll,lc,lt,afterPC,afterReady,afterRep,afterCounter,afterOutput,lm,lb,lcount,lrequests,lrefinement,lLower⟩:=
      ih (j:=j+1) (by omega) next nextPC nextReady nextRep nextCounter
        (fb next (List.mem_of_getLast? fl))
    have joined:=joinTrace_spec program input first later before next after (bodyCost+300)
      (remaining*(bodyCost+300)+90) fh fl lh ll fc lc ft lt
    have count:=join_entries_le labels first later next fl
    have nextOutside : next.pc≠labels.solveEntry:=by
      rw [nextPC]
      exact Nat.ne_of_lt ((show origin≤exitPC origin body by unfold exitPC;omega).trans_lt belowEntry)
    have requests:=requests_join labels first later next fl nextOutside
    rw [frequests,lrequests] at requests
    have refinement:=refinement_join program labels P fee callConstant first later next fl lh frefinement lrefinement
    refine ⟨joinTrace first later,after,joined.1,joined.2.1,joined.2.2.1,
      joined.2.2.2.trans ?_,afterPC,afterReady,afterRep,afterCounter,afterOutput.trans nextOutput,
      RegionMemory.join_trace first later before next region fl fm lm,
      PDCompute.Pack.joinTrace_invariant first later (fun state=>RootD27.Bits.SafeBits state budget) fb lb,by omega,
      requests.trans (tailRequests_head P fee j remaining).symm,refinement,
      PDCompute.Pack.joinTrace_invariant first later (fun state=>origin≤state.pc) fLower lLower⟩
    simp only [Nat.succ_mul]
    omega

/-- Original J=P.bisectionBudget fee initialized by the real prepared
caller. BodySpec is a clearly exposed INTERNAL component parameter for
Root's literal code, not a new original solver/search input assumption. -/
theorem search_loop_calls_trace (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin : ℕ) (body : List Instruction)
    (budget : ℕ) (region : Finset ℕ) (bodyCost callConstant : ℕ)
    (fetched : FetchesCode program origin (code origin body))
    (bodySpec : CallBodyLowerSpec program labels input P fee origin body budget region bodyCost callConstant)
    (counterInside : 28∈region) (room : 7≤budget) (pcBits : natBits (exitPC origin body)≤budget)
    (belowEntry : exitPC origin body<labels.solveEntry)
    (before : State) (position : before.pc=origin) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (P.cachedInitialState P.endpointCache fee))
    (counter : before.heap 28=.natural (P.bisectionBudget fee)) (safe : RootD27.Bits.SafeBits before budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤(P.bisectionBudget fee+1)*(bodyCost+300) ∧
      after.pc=exitPC origin body ∧ Ready P fee after ∧
      SearchStateRep P fee after (P.cachedMultiplierSearch P.endpointCache fee (P.bisectionBudget fee)) ∧
      after.heap 28=.natural 0 ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state region) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace≤P.bisectionBudget fee ∧
      peakCells trace≤workingCells before+region.card ∧
      [0,P.Lambda]++actualSolveRequests labels trace=
        (P.cachedSearchWithLog P.endpointCache fee (P.bisectionBudget fee)).2 ∧
      SolverCallRefinement program labels P fee callConstant trace ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace=(actualSolveRequests labels trace).length ∧
      (∀ state∈trace,origin≤state.pc) := by
  obtain ⟨trace,after,head,last,chain,cost,afterPC,afterReady,afterRep,afterCounter,afterOutput,memory,bits,count,requests,refinement,lower⟩:=
    remaining_calls_trace program labels input P fee origin body budget region bodyCost callConstant fetched bodySpec
      counterInside room pcBits belowEntry (P.bisectionBudget fee) 0 (by omega) before position ready represented counter safe
  refine ⟨trace,after,head,last,chain,cost.trans ?_,afterPC,afterReady,afterRep,afterCounter,afterOutput,
    memory,bits,count,?_,?_,refinement,entries_eq_requests program labels P fee callConstant trace refinement,lower⟩
  · rw [Nat.add_mul]
    omega
  · apply PDLower.CalibrationCompute.peakCells_le_of_forall
    intro state member
    exact (memory state member).workingCells_le
  · rw [requests]
    exact tailRequests_full P fee

end PDCompute.CoreLoopScope
