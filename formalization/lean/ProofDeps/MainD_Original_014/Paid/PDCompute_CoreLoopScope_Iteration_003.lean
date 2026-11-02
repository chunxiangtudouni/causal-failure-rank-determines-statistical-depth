module

public import Paid.PDCompute_CoreSearchLoop_Preserve_004
public import Paid.PDCompute_CoreLoopScope_Guard_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1100000

@[expose] public section

namespace PDCompute.CoreLoopScope

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver hiding HeapList
open PDMenu.ComputeFrame RootD27.Core PDROC.DataBits PDCompute.CoreSearchLoop

/-- One real positive-counter iteration: guard, certified original body,
literal eight-op decrement, actual jump back. A stopped source still
decrements the real counter; it is not treated as an early outer exit. -/
theorem iteration_calls_trace (program : Program) (labels : RoutineLabels) (input : List Cell)
    (P : Parameters) (fee : ℚ) (origin : ℕ) (body : List Instruction)
    (budget : ℕ) (region : Finset ℕ) (bodyCost callConstant : ℕ)
    (fetched : FetchesCode program origin (code origin body))
    (bodySpec : CallBodyLowerSpec program labels input P fee origin body budget region bodyCost callConstant)
    (counterInside : 28∈region) (room : 7≤budget) (pcBits : natBits (exitPC origin body)≤budget)
    (belowEntry : exitPC origin body<labels.solveEntry)
    (j remaining : ℕ) (finish : j+(remaining+1)=P.bisectionBudget fee)
    (before : State) (position : before.pc=origin) (ready : Ready P fee before)
    (represented : SearchStateRep P fee before (source P fee j))
    (counter : before.heap 28=.natural (remaining+1)) (safe : RootD27.Bits.SafeBits before budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤bodyCost+300 ∧
      after.pc=origin ∧ Ready P fee after ∧ SearchStateRep P fee after (source P fee (j+1)) ∧
      after.heap 28=.natural remaining ∧ after.output=before.output ∧
      (∀ state∈trace,RegionMemory before state region) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) ∧
      PaperProofs.Paid.Computation.entryCount labels.solveEntry trace≤1 ∧
      actualSolveRequests labels trace=P.nextSolveRequests fee (source P fee j) ∧
      SolverCallRefinement program labels P fee callConstant trace ∧
      (∀ state∈trace,origin≤state.pc) := by
  let tested:=guardResult before origin body (remaining+1)
  obtain ⟨guard,gh,gl,gc,gt,gm,gb,gpc⟩:=guard_lower_trace program input before origin body (remaining+1) budget
    ready.header ready.fresh counter position safe room pcBits fetched
  have testedPC : tested.pc=bodyPC origin:=by simp [tested,guardResult]
  have testedReady : Ready P fee tested:=guard_result_ready ready origin body (remaining+1)
  have testedMemory:=guard_result_memory before origin body (remaining+1)
  have testedRep : SearchStateRep P fee tested (source P fee j):=
    representation_unchanged represented testedMemory.1 testedMemory.2.1
  have testedCounter : tested.heap 28=.natural (P.bisectionBudget fee-j):=by
    change before.heap 28=_
    rw [counter]
    congr 1
    omega
  have testedFetch : FetchesCode program tested.pc body:=by
    rw [testedPC]
    exact body_fetch program origin body fetched
  obtain ⟨middle,written,mh,ml,mc,mt,wpc,wr,wp,wcounter,woutput,wm,wb,wcount,mrequests,mrefinement,bodyLower⟩:=
    bodySpec j (by omega) tested testedPC testedReady testedRep testedCounter
      (gb tested (List.mem_of_getLast? gl)) testedFetch
  have writtenCounter : written.heap 28=.natural (remaining+1):=wcounter.trans counter
  have writtenSafe:=wb written (List.mem_of_getLast? ml)
  have decrFetch : FetchesCode program written.pc decrementCode:=by
    rw [wpc]
    exact decrement_fetch program origin body fetched
  have decrBits : natBits (written.pc+8)≤budget:=
    (natBits_mono (by rw [wpc];unfold decrementPC exitPC;omega : written.pc+8≤exitPC origin body)).trans pcBits
  let decremented:=decrementResult written remaining
  obtain ⟨decr,dh,dl,dc,dt,dm,db,dpc⟩:=decrement_trace program input written remaining budget
    wr.header wr.fresh writtenCounter writtenSafe room decrBits decrFetch
  have decrReady : Ready P fee decremented:=decrement_ready wr remaining
  have decrRep : SearchStateRep P fee decremented (source P fee (j+1)):=
    representation_counter wp (decrement_region written remaining)
  have decrPC : decremented.pc=backPC origin body:=by
    change written.pc+8=_
    rw [wpc]
    unfold decrementPC backPC
    omega
  have jumpFetch : program[decremented.pc]?=some (.jump origin):=by
    rw [decrPC]
    exact back_fetch program origin body fetched
  let after:=jumpResult decremented origin
  let back:=[decremented,after]
  obtain ⟨jh,jl,jc,jt,jm⟩:=jump_trace_storage program input decremented origin jumpFetch
  have afterReady : Ready P fee after:=ready_jump decrReady origin
  have afterRep : SearchStateRep P fee after (source P fee (j+1)):=representation_unchanged decrRep rfl rfl
  have afterSafe : RootD27.Bits.SafeBits after budget:=
    (db decremented (List.mem_of_getLast? dl)).withPC origin
      ((natBits_mono (by unfold exitPC;omega : origin≤exitPC origin body)).trans pcBits)
  have jumpBits : ∀ state∈back,RootD27.Bits.SafeBits state budget:=by
    intro state member
    simp only [back,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state
      exact db decremented (List.mem_of_getLast? dl)
    · subst state
      exact afterSafe
  have guardMemory : ∀ state∈guard,RegionMemory before state region:=
    fun state member=>(gm state member).enlarge (Finset.empty_subset _)
  have decrMemory : ∀ state∈decr,RegionMemory written state region:=
    fun state member=>(dm state member).enlarge (Finset.singleton_subset_iff.mpr counterInside)
  have jumpMemory : ∀ state∈back,RegionMemory decremented state region:=by
    intro state member
    have same:=jm state member
    exact unchanged_region region same.1 same.2.1 same.2.2
  have guardCount : PaperProofs.Paid.Computation.entryCount labels.solveEntry guard=0:=
    (no_solve_entry labels guard (fun state member=>Nat.ne_of_lt (((gpc state member).2).trans_lt belowEntry))).2
  have decrCount : PaperProofs.Paid.Computation.entryCount labels.solveEntry decr=0:=by
    apply (no_solve_entry labels decr ?_).2
    intro state member
    have bound:=(dpc state member).2
    have upper : written.pc+8≤exitPC origin body:=by rw [wpc];unfold decrementPC exitPC;omega
    exact Nat.ne_of_lt ((bound.trans upper).trans_lt belowEntry)
  have jumpCount : PaperProofs.Paid.Computation.entryCount labels.solveEntry back=0:=by
    apply (no_solve_entry labels back ?_).2
    intro state member
    have bound : state.pc≤exitPC origin body:=by
      simp only [back,List.mem_cons,List.not_mem_nil,or_false] at member
      rcases member with same|same
      · subst state
        rw [decrPC]
        unfold backPC exitPC
        omega
      · subst state
        change origin≤exitPC origin body
        unfold exitPC
        omega
    exact Nat.ne_of_lt (bound.trans_lt belowEntry)
  have join1:=joinTrace_spec program input guard middle before tested written 90 bodyCost
    gh gl mh ml gc mc gt mt
  have memory1:=RegionMemory.join_trace guard middle before tested region gl guardMemory wm
  have bits1:=PDCompute.Pack.joinTrace_invariant guard middle (fun state=>RootD27.Bits.SafeBits state budget) gb wb
  have entries1:=join_entries_le labels guard middle tested gl
  have join2:=joinTrace_spec program input (joinTrace guard middle) decr before written decremented
    (90+bodyCost) 135 join1.1 join1.2.1 dh dl join1.2.2.1 dc join1.2.2.2 dt
  have memory2:=RegionMemory.join_trace (joinTrace guard middle) decr before written region join1.2.1 memory1 decrMemory
  have bits2:=PDCompute.Pack.joinTrace_invariant (joinTrace guard middle) decr
    (fun state=>RootD27.Bits.SafeBits state budget) bits1 db
  have entries2:=join_entries_le labels (joinTrace guard middle) decr written join1.2.1
  have join3:=joinTrace_spec program input (joinTrace (joinTrace guard middle) decr) back before decremented after
    ((90+bodyCost)+135) 30 join2.1 join2.2.1 jh jl join2.2.2.1 jc join2.2.2.2 jt
  have entries3:=join_entries_le labels (joinTrace (joinTrace guard middle) decr) back decremented join2.2.1
  have emptyResources (states : List State) (zero : PaperProofs.Paid.Computation.entryCount labels.solveEntry states=0) :
      actualSolveRequests labels states=[] ∧ SolverCallRefinement program labels P fee callConstant states:=by
    have empty : states.filter (fun state=>state.pc==labels.solveEntry)=[]:=List.length_eq_zero_iff.mp zero
    have excluded : ∀ state∈states,state.pc≠labels.solveEntry:=by
      intro state member position
      have filtered : state∈states.filter (fun state=>state.pc==labels.solveEntry):=
        List.mem_filter.mpr ⟨member,by simp [position]⟩
      rw [empty] at filtered
      exact False.elim (List.not_mem_nil filtered)
    exact ⟨(no_solve_entry labels states excluded).1,
      refinement_of_no_entry program labels P fee callConstant states excluded⟩
  have guardExtra:=emptyResources guard guardCount
  have decrExtra:=emptyResources decr decrCount
  have jumpExtra:=emptyResources back jumpCount
  have testedOutside : tested.pc≠labels.solveEntry:=by
    exact Nat.ne_of_lt (((gpc tested (List.mem_of_getLast? gl)).2).trans_lt belowEntry)
  have writtenOutside : written.pc≠labels.solveEntry:=by
    have bound : written.pc≤exitPC origin body:=by rw [wpc];unfold decrementPC exitPC;omega
    exact Nat.ne_of_lt (bound.trans_lt belowEntry)
  have decrOutside : decremented.pc≠labels.solveEntry:=by
    have bound : decremented.pc≤exitPC origin body:=by rw [decrPC];unfold backPC exitPC;omega
    exact Nat.ne_of_lt (bound.trans_lt belowEntry)
  have request1:=requests_join labels guard middle tested gl testedOutside
  rw [guardExtra.1,mrequests,List.nil_append] at request1
  have request2:=requests_join labels (joinTrace guard middle) decr written join1.2.1 writtenOutside
  rw [request1,decrExtra.1,List.append_nil] at request2
  have request3:=requests_join labels (joinTrace (joinTrace guard middle) decr) back decremented join2.2.1 decrOutside
  rw [request2,jumpExtra.1,List.append_nil] at request3
  have refinement1:=refinement_join program labels P fee callConstant guard middle tested gl mh guardExtra.2 mrefinement
  have refinement2:=refinement_join program labels P fee callConstant (joinTrace guard middle) decr written
    join1.2.1 dh refinement1 decrExtra.2
  have refinement3:=refinement_join program labels P fee callConstant (joinTrace (joinTrace guard middle) decr) back
    decremented join2.2.1 jh refinement2 jumpExtra.2
  have decrLower : ∀ state∈decr,origin≤state.pc := by
    intro state member
    have base : origin≤written.pc:=by rw [wpc];unfold decrementPC;omega
    exact base.trans (dpc state member).1
  have backLower : ∀ state∈back,origin≤state.pc := by
    intro state member
    simp only [back,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with same|same
    · subst state
      rw [decrPC]
      unfold backPC
      omega
    · subst state
      exact le_refl origin
  have lower1:=PDCompute.Pack.joinTrace_invariant guard middle (fun state=>origin≤state.pc)
    (fun state member=>(gpc state member).1) bodyLower
  have lower2:=PDCompute.Pack.joinTrace_invariant (joinTrace guard middle) decr
    (fun state=>origin≤state.pc) lower1 decrLower
  have lower3:=PDCompute.Pack.joinTrace_invariant (joinTrace (joinTrace guard middle) decr) back
    (fun state=>origin≤state.pc) lower2 backLower
  refine ⟨joinTrace (joinTrace (joinTrace guard middle) decr) back,after,join3.1,join3.2.1,join3.2.2.1,
    join3.2.2.2.trans (by omega),rfl,afterReady,afterRep,?_,?_,
    RegionMemory.join_trace _ back before decremented region join2.2.1 memory2 jumpMemory,
    PDCompute.Pack.joinTrace_invariant _ back (fun state=>RootD27.Bits.SafeBits state budget) bits2 jumpBits,?_,request3,refinement3,lower3⟩
  · simp [after,jumpResult,decremented,decrementResult]
  · exact woutput.trans rfl
  · rw [guardCount] at entries1
    rw [decrCount] at entries2
    rw [jumpCount] at entries3
    omega

end PDCompute.CoreLoopScope
