module

public import Paid.RootD27Core_RootStatistics_043

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList linearExecute)

theorem rootStatistics_prefix_memory (input : List Cell) (before after : State) (target source menu stepsTaken : ℕ)
    (observation repairs failure : ℚ) (lower : 13≤target) (upper : target+2<46) (sourceBound : 51≤source)
    (address : before.register .address=.natural source)
    (root : HeapList before (source-3) [.rational observation,.rational repairs,.rational failure])
    (menuLive : 7∈before.live) (menuValue : before.heap 7=.natural menu)
    (bound : stepsTaken≤20)
    (actual : linearExecute input ((rootStatisticsCode target).take stepsTaken) before=some after) :
    RegionMemory before after {target,target+1,target+2} := by
  have ol:=root.1 0 (by change 0<3;decide)
  have rl:=root.1 1 (by change 1<3;decide)
  have fl:=root.1 2 (by change 2<3;decide)
  have ov:=PDLower.CalibrationCompute.HeapList.value root 0 (by change 0<3;decide)
  have rv:=PDLower.CalibrationCompute.HeapList.value root 1 (by change 1<3;decide)
  have fv:=PDLower.CalibrationCompute.HeapList.value root 2 (by change 2<3;decide)
  simp only [Nat.add_zero,List.getElem_cons_zero,List.getElem_cons_succ] at ol ov rv fv
  have r1 : source-3+1≠target:=by omega
  have r2 : source-3+2≠target:=by omega
  have s2 : source-3+2≠target+1:=by omega
  have t0 : 7≠target:=by omega
  have t1 : 7≠target+1:=by omega
  have t2 : 7≠target+2:=by omega
  have arithmetic : menu*2+99=99+2*menu:=by omega
  interval_cases stepsTaken <;>
    simp [rootStatisticsCode,linearExecute,Instruction.execute,State.set,NatOp.eval,Cell.nat?,
      address,ol,rl,fl,ov,rv,fv,menuLive,menuValue,r1,r2,s2,t0,t1,t2,arithmetic,Nat.add_assoc] at actual <;> subst after
  all_goals
    refine ⟨?_,?_,?_,rfl⟩
    · intro query outside
      have q0 : query≠target:=by intro same;subst query;simp at outside
      have q1 : query≠target+1:=by intro same;subst query;simp at outside
      have q2 : query≠target+2:=by intro same;subst query;simp at outside
      simp_all
    · intro query member
      simp only [Finset.mem_insert,Finset.mem_union,Finset.mem_singleton] at member ⊢
      tauto
    · first
      | exact Finset.Subset.refl _
      | exact Finset.subset_insert _ _
      | exact (Finset.subset_insert _ _).trans (Finset.subset_insert _ _)
      | exact ((Finset.subset_insert _ _).trans (Finset.subset_insert _ _)).trans (Finset.subset_insert _ _)

/-- Same physical twenty-op root loads/stores, exact returned registers,
all-prefix memory footprint and peak increase of at most three cells. -/
theorem rootStatistics_actual (program : Program) (input : List Cell) (before : State)
    (target source menu : ℕ) (observation repairs failure : ℚ)
    (lower : 13≤target) (upper : target+2<46) (sourceBound : 51≤source)
    (address : before.register .address=.natural source)
    (root : HeapList before (source-3) [.rational observation,.rational repairs,.rational failure])
    (menuLive : 7∈before.live) (menuValue : before.heap 7=.natural menu)
    (fetched : FetchesCode program before.pc (rootStatisticsCode target)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (rootStatisticsResult before target menu observation repairs failure) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤315 ∧
      (∀ state∈trace,RegionMemory before state {target,target+1,target+2}) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+20) ∧
      peakCells trace≤workingCells before+3 := by
  have executed:=rootStatistics_execute input before target source menu observation repairs failure
    lower upper sourceBound address root menuLive menuValue
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input _
    (rootStatistics_straight target) before _ fetched executed
  have memory : ∀ state∈trace,RegionMemory before state {target,target+1,target+2} := by
    intro state member
    have split:=List.dropLast_append_getLast? (rootStatisticsResult before target menu observation repairs failure)
      (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨stepsTaken,bound,actual⟩:=prefixes state proper
      exact rootStatistics_prefix_memory input before state target source menu stepsTaken observation repairs failure
        lower upper sourceBound address root menuLive menuValue (by simpa only [rootStatistics_length] using bound.le) actual
    · exact rootStatistics_prefix_memory input before state target source menu 20 observation repairs failure
        lower upper sourceBound address root menuLive menuValue (le_refl _) (by
          have same : state=rootStatisticsResult before target menu observation repairs failure:=List.mem_singleton.mp terminal
          subst state
          rw [←rootStatistics_length target,List.take_length]
          exact executed)
  have pcs : ∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+20 := by
    intro state member
    have split:=List.dropLast_append_getLast? (rootStatisticsResult before target menu observation repairs failure)
      (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨stepsTaken,bound,actual⟩:=prefixes state proper
      have straight : StraightCode ((rootStatisticsCode target).take stepsTaken) :=
        fun instruction inside=>rootStatistics_straight target instruction (List.mem_of_mem_take inside)
      have pc:=linearExecute_pc input _ straight before state actual
      simp only [List.length_take,Nat.min_eq_left bound.le] at pc
      rw [rootStatistics_length] at bound
      omega
    · have same : state=rootStatisticsResult before target menu observation repairs failure:=List.mem_singleton.mp terminal
      subst state
      change before.pc≤before.pc+20 ∧ before.pc+20≤before.pc+20
      omega
  refine ⟨trace,head,last,chain,cost,memory,pcs,?_⟩
  have notFirst : target∉({target+1,target+2} : Finset ℕ) := by
    simp only [Finset.mem_insert,Finset.mem_singleton]
    omega
  have notSecond : target+1∉({target+2} : Finset ℕ) := by
    simp only [Finset.mem_singleton]
    omega
  have card : ({target,target+1,target+2} : Finset ℕ).card=3 := by
    rw [Finset.card_insert_of_notMem notFirst,Finset.card_insert_of_notMem notSecond,Finset.card_singleton]
  apply PDLower.CalibrationCompute.peakCells_le_of_forall
  intro state member
  simpa only [card] using (memory state member).workingCells_le

end RootD27.Core
