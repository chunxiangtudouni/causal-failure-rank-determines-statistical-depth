module

public import Paid.RootD27Core_InitialSolvedState_062
public import Paid.RootD27Core_SearchInitialize_052

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList)
open PDLower.CoreSearch

/-- Expose actual instruction positions on the SAME scalar macro trace.
The PC bounds support real phase/call counting, in addition to the
precise memory frame. No unrelated successful trace is substituted. -/
theorem scalar_commands_located_actual (commands : List HeaderCommand)
    (program : Program) (input : List Cell) (before : State) (values next : ℕ→Cell)
    (valid : ∀ command∈commands,command.Valid)
    (targets : ∀ command∈commands,commandTarget command∈scalarRegion)
    (header : Header before 0 values) (fresh : before.register .fresh=.natural 0)
    (evaluated : headerEval commands values=some next)
    (fetched : FetchesCode program before.pc (headerCode commands)) :
    ∃ (trace : List State) (after : State),trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧
      time program trace≤15*((headerCode commands).length+1) ∧
      Header after 0 next ∧ after.register .fresh=.natural 0 ∧
      after.pc=before.pc+(headerCode commands).length ∧
      (∀ state∈trace,MemoryFrame scalarRegion before state ∧ HeaderMemory before state 0) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+(headerCode commands).length) := by
  obtain ⟨after,run,afterHeader,afterFresh,pc,_frame,_output⟩:=
    headerCode_realize commands input before 0 0 0 values next valid header fresh evaluated
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input (headerCode commands)
    (headerCode_straight commands) before after fetched run
  refine ⟨trace,after,head,last,chain,cost,afterHeader,afterFresh,pc,?_,?_⟩
  · intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,actual⟩:=prefixes state proper
      exact commands_prefix_scalar_memory commands input before state values next valid targets
        header fresh evaluated count bound.le actual
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact commands_prefix_scalar_memory commands input before after values next valid targets
        header fresh evaluated (headerCode commands).length (le_refl _)
        (by simpa only [List.take_length] using run)
  · intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,actual⟩:=prefixes state proper
      have straight : StraightCode ((headerCode commands).take count):=
        fun instruction member=>headerCode_straight commands instruction (List.mem_of_mem_take member)
      have statePC:=linearExecute_pc input _ straight before state actual
      simp only [List.length_take,Nat.min_eq_left bound.le] at statePC
      omega
    · have same:=List.mem_singleton.mp terminal
      subst state
      omega

theorem scalar_region_memory {before after : State}
    (memory : MemoryFrame scalarRegion before after ∧ HeaderMemory before after 0) :
    RegionMemory before after scalarRegion := by
  refine ⟨memory.1.1,?_,?_,memory.2.2.2⟩
  · rw [memory.2.2.1]
    exact Finset.subset_union_left
  · rw [memory.2.2.1]

end RootD27.Core
