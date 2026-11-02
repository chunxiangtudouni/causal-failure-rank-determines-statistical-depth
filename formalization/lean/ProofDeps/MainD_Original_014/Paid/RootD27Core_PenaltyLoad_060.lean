module

public import Paid.RootD27Core_SolvedBufferFrame_059

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDMenu.ComputeFrame
open PDCompute.Solver hiding HeapList
open PDLower.CalibrationCompute (HeapList loadSlot loadSlotResult linearExecute)

/-- Reuse the original three-instruction heap load. The source penalty
is physically read from the live scalar header; neither code nor an
additional input carries the answer. Every prefix is actually readonly. -/
theorem header_penalty_load_actual (program : Program) (input : List Cell) (before : State)
    (values : ℕ→Cell) (slot : ℕ) (penalty : ℚ) (header : Header before 0 values)
    (inside : slot<headerWords) (fresh : before.register .fresh=.natural 0)
    (value : values slot=.rational penalty)
    (fetched : FetchesCode program before.pc (loadSlot slot .total)) :
    ∃ trace : List State,
      trace.head?=some before ∧ trace.getLast?=some (loadSlotResult before 0 slot .total) ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤60 ∧
      (loadSlotResult before 0 slot .total).register .total=.rational penalty ∧
      (loadSlotResult before 0 slot .total).register .fresh=.natural 0 ∧
      (∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ state.output=before.output) ∧
      (∀ state∈trace,before.pc≤state.pc ∧ state.pc≤before.pc+3) := by
  let code:=loadSlot slot .total
  let after:=loadSlotResult before 0 slot .total
  have executed:=(header.loadSlot_execute input slot .total inside fresh).1
  have penaltyLoaded:=(header.loadSlot_execute input slot .total inside fresh).2.trans value
  have freshLoaded:=(loadSlotResult_fresh before 0 slot .total (by decide)).trans fresh
  obtain ⟨trace,head,last,chain,cost,prefixes⟩:=linearExecute_trace_time program input code
    (loadSlot_straight slot .total) before after fetched executed
  have readonly : code.all PDLower.CalibrationCompute.readOnly=true:=rfl
  have finalPC : after.pc=before.pc+3:=rfl
  refine ⟨trace,head,last,chain,cost,penaltyLoaded,freshLoaded,?_,?_⟩
  · intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,_bound,actual⟩:=prefixes state proper
      have safe : (code.take count).all PDLower.CalibrationCompute.readOnly=true := by
        apply List.all_eq_true.mpr
        intro instruction member
        exact (List.all_eq_true.mp readonly) instruction (List.mem_of_mem_take member)
      exact PDLower.CalibrationCompute.linearReadOnly_heap input _ before state safe actual
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      exact ⟨rfl,rfl,rfl⟩
  · intro state member
    have split:=List.dropLast_append_getLast? after (by rw [last];simp)
    rw [←split] at member
    rcases List.mem_append.mp member with proper|terminal
    · obtain ⟨count,bound,actual⟩:=prefixes state proper
      have straight : StraightCode (code.take count):=
        fun instruction member=>loadSlot_straight slot .total instruction (List.mem_of_mem_take member)
      have pc:=linearExecute_pc input _ straight before state actual
      simp only [List.length_take,Nat.min_eq_left bound.le] at pc
      change count<3 at bound
      omega
    · have same : state=after:=List.mem_singleton.mp terminal
      subst state
      omega

end RootD27.Core
