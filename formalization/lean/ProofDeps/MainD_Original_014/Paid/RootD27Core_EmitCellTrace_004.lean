module

public import Paid.RootD27Core_EmitPrimitives_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid.Computation PDMenu.ComputeFrame

theorem emitCell_actual (program : Program) (input : List Cell) (before : State)
    (origin returnPC pointer remaining : ℕ) (value : Cell) (position : before.pc=origin+1)
    (address : before.register .address=.natural pointer)
    (index : before.register .index=.natural (remaining+1))
    (live : pointer∈before.live) (payload : before.heap pointer=value)
    (fetched : FetchesCode program origin (emitHeapCode origin returnPC)) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace≤105 ∧ after.pc=origin ∧
      after.register .address=.natural (pointer+1) ∧ after.register .index=.natural remaining ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output++[value] ∧
      ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧
        (state.output=before.output ∨ state.output=before.output++[value]) := by
  let middle:=emitCellResult before pointer remaining value
  let after : State:={middle with pc:=origin}
  have fetch : FetchesCode program before.pc emitCellCode := by
    rw [position];exact emitHeap_cell_fetch program origin returnPC fetched
  obtain ⟨trace,head,last,chain,bound,prefixes⟩:=linearExecute_trace_time program input emitCellCode
    emitCell_straight before middle fetch (emitCell_execute input before pointer remaining value address index live payload)
  have middlePC : middle.pc=origin+6 := by
    change before.pc+5=origin+6
    omega
  have control : step program input middle=some after := by
    simp only [step,middlePC,emitHeap_jump_fetch program origin returnPC fetched]
    rfl
  have appended:=chain_append_control program input trace middle after chain last control
  have nonempty : trace≠[] := by intro same; simp only [same,List.head?_nil,reduceCtorEq] at head
  refine ⟨trace++[after],after,?_,by simp,appended.1,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using head
  · have short : time program trace≤90 := bound
    exact appended.2.trans (Nat.add_le_add_right short 15)
  · intro state member
    rcases List.mem_append.mp member with prior|final
    · have split:=List.dropLast_append_getLast? middle (by rw [last];simp)
      rw [←split] at prior
      rcases List.mem_append.mp prior with proper|terminal
      · obtain ⟨count,inside,executed⟩:=prefixes state proper
        exact emitCell_prefix input before state pointer count value address live payload inside executed
      · have same : state=middle := by simpa only [List.mem_singleton] using terminal
        subst state
        exact ⟨rfl,rfl,Or.inr rfl⟩
    · have same : state=after := by simpa only [List.mem_singleton] using final
      subst state
      exact ⟨rfl,rfl,Or.inr rfl⟩

end RootD27.Core
