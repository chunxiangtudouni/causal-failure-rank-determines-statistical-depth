module

public import Paid.PDCompute_SolverEmitPrefixBits_207

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 850000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame
open PDLower.CalibrationCompute (linearExecute)

/-- Same real FIVE-op output body and fetched literal backjump,
preserving its original heap/output prefix facts and all-state bits. -/
theorem emitCell_trace_resources (program : Program) (input : List Cell) (before : State)
    (origin returnPC pointer remaining budget : ℕ) (value : Cell) (position : before.pc=origin+1)
    (address : before.register .address=.natural pointer) (index : before.register .index=.natural (remaining+1))
    (live : pointer∈before.live) (payload : before.heap pointer=value)
    (fetch : FetchesCode program origin (RootD27.Core.emitHeapCode origin returnPC)) (safe : RootD27.Bits.SafeBits before budget)
    (oneBits : (.natural 1 : Cell).bits≤budget) (pointerBits : 1+natBits (pointer+1)≤budget) (pcBits : natBits (origin+7)≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤105 ∧
      after.pc=origin ∧ after.register .address=.natural (pointer+1) ∧ after.register .index=.natural remaining ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output++[value] ∧
      (∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ (state.output=before.output ∨ state.output=before.output++[value])) ∧
      (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let middle:=RootD27.Core.emitCellResult before pointer remaining value
  let after : State:={middle with pc:=origin}
  have bodyFetch : FetchesCode program before.pc RootD27.Core.emitCellCode := by rw [position];exact RootD27.Core.emitHeap_cell_fetch program origin returnPC fetch
  have run:=RootD27.Core.emitCell_execute input before pointer remaining value address index live payload
  have safePrefixes:=emitCellCode_prefix_safe input before pointer remaining budget value address index live payload safe oneBits pointerBits
    ((natBits_mono (by rw [position];omega : before.pc+5≤origin+7)).trans pcBits)
  obtain ⟨trace,head,last,chain,cost,resources⟩:=PDCompute.Pack.linearExecute_trace_invariant program input RootD27.Core.emitCellCode RootD27.Core.emitCell_straight
    before middle bodyFetch run
    (fun state=>(state.heap=before.heap ∧ state.live=before.live ∧ (state.output=before.output ∨ state.output=before.output++[value])) ∧ RootD27.Bits.SafeBits state budget) (by
      intro count bound state executed
      have storage : state.heap=before.heap ∧ state.live=before.live ∧ (state.output=before.output ∨ state.output=before.output++[value]) := by
        by_cases full : count=5
        · subst count
          change linearExecute input RootD27.Core.emitCellCode before=some state at executed
          rw [run] at executed
          have same:=Option.some.inj executed
          subst state
          exact ⟨rfl,rfl,Or.inr rfl⟩
        · exact RootD27.Core.emitCell_prefix input before state pointer count value address live payload (by change count≤5 at bound;omega) executed
      exact ⟨storage,safePrefixes count state executed⟩)
  have memory : ∀ state∈trace,state.heap=before.heap ∧ state.live=before.live ∧ (state.output=before.output ∨ state.output=before.output++[value]) :=
    fun state member=>(resources state member).1
  have bounded : ∀ state∈trace,RootD27.Bits.SafeBits state budget := fun state member=>(resources state member).2
  have middlePC : middle.pc=origin+6 := by change before.pc+5=origin+6;omega
  have actual : step program input middle=some after := by
    simp only [step,middlePC,RootD27.Core.emitHeap_jump_fetch program origin returnPC fetch]
    rfl
  have afterSafe:=PDCompute.Pack.jump_execute_safe input middle after origin budget (bounded middle (List.mem_of_getLast? last))
    ((natBits_mono (by omega : origin≤origin+7)).trans pcBits) rfl
  have appended:=chain_append_control program input trace middle after chain last actual
  have nonempty : trace≠[] := by intro empty;rw [empty] at head;cases head
  refine ⟨trace++[after],after,?_,by simp,appended.1,?_,rfl,rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil trace nonempty] using head
  · have bodyBound : time program trace≤90 := cost
    exact appended.2.trans (Nat.add_le_add_right bodyBound 15)
  · intro state member
    rcases List.mem_append.mp member with prior|terminal
    · exact memory state prior
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact ⟨rfl,rfl,Or.inr rfl⟩
  · intro state member
    rcases List.mem_append.mp member with prior|terminal
    · exact bounded state prior
    · have same:=List.mem_singleton.mp terminal
      subst state
      exact afterSafe

end PDCompute.Solver
