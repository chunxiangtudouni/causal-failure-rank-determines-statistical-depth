module

public import Paid.PDCompute_SolverCandidateMemory_066
public import Paid.PDCompute_SolverScanAdvance_044

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

theorem Header.addNatSlot_trace_memory {before : State} {base : ℕ} {values : ℕ → Cell}
    (header : Header before base values) (program : Program) (input : List Cell) (slot value amount : ℕ)
    (inside : slot < headerWords) (hbase : before.register .fresh=.natural base)
    (hvalue : values slot=.natural value) (fetched : FetchesCode program before.pc (PDCompute.Solver.addNatSlot slot amount)) :
    ∃ trace : List State, trace.head?=some before ∧ trace.getLast?=some (addNatSlotResult before base slot value amount) ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 135 ∧ ∀ state ∈ trace, HeaderMemory before state base := by
  apply linearExecute_trace_memory program input (PDCompute.Solver.addNatSlot slot amount) (addNatSlot_straight slot amount)
    before (addNatSlotResult before base slot value amount) base fetched
    (addNatSlot_execute input before base slot value amount hbase (header.live slot inside)
      ((header.value slot inside).trans hvalue))
  intro count bound state execute
  exact addNatSlot_header_memory input before state base slot value amount values header inside hbase hvalue count bound execute

theorem scanKernel_advance_trace_memory (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (hcode : FetchesCode program origin (scanKernel mode origin)) (before : State)
    (base n k index pointer : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin+95) (header : Header before base values)
    (hbase : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hp : values 39=.natural pointer) :
    ∃ trace : List State, ∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later => step program input first=some later) ∧
      time program trace ≤ 285 ∧ Header after base (scanAdvanceValues values index pointer) ∧
      after.register .fresh=.natural base ∧ after.pc=origin ∧
      Frame before after base n k ∧ after.output=before.output ∧
      ∀ state ∈ trace, HeaderMemory before state base := by
  let first := addNatSlotResult before base 25 index 1
  let second := addNatSlotResult first base 39 pointer 2
  let after : State := {second with pc:=origin}
  have firstFields := addNatSlotResult_fields before base 25 index 1
  have secondFields := addNatSlotResult_fields first base 39 pointer 2
  obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstMemory⟩ :=
    header.addNatSlot_trace_memory program input 25 index 1 (by decide) hbase hi
      (scanKernel_counter_fetch mode program origin hcode before hpc)
  have firstHeader : Header first base (Function.update values 25 (.natural (index+1))) := header.addNatSlot 25 index 1
  have firstBase : first.register .fresh=.natural base := firstFields.2.2.1.trans hbase
  have firstPC : first.pc=origin+103 := firstFields.2.2.2.1.trans (congrArg (·+8) hpc)
  have firstPointer : (Function.update values 25 (.natural (index+1))) 39=.natural pointer := hp
  obtain ⟨secondTrace,secondHead,secondLast,secondChain,secondTime,secondMemory⟩ :=
    firstHeader.addNatSlot_trace_memory program input 39 pointer 2 (by decide) firstBase firstPointer
      (scanKernel_pointer_fetch mode program origin hcode first firstPC)
  have secondPC : second.pc=origin+111 := secondFields.2.2.2.1.trans (congrArg (·+8) firstPC)
  have fetched := scanKernel_back_fetch mode program origin hcode second secondPC
  have control : step program input second=some after := by unfold step; rw [fetched]; rfl
  have joined := joinTrace_spec program input firstTrace secondTrace before first second 135 135
    firstHead firstLast secondHead secondLast firstChain secondChain firstTime secondTime
  have joinedMemory := joinTrace_memory firstTrace secondTrace before first base firstLast firstMemory secondMemory
  have appended := chain_append_control program input (joinTrace firstTrace secondTrace) second after joined.2.2.1 joined.2.1 control
  have afterMemory : HeaderMemory before after base :=
    (HeaderMemory.trace_last joinedMemory joined.2.1).trans (HeaderMemory.of_unchanged base rfl rfl rfl)
  have nonempty : joinTrace firstTrace secondTrace ≠ [] := by
    intro empty
    have head := joined.1
    simp only [empty,List.head?_nil,reduceCtorEq] at head
  refine ⟨joinTrace firstTrace secondTrace++[after],after,?_,by simp,appended.1,?_,firstHeader.addNatSlot 39 pointer 2,
    secondFields.2.2.1.trans firstBase,rfl,
    (addNatSlotResult_frame before base 25 index 1 n k (by decide)).trans
      (addNatSlotResult_frame first base 39 pointer 2 n k (by decide)),
    secondFields.2.2.2.2.trans firstFields.2.2.2.2,
    appendTrace_memory (joinTrace firstTrace secondTrace) before after base joinedMemory afterMemory⟩
  · simpa only [List.head?_append_of_ne_nil _ nonempty] using joined.1
  · have bound := appended.2
    omega

end PDCompute.Solver
