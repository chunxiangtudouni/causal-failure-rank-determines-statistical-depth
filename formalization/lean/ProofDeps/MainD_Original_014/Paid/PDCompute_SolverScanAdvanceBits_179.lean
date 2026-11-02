module

public import Paid.PDCompute_Nat_IncrementResources_016
public import Paid.PDCompute_SolverAdvanceMemory_067

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 750000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation PDROC.DataBits PDMenu.ComputeFrame

/-- The real index/cursor increments and real original back-edge.
The ROM cursor is bounded by its own source address, not by workspace. -/
theorem scanKernel_advance_trace_bits (mode : ReaderMode) (program : Program) (input : List Cell) (origin : ℕ)
    (fetch : FetchesCode program origin (scanKernel mode origin)) (before : State)
    (base n k index pointer budget : ℕ) (values : ℕ → Cell)
    (hpc : before.pc=origin+95) (header : Header before base values) (fresh : before.register .fresh=.natural base)
    (hi : values 25=.natural index) (hp : values 39=.natural pointer) (safe : RootD27.Bits.SafeBits before budget)
    (small : 4≤budget) (addressBits : 1+natBits (base+headerWords)≤budget)
    (indexBits : 1+natBits (index+1)≤budget) (pointerBits : 1+natBits (pointer+2)≤budget)
    (pcBits : natBits (origin+112)≤budget) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧ trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤285 ∧
      Header after base (scanAdvanceValues values index pointer) ∧ after.register .fresh=.natural base ∧ after.pc=origin ∧
      Frame before after base n k ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,RootD27.Bits.SafeBits state budget) := by
  let first:=addNatSlotResult before base 25 index 1
  let second:=addNatSlotResult first base 39 pointer 2
  let after : State:={second with pc:=origin}
  have slotBits (slot : ℕ) (inside : slot<headerWords) : 1+natBits (base+slot)≤budget :=
    (Nat.add_le_add_left (natBits_mono (by omega : base+slot≤base+headerWords)) 1).trans addressBits
  have literalOne : (.natural 1 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have literalTwo : (.natural 2 : Cell).bits≤budget := by norm_num [Cell.bits,natBits]; omega
  have firstCounter : natBits (before.pc+8)≤budget :=
    (natBits_mono (by rw [hpc]; omega : before.pc+8≤origin+112)).trans pcBits
  obtain ⟨firstTrace,firstHead,firstLast,firstChain,firstTime,firstHeader,firstBase,firstPC,firstFrame,firstOutput,firstResources⟩:=
    PDCompute.NatControl.addNatSlot_trace_resources program input before base n k 25 index 1 budget values header fresh (by decide) hi safe
      (slotBits 25 (by decide)) literalOne indexBits firstCounter (scanKernel_counter_fetch mode program origin fetch before hpc)
  have firstMemory : ∀ state∈firstTrace,HeaderMemory before state base := fun state member=>(firstResources state member).1
  have firstSafe : ∀ state∈firstTrace,RootD27.Bits.SafeBits state budget := fun state member=>(firstResources state member).2.1
  have atSecond : first.pc=origin+103 := firstPC.trans (congrArg (·+8) hpc)
  have firstPointer : (Function.update values 25 (.natural (index+1))) 39=.natural pointer := hp
  have secondCounter : natBits (first.pc+8)≤budget :=
    (natBits_mono (by rw [atSecond]; omega : first.pc+8≤origin+112)).trans pcBits
  obtain ⟨secondTrace,secondHead,secondLast,secondChain,secondTime,secondHeader,secondBase,secondPC,secondFrame,secondOutput,secondResources⟩:=
    PDCompute.NatControl.addNatSlot_trace_resources program input first base n k 39 pointer 2 budget (Function.update values 25 (.natural (index+1)))
      firstHeader firstBase (by decide) firstPointer (firstSafe first (List.mem_of_getLast? firstLast))
      (slotBits 39 (by decide)) literalTwo pointerBits secondCounter (scanKernel_pointer_fetch mode program origin fetch first atSecond)
  have secondMemory : ∀ state∈secondTrace,HeaderMemory first state base := fun state member=>(secondResources state member).1
  have secondSafe : ∀ state∈secondTrace,RootD27.Bits.SafeBits state budget := fun state member=>(secondResources state member).2.1
  have atBack : second.pc=origin+111 := secondPC.trans (congrArg (·+8) atSecond)
  have actual : step program input second=some after := by
    unfold step
    rw [scanKernel_back_fetch mode program origin fetch second atBack]
    rfl
  have afterSafe : RootD27.Bits.SafeBits after budget := (secondSafe second (List.mem_of_getLast? secondLast)).withPC _
    ((natBits_mono (by omega : origin≤origin+112)).trans pcBits)
  have joined:=joinTrace_spec program input firstTrace secondTrace before first second 135 135 firstHead firstLast secondHead secondLast firstChain secondChain firstTime secondTime
  have allMemory:=joinTrace_memory firstTrace secondTrace before first base firstLast firstMemory secondMemory
  have allSafe:=PDCompute.Pack.joinTrace_invariant firstTrace secondTrace (fun state=>RootD27.Bits.SafeBits state budget) firstSafe secondSafe
  have appended:=chain_append_control program input (joinTrace firstTrace secondTrace) second after joined.2.2.1 joined.2.1 actual
  have afterMemory : HeaderMemory before after base := (HeaderMemory.trace_last allMemory joined.2.1).trans (HeaderMemory.of_unchanged base rfl rfl rfl)
  have nonempty : joinTrace firstTrace secondTrace≠[] := by intro empty; have hh:=joined.1; rw [empty] at hh; cases hh
  refine ⟨joinTrace firstTrace secondTrace++[after],after,?_,by simp,appended.1,?_,secondHeader,secondBase,rfl,
    afterMemory.frame n k,secondOutput.trans firstOutput,appendTrace_memory (joinTrace firstTrace secondTrace) before after base allMemory afterMemory,?_⟩
  · simpa only [List.head?_append_of_ne_nil _ nonempty] using joined.1
  · have bound:=appended.2
    omega
  · intro state member
    rcases List.mem_append.mp member with old|new
    · exact allSafe state old
    · have same:=List.mem_singleton.mp new
      subst state
      exact afterSafe

end PDCompute.Solver
