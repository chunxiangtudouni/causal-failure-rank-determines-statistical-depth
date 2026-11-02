module
public import Paid.PDCompute_Pack_DecrementBits_061
public import Paid.PDCompute_Pack_CounterBack_033

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDROC.DataBits PDCompute.Solver PDMenu.ComputeFrame

theorem counterBack_trace_safe (program : Program) (input : List Cell) (before : State) (base slot value target budget : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : slot<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (safe : SafeBits before budget) (addressBits : 1+natBits (base+slot) ≤ budget)
    (oneBits : 1+natBits 1 ≤ budget) (counter : natBits (before.pc+8) ≤ budget) (targetBits : natBits target ≤ budget)
    (fetched : FetchesCode program before.pc (counterBackCode slot target)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤150 ∧
      Header after base (Function.update values slot (.natural (value-1))) ∧
      after.register .fresh=.natural base ∧ after.pc=target ∧ after.output=before.output ∧
      (∀ state∈trace,HeaderMemory before state base) ∧ (∀ state∈trace,SafeBits state budget) := by
  unfold counterBackCode at fetched
  obtain ⟨decrementTrace,hh,hl,hchain,ht,prefixMemory,prefixBits⟩:=
    decrement_trace_safe program input before base slot value budget values header inside hbase hvalue safe addressBits oneBits counter fetched.append_left
  have decreasedHeader:=decrement_header before base slot value values header
  have decreasedFields:=decrement_fields before base slot value
  have decreasedBase : (decrementResult before base slot value).register .fresh=.natural base:=decreasedFields.2.2.1.trans hbase
  have decreasedPC : (decrementResult before base slot value).pc=before.pc+8:=decreasedFields.2.2.2.1
  have decreasedOutput : (decrementResult before base slot value).output=before.output:=decreasedFields.2.2.2.2
  let decreased:=decrementResult before base slot value
  have jumpFetch : program[decreased.pc]?=some (.jump target) := by
    rw [decreasedPC]
    exact (fetched 8 (by rw [List.length_append,decrementSlot_length];simp)).trans
      ((List.getElem?_append_right (l₁:=decrementSlot slot) (l₂:=[.jump target]) (i:=8)
        (by rw [decrementSlot_length])).trans (by rfl))
  let after:State:={decreased with pc:=target}
  have jump : step program input decreased=some after := by simp [step,jumpFetch,Instruction.execute,after]
  have joined:=chain_append_control program input decrementTrace decreased after hchain hl jump
  have nonempty : decrementTrace≠[] := by intro empty;simp only [empty,List.head?_nil,reduceCtorEq] at hh
  have lastMemory:=HeaderMemory.trace_last prefixMemory hl
  have afterMemory : HeaderMemory before after base := lastMemory
  have decreasedSafe : SafeBits decreased budget:=prefixBits decreased (List.mem_of_getLast? hl)
  have afterSafe : SafeBits after budget:=decreasedSafe.withPC target targetBits
  refine ⟨decrementTrace++[after],after,?_,by simp,joined.1,?_,decreasedHeader,decreasedBase,rfl,decreasedOutput,?_,?_⟩
  · simpa only [List.head?_append_of_ne_nil decrementTrace nonempty] using hh
  · omega
  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact prefixMemory state earlier
    · have same : state=after := by simpa only [List.mem_singleton] using last
      subst state
      exact afterMemory

  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact prefixBits state earlier
    · have same : state=after:=by simpa only [List.mem_singleton] using last
      subst state
      exact afterSafe

end PDCompute.Pack
