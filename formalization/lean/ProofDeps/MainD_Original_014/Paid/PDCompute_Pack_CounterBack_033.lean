module
public import Paid.PDCompute_Pack_CounterTrace_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 500000
@[expose] public section
namespace PDCompute.Pack
open PaperProofs.Paid.Computation PDCompute.Solver PDMenu.ComputeFrame

def counterBackCode (slot target : ℕ) : List Instruction := decrementSlot slot++[.jump target]

theorem counterBackCode_length (slot target : ℕ) : (counterBackCode slot target).length=9 := rfl

/-- The loop back-edge really executes its decrement and jump. This
generic literal fragment is instantiated at the actual row/column PCs. -/
theorem counterBack_trace (program : Program) (input : List Cell) (before : State) (base slot value target : ℕ)
    (values : ℕ → Cell) (header : Header before base values) (inside : slot<headerWords)
    (hbase : before.register .fresh=.natural base) (hvalue : values slot=.natural value)
    (fetched : FetchesCode program before.pc (counterBackCode slot target)) :
    ∃ trace : List State,∃ after : State,
      trace.head?=some before ∧ trace.getLast?=some after ∧
      trace.IsChain (fun first later=>step program input first=some later) ∧ time program trace≤150 ∧
      Header after base (Function.update values slot (.natural (value-1))) ∧
      after.register .fresh=.natural base ∧ after.pc=target ∧ after.output=before.output ∧
      ∀ state∈trace,HeaderMemory before state base := by
  unfold counterBackCode at fetched
  obtain ⟨decrementTrace,hh,hl,hchain,ht,decreasedHeader,decreasedBase,decreasedPC,decreasedOutput,prefixMemory⟩:=
    decrement_trace program input before base slot value values header inside hbase hvalue fetched.append_left
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
  refine ⟨decrementTrace++[after],after,?_,by simp,joined.1,?_,decreasedHeader,decreasedBase,rfl,decreasedOutput,?_⟩
  · simpa only [List.head?_append_of_ne_nil decrementTrace nonempty] using hh
  · omega
  · intro state member
    rcases List.mem_append.mp member with earlier|last
    · exact prefixMemory state earlier
    · have same : state=after := by simpa only [List.mem_singleton] using last
      subst state
      exact afterMemory

end PDCompute.Pack
