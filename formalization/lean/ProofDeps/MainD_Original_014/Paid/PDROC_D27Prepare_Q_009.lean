module

public import Paid.PDROC_D27Prepare_Q_008
public import Paid.PDROC_D27Prepare_Q_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Q

theorem nat_compare_segment (R : Finset ℕ) (input : List Cell) (page : ℕ)
    (inside : page < pageCount) (before : State) (location : before.pc = pc page)
    (comparison : Comparison) (left right whenZero whenNonzero x y : ℕ)
    (layout : pageCode page = natCompareSlots comparison left right ++ branch whenZero whenNonzero)
    (fresh : before.register .fresh = .natural 0)
    (leftValue : Search.SlotHas before left (.natural x))
    (rightValue : Search.SlotHas before right (.natural y)) (B : ℕ)
    (bounded : StateBounds 64 B before) (addressBits : 1 + natBits 64 ≤ B)
    (leftInside : left < 64) (rightInside : right < 64) (enough : 2 ≤ B) :
    ∃ after : State,
      after.pc = (if comparison.nat x y then pc whenNonzero else pc whenZero) ∧
      after.heap = before.heap ∧ after.live = before.live ∧
      Segment R input before after 64 B 9 := by
  let terminal := comparisonResult before 0 left right (comparison.nat x y)
  let destination := if comparison.nat x y then pc whenNonzero else pc whenZero
  let after : State := {terminal with pc := destination}
  obtain ⟨trace, head, last, length, chain, heap, live, afterFresh, output, prefixes⟩ :=
    Search.nat_compare_page_trace input page inside before location comparison left right
      whenZero whenNonzero x y layout fresh leftValue rightValue
  have executed : linearExecute input (natCompareSlots comparison left right) before = some terminal :=
    natCompareSlots_execute input before 0 left right x y comparison fresh
      (by simpa only [Nat.zero_add] using leftValue.1)
      (by simpa only [Nat.zero_add] using rightValue.1)
      (by simpa only [Nat.zero_add] using leftValue.2)
      (by simpa only [Nat.zero_add] using rightValue.2)
  have bits := natCompareSlots_prefix_bounds input before left right 64 B comparison x y bounded fresh
    leftValue.1 rightValue.1 leftValue.2 rightValue.2 leftInside rightInside addressBits enough
  have clean : ∀ instruction ∈ natCompareSlots comparison left right, NoMemoryWrite instruction := by
    intro instruction member
    simp only [natCompareSlots, PDLower.CalibrationCompute.loadSlot, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;> trivial
  have frames : LinearPrefixMemory R input (natCompareSlots comparison left right) before := by
    intro count state actual
    exact linearExecute_no_memory_write R input _ before state
      (fun instruction member => clean instruction (List.mem_of_mem_take member)) actual
  refine ⟨after, rfl, heap, live, ⟨⟨trace, head, last, chain, length.le, ?_, ?_⟩, output, afterFresh⟩⟩
  · intro state member
    rcases prefixes state member with same | ⟨count, _, actual⟩
    · simpa only [same] using (bits.final executed).with_pc destination
    · exact bits count state actual
  · intro state member
    rcases prefixes state member with same | ⟨count, _, actual⟩
    · simpa only [same] using (frames.final executed).with_pc destination
    · exact frames count state actual

theorem copy_segment (P : Parameters) (fee : ℚ) (input : List Cell) (page target source destination : ℕ)
    (inside : page < pageCount)
    (layout : pageCode page = slotSequenceCode [.copy source destination] ++ go target)
    (destinationInside : destination ∈ region) (sourceSmall : source < 64) (destinationSmall : destination < 64)
    (before : State) (location : before.pc = pc page) (fresh : before.register .fresh = .natural 0)
    (value : Cell) (stored : Search.SlotHas before source value)
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, after.pc = pc target ∧ Search.SlotHas after destination value ∧
      Segment region input before after 64 (operandBudget P fee) 8 := by
  let memory : SlotMemory := ⟨before.heap, before.live⟩
  let next := memory.write destination value
  have matched : MemoryMatch before memory := ⟨rfl, rfl, fresh⟩
  have evaluated : slotSequenceEval [.copy source destination] memory = some next := by
    simp only [slotSequenceEval, copy_eval memory source destination value stored, Option.bind_some, next]
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory := ⟨bounded.live, bounded.heapValues⟩
  have valueBits : value.bits ≤ operandBudget P fee := by
    simpa only [stored.2] using bounded.heapValues source stored.1
  have nextBound := memoryBound.write destination value destinationSmall valueBits
  have semantic : SequenceMemoryBounds [.copy source destination] memory 64 (operandBudget P fee) :=
    SequenceMemoryBounds.cons _ [] memory next 64 _ memoryBound
      (copy_eval memory source destination value stored) (SequenceMemoryBounds.nil next 64 _ nextBound)
  have addresses : ∀ command ∈ [.copy source destination], CommandAddresses 64 command := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    exact ⟨sourceSmall, destinationSmall⟩
  have writes : ∀ command ∈ [.copy source destination], Memory.target command ∈ region := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    exact destinationInside
  obtain ⟨after, trace, afterMatch, afterPc, output, afterFresh, head, last, length, chain, bounds, frames⟩ :=
    sequence_page_resources P fee input page target inside [.copy source destination] layout before location
      memory next matched evaluated bounded semantic addresses writes
  have actual := match_has after next destination value afterMatch (Has.write_same memory destination value)
  have lengthEq : trace.length = 8 := by simpa only [show (slotSequenceCode [.copy source destination]).length = 6 from rfl] using length
  exact ⟨after, afterPc, actual, ⟨⟨trace, head, last, chain, lengthEq.le, bounds, frames⟩, output, afterFresh⟩⟩

end PDROC.D27Prepare.Q
