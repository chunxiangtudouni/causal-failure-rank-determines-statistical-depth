module

public import Paid.PDROC_D27Prepare_Q_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Q

theorem first_setup_trace (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (raw : Search.RawConstants P fee before) (location : before.pc = pc 10)
    (hM : Search.SlotHas before 7 (.natural P.certificate.M))
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ (after : State) (trace : List State), after.pc = pc 11 ∧
      Search.SlotHas after 32 (.rational (firstValue P)) ∧
      after.output = before.output ∧ after.register .fresh = before.register .fresh ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length = 29 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      (∀ state ∈ trace, MemoryProgress region before state) ∧
      after.heap = Function.update before.heap 32 (.rational (firstValue P)) ∧
      after.live = insert 32 before.live := by
  let memory : SlotMemory := ⟨before.heap, before.live⟩
  have matched : MemoryMatch before memory := ⟨rfl, rfl, raw.fresh⟩
  have hm : Has memory 7 (.natural P.certificate.M) := ⟨hM.1, hM.2⟩
  have h1 : Has memory 17 (.rational 1) := ⟨raw.ratOne.1, raw.ratOne.2⟩
  have hg : Has memory 2 (.rational P.certificate.gamma) := ⟨raw.gamma.1, raw.gamma.2⟩
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory := ⟨bounded.live, bounded.heapValues⟩
  have addresses : ∀ command ∈ firstCeilSetupCommands, CommandAddresses 64 command := by
    intro command member
    simp only [firstCeilSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command ∈ firstCeilSetupCommands, Memory.target command ∈ region := by
    intro command member
    simp only [firstCeilSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  obtain ⟨after, trace, afterMatch, afterPc, afterOutput, afterFresh, head, last, length, chain, values, frames⟩ :=
    sequence_page_resources P fee input 10 11 (by decide) firstCeilSetupCommands rfl before location memory
      (firstNext memory P) matched (first_body_eval memory P hm h1 hg) bounded
      (first_body_memory_bounds memory P fee memoryBound hm h1 hg) addresses writes
  have stored : Has (firstNext memory P) 32 (.rational (firstValue P)) := Has.write_same _ _ _
  have actual : Search.SlotHas after 32 (.rational (firstValue P)) := match_has after _ 32 _ afterMatch stored
  refine ⟨after, trace, afterPc, actual, afterOutput, afterFresh, head, last, ?_, chain, values, frames, ?_, ?_⟩
  · have codeLength : (slotSequenceCode firstCeilSetupCommands).length = 27 := by decide
    simpa only [codeLength, Nat.reduceAdd] using length
  · simpa only [firstNext, SlotMemory.write, memory, Function.update_idem] using afterMatch.heap
  · simpa only [firstNext, SlotMemory.write, memory, Finset.insert_idem] using afterMatch.live

theorem second_setup_trace (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (raw : Search.RawConstants P fee before) (location : before.pc = pc 13)
    (hE : Search.SlotHas before 8 (.natural P.certificate.E))
    (hGammaSquared : Search.SlotHas before 24 (.rational (P.certificate.gamma ^ 2)))
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ (after : State) (trace : List State), after.pc = pc 14 ∧
      Search.SlotHas after 32 (.rational (secondValue P)) ∧
      after.output = before.output ∧ after.register .fresh = before.register .fresh ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length = 29 ∧
      trace.IsChain (fun a b => step Program.program input a = some b) ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      (∀ state ∈ trace, MemoryProgress region before state) ∧
      after.heap = Function.update before.heap 32 (.rational (secondValue P)) ∧
      after.live = insert 32 before.live := by
  let memory : SlotMemory := ⟨before.heap, before.live⟩
  have matched : MemoryMatch before memory := ⟨rfl, rfl, raw.fresh⟩
  have he : Has memory 8 (.natural P.certificate.E) := ⟨hE.1, hE.2⟩
  have h2 : Has memory 18 (.rational 2) := ⟨raw.ratTwo.1, raw.ratTwo.2⟩
  have hg : Has memory 24 (.rational (P.certificate.gamma ^ 2)) := ⟨hGammaSquared.1, hGammaSquared.2⟩
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory := ⟨bounded.live, bounded.heapValues⟩
  have addresses : ∀ command ∈ secondCeilSetupCommands, CommandAddresses 64 command := by
    intro command member
    simp only [secondCeilSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command ∈ secondCeilSetupCommands, Memory.target command ∈ region := by
    intro command member
    simp only [secondCeilSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  obtain ⟨after, trace, afterMatch, afterPc, afterOutput, afterFresh, head, last, length, chain, values, frames⟩ :=
    sequence_page_resources P fee input 13 14 (by decide) secondCeilSetupCommands rfl before location memory
      (secondNext memory P) matched (second_body_eval memory P he h2 hg) bounded
      (second_body_memory_bounds memory P fee memoryBound he h2 hg) addresses writes
  have stored : Has (secondNext memory P) 32 (.rational (secondValue P)) := Has.write_same _ _ _
  have actual : Search.SlotHas after 32 (.rational (secondValue P)) := match_has after _ 32 _ afterMatch stored
  refine ⟨after, trace, afterPc, actual, afterOutput, afterFresh, head, last, ?_, chain, values, frames, ?_, ?_⟩
  · have codeLength : (slotSequenceCode secondCeilSetupCommands).length = 27 := by decide
    simpa only [codeLength, Nat.reduceAdd] using length
  · simpa only [secondNext, SlotMemory.write, memory, Function.update_idem] using afterMatch.heap
  · simpa only [secondNext, SlotMemory.write, memory, Finset.insert_idem] using afterMatch.live

end PDROC.D27Prepare.Q
