module

public import Paid.PDROC_D27Prepare_EndpointRun_005
public import Paid.PDROC_D27Prepare_Search_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.EndpointRun

theorem guard_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State) (memory : SlotMemory)
    (matched : MemoryMatch before memory) (location : before.pc = pc 5)
    (bounded : StateBounds 64 (operandBudget P fee) before) (m : ℕ) (range : m ≤ P.certificate.M)
    (data : EndpointData P memory m) :
    ∃ after : State, MemoryMatch after (guardMemory P memory m) ∧
      after.pc = (if m = P.certificate.M then pc 7 else pc 6) ∧
      Segment loopRegion input before after 64 (operandBudget P fee) 29 := by
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory := by
    constructor
    · simpa only [matched.live] using bounded.live
    · simpa only [matched.live, matched.heap] using bounded.heapValues
  have evaluated := Search.endpointTest_eval P.certificate m memory data.ratOne data.power data.ratio
  obtain ⟨computed, bodyRun, computedMatch, _, _⟩ := slotSequence_realize Search.endpointTestCommands input before memory
    (guardMemory P memory m) matched evaluated
  have addresses : ∀ command ∈ Search.endpointTestCommands, CommandAddresses 64 command := by
    intro command member
    simp only [Search.endpointTestCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command ∈ Search.endpointTestCommands, Memory.target command ∈ loopRegion := by
    intro command member
    simp only [Search.endpointTestCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  have arithmeticBounds := slotSequence_prefix_bounds Search.endpointTestCommands input before memory
    (guardMemory P memory m) 64 (operandBudget P fee) matched bounded addresses (operandBudget_address_bits P fee)
    evaluated (guard_semantic_bounds P fee memory m range data memoryBound)
  have arithmeticBound := arithmeticBounds.final bodyRun
  have computedData := guard_data P memory m data
  have one := match_has computed _ 17 _ computedMatch computedData.ratOne
  have product := match_has computed _ 32 _ computedMatch (Has.write_same _ _ _)
  have enough : 2 ≤ operandBudget P fee := by
    have h := linear_le_operandBudget P fee
    omega
  have compareBounds := ratCompareSlots_prefix_bounds input computed 17 32 64 (operandBudget P fee) .lessEqual
    1 (P.certificate.menuRatio * (1 + P.certificate.odds ^ m)) arithmeticBound computedMatch.base
    one.1 product.1 one.2 product.2 (by decide) (by decide) (operandBudget_address_bits P fee) enough
  have fullBounds := LinearPrefixBounds.append input (slotSequenceCode Search.endpointTestCommands)
    (ratCompareSlots .lessEqual 17 32) before computed 64 (operandBudget P fee) bodyRun arithmeticBounds compareBounds
  rw [← Search.endpointGuard_compiled] at fullBounds
  have arithmeticFrames := sequence_prefix_memory loopRegion Search.endpointTestCommands input before memory
    (guardMemory P memory m) matched evaluated writes
  have compareFrames : LinearPrefixMemory loopRegion input (ratCompareSlots .lessEqual 17 32) computed := by
    intro count state actual
    apply linearExecute_no_memory_write loopRegion input _ computed state _ actual
    intro instruction member
    have inFull := List.mem_of_mem_take member
    simp only [ratCompareSlots, PDLower.CalibrationCompute.loadSlot, List.mem_append,
      List.mem_cons, List.not_mem_nil, or_false] at inFull
    rcases inFull with ((rfl | rfl | rfl) | (rfl | rfl | rfl)) | rfl <;> trivial
  have fullFrames := LinearPrefixMemory.append loopRegion input (slotSequenceCode Search.endpointTestCommands)
    (ratCompareSlots .lessEqual 17 32) before computed bodyRun arithmeticFrames compareFrames
  rw [← Search.endpointGuard_compiled] at fullFrames
  obtain ⟨after, trace, head, last, length, chain, afterPc, heap, live, fresh, output,
    members, terminal, executed, afterShape⟩ := Search.endpoint_guard_page_trace input P.certificate m range before
      location matched.base (match_has before memory 17 _ matched data.ratOne)
      (match_has before memory 28 _ matched data.power) (match_has before memory 29 _ matched data.ratio)
  have afterMatch : MemoryMatch after (guardMemory P memory m) := by
    constructor
    · simpa only [guardMemory, SlotMemory.write, Function.update_idem, matched.heap] using heap
    · simpa only [guardMemory, SlotMemory.write, Finset.insert_idem, matched.live] using live
    · exact fresh.trans matched.base
  refine ⟨after, afterMatch, afterPc, ⟨⟨trace, head, last, chain, length.le, ?_, ?_⟩, output, fresh⟩⟩
  · intro state member
    rcases members state member with same | ⟨count, _, actual⟩
    · subst state
      rw [afterShape]
      exact (fullBounds.final executed).with_pc _
    · exact fullBounds count state actual
  · intro state member
    rcases members state member with same | ⟨count, _, actual⟩
    · subst state
      rw [afterShape]
      exact (fullFrames.final executed).with_pc _
    · exact fullFrames count state actual

end PDROC.D27Prepare.EndpointRun
