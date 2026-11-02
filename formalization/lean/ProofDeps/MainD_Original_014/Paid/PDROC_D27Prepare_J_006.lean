module

public import Paid.PDROC_D27Prepare_J_002
public import Paid.PDROC_D27Prepare_J_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Tail PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.J

theorem ratio_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State) (memory : SlotMemory)
    (matched : MemoryMatch before memory) (location : before.pc = pc 39)
    (bounded : StateBounds 64 (operandBudget P fee) before)
    (htwo : Has memory 18 (.rational 2)) (hL : Has memory 11 (.rational P.Lambda))
    (hr : Has memory 3 (.rational P.certificate.risk))
    (hf : Has memory 44 (.rational (P.positiveValueFloor fee))) (positive : 0 < P.positiveValueFloor fee) :
    ∃ after : State, MemoryMatch after (ratioNext memory P fee) ∧ after.pc = pc 40 ∧
      Segment region input before after 64 (operandBudget P fee) 32 := by
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory := by
    constructor
    · simpa only [matched.live] using bounded.live
    · simpa only [matched.live, matched.heap] using bounded.heapValues
  have addresses : ∀ command ∈ budgetRatioSetupCommands, CommandAddresses 64 command := by
    intro command member
    simp only [budgetRatioSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command ∈ budgetRatioSetupCommands, Memory.target command ∈ region := by
    intro command member
    simp only [budgetRatioSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl <;> decide
  obtain ⟨after, afterMatch, afterPc, segment⟩ := sequence_page_segment region input (operandBudget P fee)
    39 40 (by decide) budgetRatioSetupCommands rfl before location memory (ratioNext memory P fee) matched
    (ratio_body_eval memory P fee htwo hL hr hf positive) bounded
    (ratio_semantic_bounds P fee memory memoryBound htwo hL hr hf positive)
    (operandBudget_address_bits P fee) addresses writes
  exact ⟨after, afterMatch, afterPc, segment⟩

theorem halve_setup_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State) (memory : SlotMemory)
    (matched : MemoryMatch before memory) (location : before.pc = pc 42)
    (bounded : StateBounds 64 (operandBudget P fee) before)
    (hc : Has memory 46 (.natural (Nat.ceil (Budget.originalRatio P fee))))
    (hone : Has memory 14 (.natural 1)) (hzero : Has memory 13 (.natural 0)) :
    ∃ after : State, MemoryMatch after (halveInitial memory (Nat.ceil (Budget.originalRatio P fee))) ∧
      after.pc = pc 43 ∧ Segment region input before after 64 (operandBudget P fee) 18 := by
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory := by
    constructor
    · simpa only [matched.live] using bounded.live
    · simpa only [matched.live, matched.heap] using bounded.heapValues
  have addresses : ∀ command ∈ budgetHalveSetupCommands, CommandAddresses 64 command := by
    intro command member
    simp only [budgetHalveSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command ∈ budgetHalveSetupCommands, Memory.target command ∈ region := by
    intro command member
    simp only [budgetHalveSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  obtain ⟨after, afterMatch, afterPc, segment⟩ := sequence_page_segment region input (operandBudget P fee)
    42 43 (by decide) budgetHalveSetupCommands rfl before location memory
    (halveInitial memory (Nat.ceil (Budget.originalRatio P fee))) matched
    (halve_setup_eval memory (Nat.ceil (Budget.originalRatio P fee)) hc hone hzero) bounded
    (halve_setup_semantic_bounds P fee memory memoryBound hc hone hzero)
    (operandBudget_address_bits P fee) addresses writes
  exact ⟨after, afterMatch, afterPc, segment⟩

end PDROC.D27Prepare.J
