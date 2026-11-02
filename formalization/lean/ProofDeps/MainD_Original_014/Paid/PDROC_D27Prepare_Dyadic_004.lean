module

public import Paid.PDROC_D27Prepare_Dyadic_003
public import Paid.PDROC_D27Prepare_Search_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Tail PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Dyadic

/-- Actual page21 computes Lambda and initializes the dyadic counter and
power from constants. These values are not input cells or loop premises. -/
theorem setup_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (initial : Search.SearchFinished P fee before) (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, MemoryMatch after (multiplierNext (Search.currentMemory before) P) ∧
      after.pc = pc 22 ∧ Segment region input before after 64 (operandBudget P fee) 54 := by
  let memory := Search.currentMemory before
  have matched : MemoryMatch before memory := Search.currentMemory_match before initial.raw.fresh
  have old (address : ℕ) (value : Cell) (stored : Search.SlotHas before address value) : Has memory address value :=
    has_of_match before memory address value matched stored
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory := ⟨bounded.live, bounded.heapValues⟩
  have evaluated := multiplier_body_eval memory P (old 20 _ initial.raw.ratFour) (old 4 _ initial.raw.reviewFee)
    (old 22 _ initial.ratStages) (old 23 _ initial.ratT0) (old 3 _ initial.raw.risk)
    (old 13 _ initial.raw.natZero) (old 17 _ initial.raw.ratOne)
  have semantic := multiplier_semantic_bounds P fee memory memoryBound
    (old 20 _ initial.raw.ratFour) (old 4 _ initial.raw.reviewFee) (old 22 _ initial.ratStages)
    (old 23 _ initial.ratT0) (old 3 _ initial.raw.risk) (old 13 _ initial.raw.natZero) (old 17 _ initial.raw.ratOne)
  have addresses : ∀ command ∈ multiplierSetupCommands, CommandAddresses 64 command := by
    intro command member
    simp only [multiplierSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command ∈ multiplierSetupCommands, Memory.target command ∈ region := by
    intro command member
    simp only [multiplierSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨after, afterMatch, afterPc, segment⟩ := J.sequence_page_segment region input (operandBudget P fee)
    21 22 (by decide) multiplierSetupCommands rfl before initial.location memory (multiplierNext memory P) matched
    evaluated bounded semantic (operandBudget_address_bits P fee) addresses writes
  exact ⟨after, afterMatch, afterPc, segment⟩

end PDROC.D27Prepare.Dyadic
