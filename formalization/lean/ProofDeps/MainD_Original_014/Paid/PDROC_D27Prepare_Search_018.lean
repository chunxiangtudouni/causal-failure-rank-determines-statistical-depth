module

public import Paid.PDROC_D27Prepare_Search_017
public import Paid.PDROC_D27Prepare_Search_008
public import Paid.PDROC_D27Prepare_J_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Search

/-- The actual first search setup computes powers/threshold from the
raw scalars, instead of requiring them in the initial heap. -/
theorem majority_setup_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (matched : MemoryMatch before memory)
    (ready : SearchInitial P fee before)
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, MemoryMatch after (majoritySetupMemory P.certificate memory) ∧
      MajorityReady P.certificate 0 after ∧
      Segment searchRegion input before after 64 (operandBudget P fee) 85 := by
  have old (address : ℕ) (value : Cell) (stored : SlotHas before address value) : Has memory address value :=
    has_of_match before memory address value matched stored
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory := by
    constructor
    · simpa only [matched.live] using bounded.live
    · simpa only [matched.live, matched.heap] using bounded.heapValues
  have evaluated := majoritySetup_eval P.certificate memory
    (old 0 _ ready.raw.stages) (old 2 _ ready.raw.gamma) (old 3 _ ready.raw.risk)
    (old 17 _ ready.raw.ratOne) (old 18 _ ready.raw.ratTwo) (old 20 _ ready.raw.ratFour)
  have semantic := majority_setup_semantic_bounds P fee memory memoryBound
    (old 0 _ ready.raw.stages) (old 2 _ ready.raw.gamma) (old 3 _ ready.raw.risk)
    (old 17 _ ready.raw.ratOne) (old 18 _ ready.raw.ratTwo) (old 20 _ ready.raw.ratFour)
  have addresses : ∀ command ∈ majoritySetupCommands, CommandAddresses 64 command := by
    intro command member
    simp only [majoritySetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command ∈ majoritySetupCommands, Memory.target command ∈ searchRegion := by
    intro command member
    simp only [majoritySetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨after, afterMatch, afterPc, segment⟩ := J.sequence_page_segment searchRegion input (operandBudget P fee)
    1 2 (by decide) majoritySetupCommands rfl before ready.location memory
    (majoritySetupMemory P.certificate memory) matched evaluated bounded semantic
    (operandBudget_address_bits P fee) addresses writes
  have counter : Has (majoritySetupMemory P.certificate memory) 6 (.natural 1) := by
    simpa [majoritySetupMemory, Has, SlotMemory.write] using old 6 _ ready.t0
  have two : Has (majoritySetupMemory P.certificate memory) 15 (.natural 2) := by
    simpa [majoritySetupMemory, Has, SlotMemory.write] using old 15 _ ready.raw.natTwo
  have square : Has (majoritySetupMemory P.certificate memory) 26 (.rational (P.certificate.varianceBase ^ 2)) := by
    simp [majoritySetupMemory, Has, SlotMemory.write]
  have threshold : Has (majoritySetupMemory P.certificate memory) 27
      (.rational ((P.certificate.risk / (2 * (P.certificate.stages : ℚ))) ^ 2)) := by
    simp [majoritySetupMemory, Has, SlotMemory.write]
  have power : Has (majoritySetupMemory P.certificate memory) 28 (.rational P.certificate.varianceBase) := Has.write_same _ _ _
  have actualReady : MajorityReady P.certificate 0 after := by
    refine ⟨afterMatch.base, afterPc, ?_, match_has after _ 15 _ afterMatch two,
      match_has after _ 26 _ afterMatch square, match_has after _ 27 _ afterMatch threshold, ?_⟩
    · simpa only [SlotHas, Nat.mul_zero, Nat.zero_add] using match_has after _ 6 _ afterMatch counter
    · simpa only [SlotHas, Nat.mul_zero, Nat.zero_add, pow_one] using match_has after _ 28 _ afterMatch power
  exact ⟨after, afterMatch, actualReady, segment⟩

end PDROC.D27Prepare.Search
