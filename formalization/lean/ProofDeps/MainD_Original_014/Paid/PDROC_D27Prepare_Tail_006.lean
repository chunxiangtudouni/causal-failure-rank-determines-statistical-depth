module

public import Paid.PDROC_D27Prepare_Tail_005
public import Paid.PDROC_D27Prepare_J_001
public import Paid.PDROC_D27Prepare_Resources_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Tail

theorem binomial_setup_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (matched : MemoryMatch before memory)
    (location : before.pc=pc 26) (bounded : StateBounds 64 (operandBudget P fee) before)
    (hzero : Has memory 13 (.natural 0)) (hone : Has memory 17 (.rational 1))
    (hrzero : Has memory 16 (.rational 0)) :
    ∃ after : State,MemoryMatch after (binomialInitial memory) ∧ after.pc=pc 27 ∧
      Segment binomialRegion input before after 64 (operandBudget P fee) 20 := by
  have addresses : ∀ command∈binomialSetupCommands,CommandAddresses 64 command := by
    intro command member
    simp only [binomialSetupCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command∈binomialSetupCommands,Memory.target command∈binomialRegion := by
    intro command member
    simp only [binomialSetupCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl <;> simp [Memory.target,binomialRegion]
  simpa only [show (slotSequenceCode binomialSetupCommands).length=18 from rfl] using
    J.sequence_page_segment binomialRegion input (operandBudget P fee) 26 27 (by decide)
      binomialSetupCommands rfl before location memory (binomialInitial memory) matched
      (binomial_setup_eval memory hzero hone hrzero) bounded
      (binomial_setup_memory_bounds memory _ (MemoryMatch.memoryBounds before memory 64 _ matched bounded)
        hzero hone hrzero) (operandBudget_address_bits P fee) addresses writes

theorem binomial_update_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (i : ℕ) (matched : MemoryMatch before memory)
    (location : before.pc=pc 30) (bounded : StateBounds 64 (operandBudget P fee) before)
    (index : i≤P.certificate.stages)
    (hN : Has memory 0 (.natural P.certificate.stages)) (hi : Has memory 40 (.natural i))
    (hone : Has memory 14 (.natural 1))
    (hchoose : Has memory 41 (.rational (P.certificate.stages.choose i))) :
    ∃ after : State,MemoryMatch after (binomialNext memory P.certificate.stages i) ∧ after.pc=pc 27 ∧
      Segment binomialRegion input before after 64 (operandBudget P fee) 62 := by
  have addresses : ∀ command∈binomialStepCommands,CommandAddresses 64 command := by
    intro command member
    simp only [binomialStepCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command∈binomialStepCommands,Memory.target command∈binomialRegion := by
    intro command member
    simp only [binomialStepCommands,List.mem_cons,List.not_mem_nil,or_false] at member
    rcases member with rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> simp [Memory.target,binomialRegion]
  simpa only [show (slotSequenceCode binomialStepCommands).length=60 from rfl] using
    J.sequence_page_segment binomialRegion input (operandBudget P fee) 30 27 (by decide)
      binomialStepCommands rfl before location memory (binomialNext memory P.certificate.stages i) matched
      (binomial_body_eval memory P.certificate.stages i hN hi hone hchoose) bounded
      (binomial_body_memory_bounds P fee memory i index
        (MemoryMatch.memoryBounds before memory 64 _ matched bounded) hN hi hone hchoose)
      (operandBudget_address_bits P fee) addresses writes

theorem binomial_add_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (i : ℕ) (matched : MemoryMatch before memory)
    (location : before.pc=pc 29) (bounded : StateBounds 64 (operandBudget P fee) before)
    (index : i≤P.certificate.stages)
    (htail : Has memory 42 (.rational (Binomial.partialTail P.certificate.stages P.tools i)))
    (hchoose : Has memory 41 (.rational (P.certificate.stages.choose i))) :
    ∃ after : State,MemoryMatch after (memory.write 42 (.rational
        ((Binomial.partialTail P.certificate.stages P.tools i : ℚ)+P.certificate.stages.choose i))) ∧
      after.pc=pc 30 ∧ Segment binomialRegion input before after 64 (operandBudget P fee) 12 := by
  have addresses : ∀ command∈tailAddCommands,CommandAddresses 64 command := by
    intro command member
    have equal := List.mem_singleton.mp member
    subst command
    norm_num [CommandAddresses]
  have writes : ∀ command∈tailAddCommands,Memory.target command∈binomialRegion := by
    intro command member
    have equal := List.mem_singleton.mp member
    subst command
    simp [Memory.target,binomialRegion]
  simpa only [show (slotSequenceCode tailAddCommands).length=10 from rfl] using
    J.sequence_page_segment binomialRegion input (operandBudget P fee) 29 30 (by decide)
      tailAddCommands rfl before location memory _ matched
      (tail_add_eval memory P.certificate.stages P.tools i htail hchoose) bounded
      (tail_add_memory_bounds P fee memory P.tools i index
        (MemoryMatch.memoryBounds before memory 64 _ matched bounded) htail hchoose)
      (operandBudget_address_bits P fee) addresses writes

end PDROC.D27Prepare.Tail
