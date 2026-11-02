module

public import Paid.PDROC_D27Prepare_EndpointRun_003
public import Paid.PDROC_D27Prepare_Search_019
public import Paid.PDROC_D27Prepare_J_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.EndpointRun

def loopRegion : Finset ℕ := {7, 28, 32}

theorem setup_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (initial : Search.EndpointInitial P fee before)
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, MemoryMatch after (setupMemory P.certificate (Search.currentMemory before)) ∧
      after.pc = pc 5 ∧ EndpointData P (setupMemory P.certificate (Search.currentMemory before)) 0 ∧
      Segment region input before after 64 (operandBudget P fee) 85 := by
  let memory := Search.currentMemory before
  have matched : MemoryMatch before memory := Search.currentMemory_match before initial.raw.fresh
  have old (address : ℕ) (value : Cell) (stored : Search.SlotHas before address value) : Has memory address value :=
    has_of_match before memory address value matched stored
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory :=
    ⟨bounded.live, bounded.heapValues⟩
  have evaluated := setup_eval P.certificate memory (old 6 _ initial.t0) (old 22 _ initial.ratStages)
    (old 2 _ initial.raw.gamma) (old 3 _ initial.raw.risk) (old 17 _ initial.raw.ratOne)
    (old 18 _ initial.raw.ratTwo) (old 20 _ initial.raw.ratFour)
  have semantic := setup_semantic_bounds P fee memory memoryBound (old 6 _ initial.t0) (old 22 _ initial.ratStages)
    (old 2 _ initial.raw.gamma) (old 3 _ initial.raw.risk) (old 17 _ initial.raw.ratOne)
    (old 18 _ initial.raw.ratTwo) (old 20 _ initial.raw.ratFour)
  have addresses : ∀ command ∈ endpointSetupCommands, CommandAddresses 64 command := by
    intro command member
    simp only [endpointSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command ∈ endpointSetupCommands, Memory.target command ∈ region := by
    intro command member
    simp only [endpointSetupCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
  obtain ⟨after, afterMatch, afterPc, segment⟩ := J.sequence_page_segment region input (operandBudget P fee)
    4 5 (by decide) endpointSetupCommands rfl before initial.location memory (setupMemory P.certificate memory)
    matched evaluated bounded semantic (operandBudget_address_bits P fee) addresses writes
  have data : EndpointData P (setupMemory P.certificate memory) 0 := by
    constructor
    · simpa [setupMemory, Has, SlotMemory.write] using old 7 _ initial.M
    · simpa [setupMemory, Has, SlotMemory.write] using old 14 _ initial.raw.natOne
    · simpa [setupMemory, Has, SlotMemory.write] using old 17 _ initial.raw.ratOne
    · simp [setupMemory, Has, SlotMemory.write]
    · simp [setupMemory, Has, SlotMemory.write]
    · simp [setupMemory, Has, SlotMemory.write]
  exact ⟨after, afterMatch, afterPc, data, segment⟩

end PDROC.D27Prepare.EndpointRun
