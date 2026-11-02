module

public import Paid.PDROC_D27Prepare_EndpointRun_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.EndpointRun

theorem step_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State) (memory : SlotMemory)
    (matched : MemoryMatch before memory) (location : before.pc = pc 6)
    (bounded : StateBounds 64 (operandBudget P fee) before) (m : ℕ) (range : m < P.certificate.M)
    (data : EndpointData P memory m) :
    ∃ after : State, MemoryMatch after (stepMemory P memory m) ∧ after.pc = pc 5 ∧
      Segment loopRegion input before after 64 (operandBudget P fee) 22 := by
  have memoryBound : MemoryBounds 64 (operandBudget P fee) memory := by
    constructor
    · simpa only [matched.live] using bounded.live
    · simpa only [matched.live, matched.heap] using bounded.heapValues
  have addresses : ∀ command ∈ endpointStepCommands, CommandAddresses 64 command := by
    intro command member
    simp only [endpointStepCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> norm_num [CommandAddresses]
  have writes : ∀ command ∈ endpointStepCommands, Memory.target command ∈ loopRegion := by
    intro command member
    simp only [endpointStepCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> decide
  obtain ⟨after, afterMatch, afterPc, segment⟩ := J.sequence_page_segment loopRegion input (operandBudget P fee)
    6 5 (by decide) endpointStepCommands rfl before location memory (stepMemory P memory m) matched
    (Search.endpointStep_eval P.certificate m memory data.counter data.one data.power data.odds) bounded
    (step_semantic_bounds P fee memory m range data memoryBound) (operandBudget_address_bits P fee) addresses writes
  exact ⟨after, afterMatch, afterPc, segment⟩

def cycleMemory (P : Parameters) (memory : SlotMemory) (m : ℕ) : SlotMemory :=
  stepMemory P (guardMemory P memory m) m

theorem cycle_data (P : Parameters) (memory : SlotMemory) (m : ℕ) (data : EndpointData P memory m) :
    EndpointData P (cycleMemory P memory m) (m + 1) :=
  step_data P (guardMemory P memory m) m (guard_data P memory m data)

/-- The real rational guard, two updates and jump of one rejected M
candidate. The budget is a safe count of the actual joined state trace. -/
theorem cycle_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State) (memory : SlotMemory)
    (matched : MemoryMatch before memory) (location : before.pc = pc 5)
    (bounded : StateBounds 64 (operandBudget P fee) before) (m : ℕ) (range : m < P.certificate.M)
    (data : EndpointData P memory m) :
    ∃ after : State, MemoryMatch after (cycleMemory P memory m) ∧ after.pc = pc 5 ∧
      Segment loopRegion input before after 64 (operandBudget P fee) 51 := by
  obtain ⟨guarded, guardMatch, guardPc, first⟩ := guard_segment P fee input before memory matched location bounded m range.le data
  have at6 : guarded.pc = pc 6 := by simpa only [ite_eq_right (Nat.ne_of_lt range)] using guardPc
  obtain ⟨after, afterMatch, afterPc, later⟩ := step_segment P fee input guarded (guardMemory P memory m)
    guardMatch at6 first.final_bounds m range (guard_data P memory m data)
  exact ⟨after, afterMatch, afterPc, first.trans later⟩

end PDROC.D27Prepare.EndpointRun
