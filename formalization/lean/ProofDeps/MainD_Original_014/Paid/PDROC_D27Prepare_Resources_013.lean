module

public import Paid.PDROC_D27Prepare_Resources_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

open PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program

namespace PDROC.D27Prepare.Resources

/-- Generic finite constant initialization; no dependency on the later
prologue boundary module or on a desired final whole-machine output. -/
theorem constant_sequence_memory_bounds (commands : List SlotCommand) (memory : SlotMemory)
    (H B : ℕ) (bounded : MemoryBounds H B memory)
    (constants : ∀ command ∈ commands, ∃ target value,
      command = SlotCommand.constant target value ∧ target < H ∧ value.bits ≤ B) :
    SequenceMemoryBounds commands memory H B := by
  induction commands generalizing memory with
  | nil => exact SequenceMemoryBounds.nil memory H B bounded
  | cons command rest ih =>
      obtain ⟨target, value, same, inside, bits⟩ := constants command (by simp)
      subst command
      have nextBound : MemoryBounds H B (memory.write target value) := bounded.write target value inside bits
      apply SequenceMemoryBounds.cons (.constant target value) rest memory (memory.write target value) H B
        bounded rfl
      apply ih (memory.write target value) nextBound
      intro other member
      exact constants other (by simp only [List.mem_cons]; exact Or.inr member)

theorem constant_sequence_addresses (commands : List SlotCommand) (H B : ℕ)
    (constants : ∀ command ∈ commands, ∃ target value,
      command = SlotCommand.constant target value ∧ target < H ∧ value.bits ≤ B) :
    ∀ command ∈ commands, CommandAddresses H command := by
  intro command member
  obtain ⟨target, value, same, inside, _⟩ := constants command member
  subst command
  exact inside

end PDROC.D27Prepare.Resources
