module

public import Paid.PDROC_CalibrationRow_ScatterOperands_001
public import Paid.PDROC_CalibrationRow_OperandPrefix_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame RootD27.Bits

/-- A genuine caller cap can be larger than the phase's newly assigned
values. It is preserved once by max, rather than charged once per cell. -/
theorem Sources.safe_max {before after : State} {New : Cell → Prop} {callerBudget newBudget : ℕ}
    (sources : Sources before after New) (caller : SafeBits before callerBudget)
    (assigned : ∀ value, New value → value.bits ≤ newBudget)
    (pc : natBits after.pc ≤ max callerBudget newBudget) :
    SafeBits after (max callerBudget newBudget) := by
  apply sources.safe
  · intro bits member
    exact (caller bits member).trans (Nat.le_max_left _ _)
  · intro value member
    exact (assigned value member).trans (Nat.le_max_right _ _)
  · exact pc

/-- Convert exact SSA into the parent's frozen same-budget PrefixSafe.
Composition and complete stateCellBits are reused from the parent APIs;
the straight-code PC fact is the existing ComputeFrame theorem. -/
theorem prefixSafe_of_sources (input : List Cell) (code : List Instruction) (before : State)
    (New : Cell → Prop) (budget : ℕ) (straight : StraightCode code)
    (sources : ∀ count ≤ code.length, ∀ after,
      linearExecute input (code.take count) before = some after → Sources before after New)
    (caller : SafeBits before budget) (assigned : ∀ value, New value → value.bits ≤ budget)
    (pc : natBits (before.pc + code.length) ≤ budget) :
    Operand.PrefixSafe input code before budget := by
  apply Operand.PrefixSafe.of_bounded input code before budget
  intro count bound after executed
  have takeStraight : StraightCode (code.take count) := by
    intro instruction member
    exact straight instruction (List.mem_of_mem_take member)
  have position := linearExecute_pc input (code.take count) takeStraight before after executed
  rw [List.length_take, Nat.min_eq_left bound] at position
  have inside : after.pc ≤ before.pc + code.length := by omega
  exact (sources count bound after executed).safe caller assigned ((PDROC.DataBits.natBits_mono inside).trans pc)

end PDROC.CalibrationRow.ScatterOperands
