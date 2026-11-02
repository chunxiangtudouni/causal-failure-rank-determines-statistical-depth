module

public import Paid.RootD27Bits_SlotPrefix_004

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits

namespace PDLower.CalibrationCompute

/-- One real input load uses the actual indexed readonly value. -/
theorem loadInput_execute_safe (input : List Cell) (before after : State)
    (target pointer : Register) (location budget : ℕ) (value : Cell)
    (safe : SafeBits before budget) (address : before.register pointer=.natural location)
    (fetched : input[location]?=some value) (valueBits : value.bits≤budget)
    (pcBits : natBits (before.pc+1)≤budget)
    (actual : Instruction.execute input (.loadInput target pointer) before=some after) :
    SafeBits after budget := by
  simp [Instruction.execute,address,Cell.nat?,fetched] at actual
  subst after
  exact (safe.withPC _ pcBits).set target value valueBits

/-- Output is the actual append to the existing caller stream. -/
theorem output_execute_safe (input : List Cell) (before after : State) (source : Register) (budget : ℕ)
    (safe : SafeBits before budget) (pcBits : natBits (before.pc+1)≤budget)
    (actual : Instruction.execute input (.output source) before=some after) : SafeBits after budget := by
  simp only [Instruction.execute] at actual
  have equal := Option.some.inj actual
  subst after
  apply SafeBits.of_fields
  · exact safe.register
  · exact safe.address
  · exact safe.heap
  · intro value member
    rcases List.mem_append.mp member with old|new
    · exact safe.output value old
    · have equal : value=before.register source := List.mem_singleton.mp new
      subst value
      exact safe.register source
  · exact pcBits

theorem ratCompare_execute_safe (input : List Cell) (before after : State)
    (comparison : Comparison) (target left right : Register) (x y : ℚ) (budget : ℕ)
    (safe : SafeBits before budget) (leftValue : before.register left=.rational x)
    (rightValue : before.register right=.rational y)
    (zeroBits : (Cell.natural 0).bits≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (pcBits : natBits (before.pc+1)≤budget)
    (actual : Instruction.execute input (.ratCompare comparison target left right) before=some after) :
    SafeBits after budget := by
  simp [Instruction.execute,leftValue,rightValue,Cell.rat?] at actual
  subst after
  apply (safe.withPC _ pcBits).set target
  split_ifs
  · exact oneBits
  · exact zeroBits

end PDLower.CalibrationCompute
