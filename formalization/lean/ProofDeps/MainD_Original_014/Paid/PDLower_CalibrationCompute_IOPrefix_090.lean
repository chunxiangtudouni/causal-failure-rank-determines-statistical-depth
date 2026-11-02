module

public import Paid.PDLower_CalibrationCompute_IOBits_088
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem output_sameBudget (input : List Cell) (before : State) (source : Register) (budget : ℕ)
    (safe : SafeBits before budget) (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.output source] before budget := by
  let after : State := {before with pc:=before.pc+1,output:=before.output++[before.register source]}
  have actual : Instruction.execute input (.output source) before=some after := rfl
  exact PrefixSafe.singleton input (.output source) before after budget actual safe
    (output_execute_safe input before after source budget safe pcBits actual)

theorem loadInput_sameBudget (input : List Cell) (before : State) (target pointer : Register)
    (location budget : ℕ) (value : Cell) (safe : SafeBits before budget)
    (address : before.register pointer=.natural location) (fetched : input[location]?=some value)
    (valueBits : value.bits≤budget) (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.loadInput target pointer] before budget := by
  let after : State := ({before with pc:=before.pc+1}).set target value
  have actual : Instruction.execute input (.loadInput target pointer) before=some after := by
    simp [Instruction.execute,address,Cell.nat?,fetched,after]
  exact PrefixSafe.singleton input (.loadInput target pointer) before after budget actual safe
    (loadInput_execute_safe input before after target pointer location budget value safe address fetched valueBits pcBits actual)

theorem ratCompare_sameBudget (input : List Cell) (before : State)
    (comparison : Comparison) (target left right : Register) (x y : ℚ) (budget : ℕ)
    (safe : SafeBits before budget) (leftValue : before.register left=.rational x)
    (rightValue : before.register right=.rational y)
    (zeroBits : (Cell.natural 0).bits≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.ratCompare comparison target left right] before budget := by
  let after : State := ({before with pc:=before.pc+1}).set target
    (.natural (if comparison.rat x y then 1 else 0))
  have actual : Instruction.execute input (.ratCompare comparison target left right) before=some after := by
    simp [Instruction.execute,leftValue,rightValue,Cell.rat?,after]
  exact PrefixSafe.singleton input (.ratCompare comparison target left right) before after budget actual safe
    (ratCompare_execute_safe input before after comparison target left right x y budget safe leftValue rightValue zeroBits oneBits pcBits actual)

end PDLower.CalibrationCompute
