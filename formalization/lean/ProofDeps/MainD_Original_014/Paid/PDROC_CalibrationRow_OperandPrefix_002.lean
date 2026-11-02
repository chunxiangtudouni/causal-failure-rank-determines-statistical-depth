module

public import Paid.PDROC_CalibrationRow_OperandPrefix_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Fixed literal assignment; the untouched incoming cells keep the caller
budget, and only the actual new Cell and PC require concrete bounds. -/
theorem PrefixSafe.constant (input : List Cell) (before : State) (budget : ℕ)
    (target : Register) (value : Cell) (safe : SafeBits before budget)
    (valueBits : value.bits≤budget) (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.constant target value] before budget := by
  exact PrefixSafe.singleton input (.constant target value) before
    (({before with pc:=before.pc+1}).set target value) budget rfl safe
    ((safe.withPC _ pcBits).set target value valueBits)

theorem PrefixSafe.move (input : List Cell) (before : State) (budget : ℕ)
    (target source : Register) (safe : SafeBits before budget)
    (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.move target source] before budget := by
  exact PrefixSafe.singleton input (.move target source) before
    (({before with pc:=before.pc+1}).set target (before.register source)) budget rfl safe
    ((safe.withPC _ pcBits).set target (before.register source) (safe.register source))

theorem PrefixSafe.natOp (input : List Cell) (before : State) (budget : ℕ)
    (operation : NatOp) (target left right : Register) (x y result : ℕ)
    (safe : SafeBits before budget) (leftValue : before.register left=.natural x)
    (rightValue : before.register right=.natural y) (evaluated : operation.eval x y=some result)
    (valueBits : (Cell.natural result).bits≤budget) (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.natOp operation target left right] before budget := by
  have actual : (Instruction.natOp operation target left right).execute input before=
      some (({before with pc:=before.pc+1}).set target (.natural result)) := by
    simp [Instruction.execute,leftValue,rightValue,Cell.nat?,evaluated]
  exact PrefixSafe.singleton input _ before _ budget actual safe
    ((safe.withPC _ pcBits).set target (.natural result) valueBits)

theorem PrefixSafe.ratOp (input : List Cell) (before : State) (budget : ℕ)
    (operation : RatOp) (target left right : Register) (x y result : ℚ)
    (safe : SafeBits before budget) (leftValue : before.register left=.rational x)
    (rightValue : before.register right=.rational y) (evaluated : operation.eval x y=some result)
    (valueBits : (Cell.rational result).bits≤budget) (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.ratOp operation target left right] before budget := by
  have actual : (Instruction.ratOp operation target left right).execute input before=
      some (({before with pc:=before.pc+1}).set target (.rational result)) := by
    simp [Instruction.execute,leftValue,rightValue,Cell.rat?,evaluated]
  exact PrefixSafe.singleton input _ before _ budget actual safe
    ((safe.withPC _ pcBits).set target (.rational result) valueBits)

theorem PrefixSafe.natCompare (input : List Cell) (before : State) (budget : ℕ)
    (comparison : Comparison) (target left right : Register) (x y : ℕ)
    (safe : SafeBits before budget) (leftValue : before.register left=.natural x)
    (rightValue : before.register right=.natural y)
    (zeroBits : (Cell.natural 0).bits≤budget) (oneBits : (Cell.natural 1).bits≤budget)
    (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.natCompare comparison target left right] before budget := by
  let value : Cell := .natural (if comparison.nat x y then 1 else 0)
  have valueBits : value.bits≤budget := by
    dsimp only [value]
    split_ifs
    · exact oneBits
    · exact zeroBits
  have actual : (Instruction.natCompare comparison target left right).execute input before=
      some (({before with pc:=before.pc+1}).set target value) := by
    simp [Instruction.execute,leftValue,rightValue,Cell.nat?,value]
  exact PrefixSafe.singleton input _ before _ budget actual safe
    ((safe.withPC _ pcBits).set target value valueBits)

theorem PrefixSafe.load (input : List Cell) (before : State) (budget : ℕ)
    (target pointer : Register) (location : ℕ) (safe : SafeBits before budget)
    (address : before.register pointer=.natural location) (live : location∈before.live)
    (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.load target pointer] before budget := by
  have actual : (Instruction.load target pointer).execute input before=
      some (({before with pc:=before.pc+1}).set target (before.heap location)) := by
    simp [Instruction.execute,address,Cell.nat?,live]
  exact PrefixSafe.singleton input _ before _ budget actual safe
    ((safe.withPC _ pcBits).set target (before.heap location) (safe.heap location live))

theorem PrefixSafe.store (input : List Cell) (before : State) (budget : ℕ)
    (pointer source : Register) (location : ℕ) (safe : SafeBits before budget)
    (address : before.register pointer=.natural location)
    (pcBits : natBits (before.pc+1)≤budget) :
    PrefixSafe input [.store pointer source] before budget := by
  have registerBits := safe.register pointer
  rw [address] at registerBits
  have addressBits : natBits location≤budget := by change 1+natBits location≤budget at registerBits; omega
  let after : State :=
    {before with
      heap:=Function.update before.heap location (before.register source)
      live:=insert location before.live
      pc:=before.pc+1}
  have actual : (Instruction.store pointer source).execute input before=some after := by
    simp [Instruction.execute,address,Cell.nat?,after]
  exact PrefixSafe.singleton input _ before after budget actual safe
    ((safe.withPC _ pcBits).store location (before.register source) addressBits (safe.register source))

end PDROC.CalibrationRow.Operand
