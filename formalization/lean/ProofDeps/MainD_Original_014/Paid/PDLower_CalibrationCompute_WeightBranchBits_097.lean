module

public import Paid.PDLower_CalibrationCompute_Weight_033
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDROC_CalibrationRow_OperandPrefix_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 600000

@[expose] public section

open PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

theorem divide_bitSegment (origin : ℕ) (input : List Cell) (before : State) (numerator denominator : ℚ) (budget : ℕ)
    (position : before.pc=labelAddress origin .divide) (safe : SafeBits before budget)
    (total : before.register .total=.rational numerator) (value : before.register .value=.rational denominator)
    (nonzero : denominator≠0) (quotientBits : (Cell.rational (numerator/denominator)).bits≤budget)
    (pcBits : natBits (before.pc+1)≤budget) (emitBits : natBits (labelAddress origin .emit)≤budget) :
    BitSegment origin input before
      {(divideResult before numerator denominator) with pc:=labelAddress origin .emit} 45 budget := by
  let middle := divideResult before numerator denominator
  let after : State := {middle with pc:=labelAddress origin .emit}
  have body : linearExecute input (basicBlock .divide).body before=some middle :=
    divide_execute input before numerator denominator total value nonzero
  have prefixes := PrefixSafe.ratOp input before budget .divide .value .total .value numerator denominator
    (numerator/denominator) safe total value (by simp [RatOp.eval,nonzero]) quotientBits pcBits
  have control : (controlInstruction origin (basicBlock .divide).control).execute input middle=some after := rfl
  exact BitSegment.ofBlock origin .divide input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) ((prefixes.final body).withPC _ emitBits)

theorem zeroWeight_bitSegment (origin : ℕ) (input : List Cell) (before : State) (budget : ℕ)
    (position : before.pc=labelAddress origin .zeroWeight) (safe : SafeBits before budget)
    (zeroBits : (Cell.rational 0).bits≤budget) (pcBits : natBits (before.pc+1)≤budget)
    (emitBits : natBits (labelAddress origin .emit)≤budget) :
    BitSegment origin input before
      {({before with pc:=before.pc+1}.set .value (.rational 0)) with pc:=labelAddress origin .emit} 45 budget := by
  let middle := {before with pc:=before.pc+1}.set .value (.rational 0)
  let after : State := {middle with pc:=labelAddress origin .emit}
  have body : linearExecute input (basicBlock .zeroWeight).body before=some middle := zeroWeight_execute input before
  have prefixes := PrefixSafe.constant input before budget .value (.rational 0) safe zeroBits pcBits
  have control : (controlInstruction origin (basicBlock .zeroWeight).control).execute input middle=some after := rfl
  exact BitSegment.ofBlock origin .zeroWeight input before middle after budget position body control
    (fun count _ state executed => prefixes count state executed) ((prefixes.final body).withPC _ emitBits)

end PDLower.CalibrationCompute
