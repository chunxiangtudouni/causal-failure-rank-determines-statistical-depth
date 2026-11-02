module

public import RootB234_PrepExponent_GlobalCompare038

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.Global
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

def repeatCost (background : Stack → List Bool) (tail : List Bool) (right left : Rat) (number : Nat) : Nat :=
  let cache := RatInput.Encoder.packet left (RatInput.Encoder.packet right tail)
  RatBinary.time RatMulDiv.mulCoefficient
    (QLoop.rawBackground background cache (B23_4_RatWordPrep.NatField.packet number [])) 2 left [] cache+
    8*RatInput.Encoder.fieldSize left+3*RatInput.Encoder.fieldSize (2*left)+
    3*(PSTRTMNatValue017.rawPayload number).length+55

/-- False-test continuation: actual double-Y, dispose/clear its old
packet, park the real product, and increment the physical binary E. -/
theorem repeat_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (right left : Rat) (number : Nat) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state (.packet .repeatCopyY 0) memory
        (bank background (RatInput.Encoder.packet left (RatInput.Encoder.packet right tail))
          (B23_4_RatWordPrep.NatField.packet number []) [] [] [] []))
      (state (.packet .compareCopyY 0) afterMemory
        (bank background (RatInput.Encoder.packet (2*left) (RatInput.Encoder.packet right tail))
          (B23_4_RatWordPrep.NatField.packet (number+1) []) [] [] [] []))),
      QLoop.rootContext afterMemory=QLoop.rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ repeatCost background tail right left number := by
  let rtail := RatInput.Encoder.packet right tail
  let cache := RatInput.Encoder.packet left rtail
  let exponent := B23_4_RatWordPrep.NatField.packet number []
  obtain ⟨copyY,copyCount⟩ := copy7_actual caller .repeatCopyY rfl rfl background memory rtail exponent [] [] [] left
  let literal := Segment.edge (literal_pair_step caller .nextY background (memory.1,false,false) cache exponent [] left)
  obtain ⟨midMemory,multiply,multiplyContext,multiplyCount⟩ := mul_actual caller .nextY background
    (memory.1,false,false) cache exponent 2 left []
  obtain ⟨discard,discardCount⟩ := pull12_actual caller .repeatDiscardY rfl rfl background midMemory
    rtail exponent (RatInput.Encoder.packet (2*left) []) [] left
  obtain ⟨clear,clearCount⟩ := clear_actual caller .repeatY background (midMemory.1,false,false)
    rtail exponent (RatInput.Encoder.packet (2*left) []) (RatInput.Encoder.packet left [])
  obtain ⟨park,parkCount⟩ := park15_actual caller .repeatParkY rfl rfl background (midMemory.1,false,false)
    rtail exponent [] [] (2*left)
  obtain ⟨increment,incrementCount⟩ := increment_actual caller background (midMemory.1,false,false)
    (RatInput.Encoder.packet (2*left) rtail) number
  let j1 := copyY.append literal
  let j2 := j1.append multiply
  let j3 := j2.append discard
  let j4 := j3.append clear
  let j5 := j4.append park
  let whole := j5.append increment
  refine ⟨(midMemory.1,false,false),whole,multiplyContext,rfl,?_⟩
  have literalCount : literal.trace.length=2 := rfl
  rw [RatInput.Encoder.packet_length] at clearCount
  simp only [List.length_nil,Nat.add_zero] at clearCount
  have c1 : j1.trace.length ≤ copyY.trace.length+literal.trace.length := copyY.append_length literal
  have c2 : j2.trace.length ≤ j1.trace.length+multiply.trace.length := j1.append_length multiply
  have c3 : j3.trace.length ≤ j2.trace.length+discard.trace.length := j2.append_length discard
  have c4 : j4.trace.length ≤ j3.trace.length+clear.trace.length := j3.append_length clear
  have c5 : j5.trace.length ≤ j4.trace.length+park.trace.length := j4.append_length park
  have c6 : whole.trace.length ≤ j5.trace.length+increment.trace.length := j5.append_length increment
  unfold repeatCost
  change whole.trace.length ≤ RatBinary.time RatMulDiv.mulCoefficient (QLoop.rawBackground background cache exponent) 2 left [] cache+
    8*RatInput.Encoder.fieldSize left+3*RatInput.Encoder.fieldSize (2*left)+3*(PSTRTMNatValue017.rawPayload number).length+55
  omega

def stopCost (right left q budget : Rat) : Nat :=
  5*RatInput.Encoder.fieldSize left+5*RatInput.Encoder.fieldSize right+
    6*RatInput.Encoder.fieldSize q+3*RatInput.Encoder.fieldSize budget+86

/-- True-test continuation: actually clear old Y/R, temporarily move Q,
restore the original budget15, then restore Q7 and return ACTIVE done. -/
theorem stop_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail exponent : List Bool) (right left q budget : Rat) :
    ∃ part : Segment caller
      (state (.packet .stopDropY 0) memory
        (bank background (RatInput.Encoder.packet left (RatInput.Encoder.packet right
          (RatInput.Encoder.packet q (RatInput.Encoder.packet budget tail)))) exponent [] [] [] []))
      (state .done (memory.1,false,false)
        (bank background (RatInput.Encoder.packet q (RatInput.Encoder.packet budget tail)) exponent
          (RatInput.Encoder.packet budget []) [] [] [])),
      part.trace.length ≤ stopCost right left q budget := by
  let bcache := RatInput.Encoder.packet budget tail
  let cache := RatInput.Encoder.packet q bcache
  let rtail := RatInput.Encoder.packet right cache
  obtain ⟨dropY,dropYCount⟩ := pull12_actual caller .stopDropY rfl rfl background memory rtail exponent [] [] left
  obtain ⟨clearY,clearYCount⟩ := clear_actual caller .stopY background (memory.1,false,false)
    rtail exponent [] (RatInput.Encoder.packet left [])
  obtain ⟨dropR,dropRCount⟩ := pull12_actual caller .stopDropR rfl rfl background (memory.1,false,false) cache exponent [] [] right
  obtain ⟨clearR,clearRCount⟩ := clear_actual caller .stopR background (memory.1,false,false)
    cache exponent [] (RatInput.Encoder.packet right [])
  obtain ⟨pullQ,pullQCount⟩ := pull12_actual caller .stopPullQ rfl rfl background (memory.1,false,false) bcache exponent [] [] q
  obtain ⟨copyB,copyBCount⟩ := copy7_actual caller .stopCopyBudget rfl rfl background (memory.1,false,false)
    tail exponent [] (RatInput.Encoder.packet q []) [] budget
  obtain ⟨restoreQ,restoreQCount⟩ := restore12_actual caller .stopRestoreQ rfl rfl background (memory.1,false,false)
    bcache exponent (RatInput.Encoder.packet budget []) [] q
  let j1 := dropY.append clearY
  let j2 := j1.append dropR
  let j3 := j2.append clearR
  let j4 := j3.append pullQ
  let j5 := j4.append copyB
  let whole := j5.append restoreQ
  refine ⟨whole,?_⟩
  rw [RatInput.Encoder.packet_length] at clearYCount clearRCount
  simp only [List.length_nil,Nat.add_zero] at clearYCount clearRCount
  have c1 : j1.trace.length ≤ dropY.trace.length+clearY.trace.length := dropY.append_length clearY
  have c2 : j2.trace.length ≤ j1.trace.length+dropR.trace.length := j1.append_length dropR
  have c3 : j3.trace.length ≤ j2.trace.length+clearR.trace.length := j2.append_length clearR
  have c4 : j4.trace.length ≤ j3.trace.length+pullQ.trace.length := j3.append_length pullQ
  have c5 : j5.trace.length ≤ j4.trace.length+copyB.trace.length := j4.append_length copyB
  have c6 : whole.trace.length ≤ j5.trace.length+restoreQ.trace.length := j5.append_length restoreQ
  unfold stopCost
  omega

end RootB234.PrepExponent.Global
