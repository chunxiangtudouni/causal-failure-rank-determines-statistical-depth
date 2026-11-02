module

public import RootB234_PrepExponent_QLoopMul024

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace RootB234.PrepExponent.QLoop
open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation PSTRWordVM
open RootL01.SymbolicSource
variable {C : Type*}

theorem bank_update11 (background : Stack → List Bool) (cache counter input trash next : List Bool) :
    Function.update (bank background cache counter input trash) 11 next=bank background cache next input trash := by
  funext slot
  fin_cases slot <;> rfl

theorem bank_update15 (background : Stack → List Bool) (cache counter input trash next : List Bool) :
    Function.update (bank background cache counter input trash) 15 next=bank background cache counter next trash := by
  funext slot
  fin_cases slot <;> rfl

theorem round_take_step (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache counter : List Bool) :
    TM2.step (program caller) (state .take memory (bank background cache (true::counter) [] []))=
      some (state (.copyQ 0) (memory.1,true,true) (bank background cache counter [] [])) := by
  simpa only [state,bank_update11] using
    take_positive caller memory (bank background cache (true::counter) [] []) counter rfl

theorem round_literal_step (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (cache counter : List Bool) (value : Rat) :
    TM2.step (program caller) (state .literalTwo memory
      (bank background cache counter (RatInput.Encoder.packet value []) []))=
      some (state (.mul default) memory (bank background cache counter (RatPair.input (2 : Rat) value []) [])) := by
  simpa only [bank_update15,RatPair.input,RatPair.packet,List.append_nil,
    show bank background cache counter (RatInput.Encoder.packet value []) [] 15=
      RatInput.Encoder.packet value [] from rfl] using
    literalTwo_step caller memory (bank background cache counter (RatInput.Encoder.packet value []) [])

def roundCost (background : Stack → List Bool) (counter tail : List Bool) (value : Rat) : Nat :=
  2+(3*RatInput.Encoder.fieldSize value+14)+2+
    RatBinary.time RatMulDiv.mulCoefficient
      (rawBackground background (RatInput.Encoder.packet value tail) counter) 2 value []
      (RatInput.Encoder.packet value tail)+
    (3*RatInput.Encoder.fieldSize value+14)+((RatInput.Encoder.packet value []).length+2)+
    (3*RatInput.Encoder.fieldSize (2*value)+14)

/-- One actual positive-counter round: copy, literal 2, real rational
multiply, discard and clear the old Q, then park the new Q. -/
theorem round_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (counter tail : List Bool) (value : Rat) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state .take memory (bank background (RatInput.Encoder.packet value tail) (true::counter) [] []))
      (state .take afterMemory (bank background (RatInput.Encoder.packet (2*value) tail) counter [] []))),
      rootContext afterMemory=rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ roundCost background counter tail value := by
  let firstPart := Segment.edge (round_take_step caller background memory (RatInput.Encoder.packet value tail) counter)
  obtain ⟨copyPart,copyCount⟩ := copy_actual caller background (memory.1,true,true) counter tail value
  let literalPart := Segment.edge (round_literal_step caller background (memory.1,false,false)
    (RatInput.Encoder.packet value tail) counter value)
  obtain ⟨midMemory,mulPart,context,mulCount⟩ := mul_actual caller background (memory.1,false,false)
    (RatInput.Encoder.packet value tail) counter 2 value
  obtain ⟨discardPart,discardCount⟩ := discard_actual caller background midMemory counter
    (RatInput.Encoder.packet (2*value) []) tail value
  obtain ⟨clearPart,clearCount⟩ := clear_actual caller background (midMemory.1,false,false) tail counter
    (RatInput.Encoder.packet (2*value) []) (RatInput.Encoder.packet value [])
  obtain ⟨parkPart,parkCount⟩ := park_actual caller background (midMemory.1,false,false) counter tail (2*value)
  let joined1 := firstPart.append copyPart
  let joined2 := joined1.append literalPart
  let joined3 := joined2.append mulPart
  let joined4 := joined3.append discardPart
  let joined5 := joined4.append clearPart
  let whole := joined5.append parkPart
  refine ⟨(midMemory.1,false,false),whole,context,rfl,?_⟩
  have firstCount : firstPart.trace.length=2 := rfl
  have literalCount : literalPart.trace.length=2 := rfl
  have count1 := firstPart.append_length copyPart
  have count2 := joined1.append_length literalPart
  have count3 := joined2.append_length mulPart
  have count4 := joined3.append_length discardPart
  have count5 := joined4.append_length clearPart
  have count6 := joined5.append_length parkPart
  change joined1.trace.length ≤ firstPart.trace.length+copyPart.trace.length at count1
  change joined2.trace.length ≤ joined1.trace.length+literalPart.trace.length at count2
  change joined3.trace.length ≤ joined2.trace.length+mulPart.trace.length at count3
  change joined4.trace.length ≤ joined3.trace.length+discardPart.trace.length at count4
  change joined5.trace.length ≤ joined4.trace.length+clearPart.trace.length at count5
  change whole.trace.length ≤ joined5.trace.length+parkPart.trace.length at count6
  change whole.trace.length ≤ _
  unfold roundCost
  omega

def roundsCost (background : Stack → List Bool) (tail : List Bool) : Nat → Rat → Nat
  | 0,_ => 2
  | count+1,value => roundCost background (List.replicate count true) tail value+
      roundsCost background tail count (2*value)

/-- Every iteration is paid by its actual finite trace. The number of
rounds is read from the physical unary counter; it is absent from the source. -/
theorem rounds_actual (caller : Statement C) (background : Stack → List Bool) (memory : Store C)
    (tail : List Bool) (value : Rat) (count : Nat) :
    ∃ (afterMemory : Store C) (part : Segment caller
      (state .take memory (bank background (RatInput.Encoder.packet value tail) (List.replicate count true) [] []))
      (state .done afterMemory (bank background (RatInput.Encoder.packet (value*(2 : Rat)^count) tail) [] [] []))),
      rootContext afterMemory=rootContext memory ∧ afterMemory.2=(false,false) ∧
      part.trace.length ≤ roundsCost background tail count value := by
  induction count generalizing memory value with
  | zero =>
    rw [pow_zero,mul_one]
    have step : TM2.step (program caller) (state .take memory
        (bank background (RatInput.Encoder.packet value tail) [] [] []))=
        some (state .done (memory.1,false,false)
          (bank background (RatInput.Encoder.packet value tail) [] [] [])) :=
      take_zero caller memory (bank background (RatInput.Encoder.packet value tail) [] [] []) rfl
    let part := Segment.edge step
    have count : part.trace.length ≤ roundsCost background tail 0 value := by rfl
    exact ⟨(memory.1,false,false),part,rfl,rfl,count⟩
  | succ count ih =>
    obtain ⟨middle,front,frontContext,_frontFlags,frontCount⟩ :=
      round_actual caller background memory (List.replicate count true) tail value
    obtain ⟨afterMemory,back,backContext,backFlags,backCount⟩ := ih middle (2*value)
    have valueStep : (2*value)*(2 : Rat)^count=value*(2 : Rat)^(count+1) := by
      rw [pow_succ]
      ring
    let back' : Segment caller
        (state .take middle (bank background (RatInput.Encoder.packet (2*value) tail) (List.replicate count true) [] []))
        (state .done afterMemory (bank background (RatInput.Encoder.packet (value*(2 : Rat)^(count+1)) tail) [] [] [])) :=
      ⟨back.trace,back.first,back.chain,back.last.trans (congrArg some (by rw [valueStep]))⟩
    let whole := front.append back'
    refine ⟨afterMemory,?_,backContext.trans frontContext,backFlags,?_⟩
    · simpa only [List.replicate_succ] using whole
    · have length : whole.trace.length ≤ front.trace.length+back.trace.length := front.append_length back'
      change whole.trace.length ≤ roundsCost background tail (count+1) value
      unfold roundsCost
      omega

end RootB234.PrepExponent.QLoop
