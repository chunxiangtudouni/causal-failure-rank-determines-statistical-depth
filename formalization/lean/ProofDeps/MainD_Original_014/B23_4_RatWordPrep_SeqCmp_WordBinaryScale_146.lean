module

public import B23_4_RatWordPrep_SeqCmp_WordBinaryResources_143
public import B23_4_RatWordPrep_SeqCmp_WordPacketResources_141

@[expose] public section
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

namespace B23_4_RatWordPrep.WordFinish.Resources

open Turing
open PaperProofs.Common.Native PaperProofs.Common.Native.PSTRWordBool
open RationalControllerComputation

variable {C : Type*}

theorem pair_outside_le_mass (background : RatInput.Stack → List Bool) :
    RatPair.Link.outside background≤RatInput.occupied background := by
  unfold RatPair.Link.outside RatInput.occupied
  apply Finset.sum_le_sum
  intro slot _member
  split_ifs <;> omega

theorem pair_fields_le_mass (before : State C) (x y : Rat) (tail : List Bool)
    (source : before.stk 15=RatPair.input x y tail) :
    RatPair.fieldSize x y≤RatInput.occupied before.stk ∧ tail.length≤RatInput.occupied before.stk := by
  have mass := RatInput.Encoder.point_mass before.stk 15
  rw [source,SeqCmp.pair_length] at mass
  omega

/-- The parent assembler's own input scale is bounded by CURRENT
canonical entry mass, with the two operands physically present on15. -/
theorem pair_space_le_mass (before : State C) (x y : Rat) (tail : List Bool)
    (source : before.stk 15=RatPair.input x y tail) :
    RatPair.space before.stk x y tail (before.stk 7)≤3000*scale before := by
  have fields := pair_fields_le_mass before x y tail source
  have outside := pair_outside_le_mass before.stk
  have scratch := RatInput.Encoder.point_mass before.stk 7
  change RatPair.Link.outside before.stk+tail.length+(before.stk 7).length+
    258*RatPair.fieldSize x y+2572≤3000*(RatInput.occupied before.stk+1)
  omega

def binaryScaleCoefficient (coefficient : Nat) : Nat := 48008+coefficient*48001^4

theorem binary_space_le_mass (coefficient : Nat) (before : State C) (x y : Rat) (tail : List Bool)
    (source : before.stk 15=RatPair.input x y tail) :
    RatBinary.space coefficient before.stk x y tail (before.stk 7)≤binaryScaleCoefficient coefficient*(scale before)^4 := by
  let S := scale before
  let P := RatPair.space before.stk x y tail (before.stk 7)
  have scalePositive : 1≤S := by unfold S scale; omega
  have power := SeqCmp.linear_fourth S scalePositive
  have pBound : P≤3000*S := pair_space_le_mass before x y tail source
  have base : 16*P+1≤48001*S := by omega
  have powered := Nat.pow_le_pow_left base 4
  have raw : RatBinary.rawBound coefficient before.stk x y tail (before.stk 7)≤coefficient*48001^4*S^4 := by
    calc
      _=coefficient*(16*P+1)^4 := rfl
      _≤coefficient*(48001*S)^4 := Nat.mul_le_mul_left coefficient powered
      _=coefficient*48001^4*S^4 := by ring
  have linear : 16*P+8≤48008*S^4 := by omega
  calc
    _=16*P+RatBinary.rawBound coefficient before.stk x y tail (before.stk 7)+8 := rfl
    _≤48008*S^4+coefficient*48001^4*S^4 := by omega
    _=binaryScaleCoefficient coefficient*S^4 := by unfold binaryScaleCoefficient; ring

theorem binary_internal_le_mass (coefficient : Nat) (before : State C) (x y : Rat) (tail : List Bool)
    (source : before.stk 15=RatPair.input x y tail) :
    RatBinary.space coefficient before.stk x y tail (before.stk 7)+32≤
      (binaryScaleCoefficient coefficient+32)*(scale before)^4 := by
  have positive : 1≤scale before := by unfold scale; omega
  have power : 1≤(scale before)^4 := positive.trans (SeqCmp.linear_fourth _ positive)
  calc
    _≤binaryScaleCoefficient coefficient*(scale before)^4+32*(scale before)^4 :=
      Nat.add_le_add (binary_space_le_mass coefficient before x y tail source)
        (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 32 power)
    _=(binaryScaleCoefficient coefficient+32)*(scale before)^4 := by ring

theorem binary_clock_le_mass (coefficient : Nat) (before : State C) (x y : Rat) (tail : List Bool)
    (source : before.stk 15=RatPair.input x y tail) :
    64*(RatBinary.space coefficient before.stk x y tail (before.stk 7)+33)≤
      (64*(binaryScaleCoefficient coefficient+33))*(scale before)^4 := by
  have positive : 1≤scale before := by unfold scale; omega
  have power : 1≤(scale before)^4 := positive.trans (SeqCmp.linear_fourth _ positive)
  have base : RatBinary.space coefficient before.stk x y tail (before.stk 7)+33≤
      binaryScaleCoefficient coefficient*(scale before)^4+33*(scale before)^4 :=
    Nat.add_le_add (binary_space_le_mass coefficient before x y tail source)
      (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left 33 power)
  exact (Nat.mul_le_mul_left 64 base).trans_eq (by ring)

theorem binary_time_le_mass (coefficient : Nat) (before : State C) (x y : Rat) (tail : List Bool)
    (source : before.stk 15=RatPair.input x y tail) :
    RatBinary.time coefficient before.stk x y tail (before.stk 7)≤
      (7*binaryScaleCoefficient coefficient+137)*(scale before)^4 := by
  have positive : 1≤scale before := by unfold scale; omega
  have power := SeqCmp.linear_fourth (scale before) positive
  have massScale : RatInput.occupied before.stk≤scale before := by unfold scale; omega
  have fields : RatPair.fieldSize x y≤(scale before)^4 :=
    (pair_fields_le_mass before x y tail source).1.trans (massScale.trans power)
  have space := binary_space_le_mass coefficient before x y tail source
  have one : 1≤(scale before)^4 := positive.trans power
  change 9*RatPair.fieldSize x y+7*RatBinary.space coefficient before.stk x y tail (before.stk 7)+128≤_
  nlinarith

theorem RunBounds.mono {caller : Statement C} {before final : State C} {run : Segment caller before final}
    {time space clock time' space' clock' : Nat} (bounds : RunBounds caller run time space clock)
    (timeBound : time≤time') (spaceBound : space≤space') (clockBound : clock≤clock') :
    RunBounds caller run time' space' clock' := by
  constructor
  · exact bounds.count.trans timeBound
  · intro current member slot; exact (bounds.boundary current member slot).trans spaceBound
  · intro current member point selected node inside slot
    exact (bounds.internal current member point selected node inside slot).trans spaceBound
  · intro current member point selected; exact (bounds.clocks current member point selected).trans clockBound

end B23_4_RatWordPrep.WordFinish.Resources
