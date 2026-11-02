module

public import RootB234_PrepExponent_QLoopFull026
public import RootB23_WordOddsBits_Core_001

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

theorem two_field : RatInput.Encoder.fieldSize (2 : Rat)=3 := rfl
theorem twelve_field : RatInput.Encoder.fieldSize (12 : Rat)=5 := rfl

theorem double_field (value : Rat) :
    RatInput.Encoder.fieldSize (2*value) ≤ RatInput.Encoder.fieldSize value+3 := by
  have bound := RootB23.WordOddsBits.mul_width_le (2 : Rat) value
  rw [←RootB23.WordOddsBits.ratInput_fieldSize_eq,←RootB23.WordOddsBits.ratInput_fieldSize_eq,
    ←RootB23.WordOddsBits.ratInput_fieldSize_eq,two_field] at bound
  omega

theorem power_field (value : Rat) (count : Nat) :
    RatInput.Encoder.fieldSize (value*(2 : Rat)^count) ≤ RatInput.Encoder.fieldSize value+3*count := by
  induction count with
  | zero => simpa only [pow_zero,mul_one,Nat.mul_zero,Nat.add_zero] using
      Nat.le_refl (RatInput.Encoder.fieldSize value)
  | succ count ih =>
    have multiply := double_field (value*(2 : Rat)^count)
    have same : value*(2 : Rat)^(count+1)=2*(value*(2 : Rat)^count) := by rw [pow_succ];ring
    rw [same]
    omega

theorem bank_length (background : Stack → List Bool) (cache counter input trash : List Bool) (slot : Stack) :
    (bank background cache counter input trash slot).length ≤
      RatInput.occupied background+cache.length+counter.length+input.length+trash.length := by
  have point := RatInput.Encoder.point_mass background slot
  unfold bank
  split_ifs <;> (try simp only [List.length_nil]) <;> omega

theorem pair_outside (background : Stack → List Bool) :
    RatPair.Link.outside background ≤ RatInput.occupied background := by
  unfold RatPair.Link.outside RatInput.occupied
  apply Finset.sum_le_sum
  intro slot _
  split_ifs <;> omega

def roundScale (background : Stack → List Bool) (counter tail : List Bool) (value : Rat) : Nat :=
  RatInput.occupied background+counter.length+tail.length+RatInput.Encoder.fieldSize value+1

theorem roundScale_positive (background : Stack → List Bool) (counter tail : List Bool) (value : Rat) :
    1 ≤ roundScale background counter tail value := by unfold roundScale;omega

theorem pair_space_round (background : Stack → List Bool) (counter tail : List Bool) (value : Rat) :
    RatPair.space (rawBackground background (RatInput.Encoder.packet value tail) counter) 2 value []
      (RatInput.Encoder.packet value tail) ≤ 8192*roundScale background counter tail value := by
  let raw := rawBackground background (RatInput.Encoder.packet value tail) counter
  have each : ∀ slot,(raw slot).length ≤ RatInput.occupied background+
      (RatInput.Encoder.packet value tail).length+counter.length := by
    intro slot
    dsimp only [raw,rawBackground,StackIso.slots]
    simpa only [List.length_nil,Nat.add_zero,Equiv.symm_symm] using
      bank_length background (RatInput.Encoder.packet value tail) counter [] [] (Arithmetic.binaryRoles slot)
  have mass := RatInput.Encoder.occupied_bound raw _ each
  have outside := (pair_outside raw).trans mass
  rw [RatInput.Encoder.packet_length] at outside
  have fields : RatPair.fieldSize (2 : Rat) value=3+RatInput.Encoder.fieldSize value := by
    rw [RatBinary.fieldSize_eq,two_field]
  change RatPair.Link.outside raw+[].length+(RatInput.Encoder.packet value tail).length+
    258*RatPair.fieldSize (2 : Rat) value+2572 ≤ _
  rw [fields,RatInput.Encoder.packet_length]
  unfold roundScale
  simp only [List.length_nil]
  omega

def binaryCoefficient : Nat := 1000000+RatMulDiv.mulCoefficient*1000000^4
def roundCoefficient : Nat := 7*binaryCoefficient+300

theorem binary_space_round (background : Stack → List Bool) (counter tail : List Bool) (value : Rat) :
    RatBinary.space RatMulDiv.mulCoefficient (rawBackground background (RatInput.Encoder.packet value tail) counter)
      2 value [] (RatInput.Encoder.packet value tail) ≤ binaryCoefficient*(roundScale background counter tail value)^4 := by
  let S := roundScale background counter tail value
  let P := RatPair.space (rawBackground background (RatInput.Encoder.packet value tail) counter) 2 value []
    (RatInput.Encoder.packet value tail)
  have positive : 1 ≤ S := roundScale_positive background counter tail value
  have power : S ≤ S^4 := by nlinarith [Nat.pow_le_pow_right positive (show 1 ≤ 4 by decide)]
  have pBound : P ≤ 8192*S := pair_space_round background counter tail value
  have base : 16*P+1 ≤ 1000000*S := by omega
  have raw : RatBinary.rawBound RatMulDiv.mulCoefficient
      (rawBackground background (RatInput.Encoder.packet value tail) counter) 2 value []
      (RatInput.Encoder.packet value tail) ≤ RatMulDiv.mulCoefficient*1000000^4*S^4 := by
    change RatMulDiv.mulCoefficient*(16*P+1)^4 ≤ _
    exact (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left base 4)).trans_eq (by ring)
  have linear : 16*P+8 ≤ 1000000*S^4 := by omega
  change 16*P+RatBinary.rawBound RatMulDiv.mulCoefficient
    (rawBackground background (RatInput.Encoder.packet value tail) counter) 2 value []
    (RatInput.Encoder.packet value tail)+8 ≤ binaryCoefficient*S^4
  unfold binaryCoefficient
  nlinarith only [raw,linear]

theorem roundCost_polynomial (background : Stack → List Bool) (counter tail : List Bool) (value : Rat) :
    roundCost background counter tail value ≤ roundCoefficient*(roundScale background counter tail value)^4 := by
  let S := roundScale background counter tail value
  have positive : 1 ≤ S := roundScale_positive background counter tail value
  have power : S ≤ S^4 := by nlinarith [Nat.pow_le_pow_right positive (show 1 ≤ 4 by decide)]
  have one : 1 ≤ S^4 := positive.trans power
  have valueBound : RatInput.Encoder.fieldSize value ≤ S := by unfold S roundScale;omega
  have doubled := double_field value
  have fields : RatPair.fieldSize (2 : Rat) value=3+RatInput.Encoder.fieldSize value := by
    rw [RatBinary.fieldSize_eq,two_field]
  have space := binary_space_round background counter tail value
  change _ ≤ binaryCoefficient*S^4 at space
  change _ ≤ roundCoefficient*S^4
  unfold roundCost RatBinary.time
  rw [fields,RatInput.Encoder.packet_length]
  simp only [List.length_nil,Nat.add_zero]
  unfold roundCoefficient
  nlinarith only [space,doubled,valueBound,power,one]

end RootB234.PrepExponent.QLoop
