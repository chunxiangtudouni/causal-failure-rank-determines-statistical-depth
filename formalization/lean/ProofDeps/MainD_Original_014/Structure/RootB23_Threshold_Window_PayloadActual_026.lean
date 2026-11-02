module

public import Structure.RootB23_Threshold_Window_PayloadCost_025
public import Structure.RootB23_Threshold_Window_Margin_021

/-! Instantiate all four physical copied fields with the actual observations
made from the original bare pair. No saved-bit tuple is a caller input. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section
namespace PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadActual
open Turing PSTRTMSeq005 PA17TMRatArithmeticParse002 PA17TMRatArithmeticBookmark014
open PA17TMRatArithmeticWidth018 (BoundedRun)

def fields (x y : Rat) : List Bool :=
  PSTRTMIncrement009.blocks (numeratorDigits x) ++ [false,false,true,false] ++
    PSTRTMIncrement009.blocks (denominatorDigits x) ++ [false,false,true,false] ++
    PSTRTMIncrement009.blocks (numeratorDigits y) ++ [false,false,true,false] ++
    PSTRTMIncrement009.blocks (denominatorDigits y) ++ [false,false]

def archive (base : List Bool) (x y : Rat) : List Bool :=
  PayloadFour.retainedArchive (sign x :: base) (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail (fieldWidth x y)

theorem actual_a (x y : Rat) :
    PayloadFour.a (mNx x y).val (numeratorDigits x).tail = numeratorDigits x := by
  unfold PayloadFour.a
  rw [(observed_memory_bits x y).2.2.2.2]
  exact (digits_observedFirst (numeratorDigits x) (numerator_ne_nil x)).symm

theorem actual_b (x y : Rat) :
    PayloadFour.b (mNx x y).val (denominatorDigits x).tail = denominatorDigits x := by
  unfold PayloadFour.b
  rw [(observed_memory_bits x y).2.2.2.1]
  exact (digits_observedFirst (denominatorDigits x) (denominator_ne_nil x)).symm

theorem actual_c (x y : Rat) :
    PayloadFour.c (mNx x y).val (numeratorDigits y).tail = numeratorDigits y := by
  unfold PayloadFour.c
  rw [(observed_memory_bits x y).2.1]
  exact (digits_observedFirst (numeratorDigits y) (numerator_ne_nil y)).symm

theorem actual_d (x y : Rat) :
    PayloadFour.d (mNx x y).val (denominatorDigits y).tail = denominatorDigits y := by
  unfold PayloadFour.d
  rw [(observed_memory_bits x y).1]
  exact (digits_observedFirst (denominatorDigits y) (denominator_ne_nil y)).symm

theorem actual_bounded (k : Nat) (base : List Bool) (x y : Rat) :
    BoundedRun (PayloadFour.machine (mNx x y).val)
      (Tape.mk₂ (false :: BareReserve.retainedArchive base x y)
        (powerWord (fieldWidth x y) 4 (k * fieldWidth x y ^ 4))) 5160
      (Tape.mk₂ (List.replicate (k * fieldWidth x y ^ 4 + 4) false ++ archive base x y) (fields x y))
      ((8192 * (k + 3) ^ 2) * (fieldWidth x y + 1) ^ 8) := by
  have row := PayloadFour.four_bounded (mNx x y).val (sign x :: base)
    (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail
    (fieldWidth x y) (k * fieldWidth x y ^ 4)
  have cost := PayloadCost.quartic_fee_le k (mNx x y).val
    (numeratorDigits x).tail (denominatorDigits x).tail
    (numeratorDigits y).tail (denominatorDigits y).tail
  rw [BareReserve.width_eq] at cost
  have actual := row.mono cost
  simpa only [archive, fields, BareReserve.retainedArchive, actual_a, actual_b, actual_c, actual_d,
    PayloadSteps.word4, PayloadNav.word3, PayloadNav.word2, PA17TMRatArithmeticCopy006.workspace,
    List.append_assoc, List.cons_append, List.nil_append, List.append_nil] using actual

theorem gap_at_least_three (k : Nat) (positive : 0 < k) (x y : Rat) :
    3 ≤ k * fieldWidth x y ^ 4 := by
  have width := Margin.rational_width_at_least_four x y
  have power := Nat.pow_le_pow_left width 4
  norm_num at power
  have scaled := Nat.mul_le_mul_left k power
  nlinarith

theorem owned_seven (left : List Bool) (gap : Nat) (enough : 3 ≤ gap) :
    List.replicate (gap + 4) false ++ left =
      List.replicate 7 false ++ (List.replicate (gap - 3) false ++ left) := by
  rw [show gap + 4 = 7 + (gap - 3) by omega, List.replicate_add, List.append_assoc]

end PaperProofs.Common.Native.RationalControllerComputation.RootB23ThresholdWindow.PayloadActual
