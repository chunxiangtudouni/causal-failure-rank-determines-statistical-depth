module

public import Paid.PDROC_BitVM_Codec_Output_List_014

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDROC.BitVM.Codec.OutputList

open Turing

def listTimeCoefficient : ℕ :=
  16384 * (PDROC.BitVM.Common.sourcePushCap countProgram Finset.univ + 1)

def listSpaceCoefficient : ℕ :=
  listTimeCoefficient * (PDROC.BitVM.Common.sourcePushCap finalProgram Finset.univ + 1)

/-- The count starts at the ACTUALLY initialized zero. This is a cubic in
actual emission ticks/data lengths, not in an arbitrary binary operand's
numeric value. The coefficient depends only on the fixed source code. -/
theorem listFinalBudget_cubic (word bytes ticks initialLeft : List Bool) :
    listFinalBudget word bytes ticks initialLeft ≤
      listTimeCoefficient * (listInitialBudget word bytes ticks initialLeft + 1) ^ 3 := by
  let U := listInitialBudget word bytes ticks initialLeft + 1
  let C := PDROC.BitVM.Common.sourcePushCap countProgram Finset.univ
  have positive : 1 ≤ U := by dsimp only [U]; omega
  have square : U ≤ U ^ 2 := by
    simpa only [Nat.mul_one, ← pow_two] using Nat.mul_le_mul_left U positive
  have cube : U ^ 2 ≤ U ^ 3 := by
    nlinarith [Nat.mul_le_mul_left (U ^ 2) positive]
  have selfCube := square.trans cube
  have oneCube := positive.trans selfCube
  have input : listInitialBudget word bytes ticks initialLeft ≤ U := by dsimp only [U]; omega
  have wordSize : word.length ≤ U := by dsimp only [U, listInitialBudget]; omega
  have byteSize : bytes.length ≤ U := by dsimp only [U, listInitialBudget]; omega
  have leftSize : initialLeft.length ≤ U := by dsimp only [U, listInitialBudget]; omega
  have tickSize : ticks.length + 1 ≤ U := by dsimp only [U, listInitialBudget]; omega
  have tickSquare : (ticks.length + 2) ^ 2 ≤ (2 * U) ^ 2 :=
    Nat.pow_le_pow_left (by omega) 2
  have loop := Nat.mul_le_mul tickSize
    (Nat.add_le_add_right (Nat.mul_le_mul_left 512 tickSquare) 4)
  have counter : listCounterBudget word ticks ≤ 4096 * U ^ 3 := by
    calc
      listCounterBudget word ticks ≤ U + 2 + U * (512 * (2 * U) ^ 2 + 4) := by
        simp only [listCounterBudget, countCost, Nat.zero_add]
        omega
      _ = 2048 * U ^ 3 + 5 * U + 2 := by ring
      _ ≤ 4096 * U ^ 3 := by omega
  have work : listWorkBudget word bytes ticks initialLeft ≤ (4096 * C + 1) * U ^ 3 := by
    calc
      listWorkBudget word bytes ticks initialLeft ≤ U + C * (4096 * U ^ 3) :=
        Nat.add_le_add input (Nat.mul_le_mul_left C counter)
      _ ≤ U ^ 3 + C * (4096 * U ^ 3) := Nat.add_le_add_right selfCube _
      _ = (4096 * C + 1) * U ^ 3 := by ring
  calc
    listFinalBudget word bytes ticks initialLeft ≤
        U + 2 + 4096 * U ^ 3 + 2 * ((4096 * C + 1) * U ^ 3) + U + 4 * U + 20 := by
      dsimp only [listFinalBudget]
      omega
    _ = (8192 * C + 4098) * U ^ 3 + 6 * U + 22 := by ring
    _ ≤ (8192 * C + 4126) * U ^ 3 := by nlinarith
    _ ≤ (16384 * (C + 1)) * U ^ 3 := Nat.mul_le_mul_right _ (by omega)

theorem listSpaceBudget_cubic (word bytes ticks initialLeft : List Bool) :
    listSpaceBudget word bytes ticks initialLeft ≤
      listSpaceCoefficient * (listInitialBudget word bytes ticks initialLeft + 1) ^ 3 := by
  let U := listInitialBudget word bytes ticks initialLeft + 1
  let D := PDROC.BitVM.Common.sourcePushCap finalProgram Finset.univ
  have positive : 1 ≤ U := by dsimp only [U]; omega
  have square : U ≤ U ^ 2 := by
    simpa only [Nat.mul_one, ← pow_two] using Nat.mul_le_mul_left U positive
  have cube : U ^ 2 ≤ U ^ 3 := by
    nlinarith [Nat.mul_le_mul_left (U ^ 2) positive]
  have initial : listInitialBudget word bytes ticks initialLeft ≤ U ^ 3 := by
    have input : listInitialBudget word bytes ticks initialLeft ≤ U := by dsimp only [U]; omega
    exact input.trans (square.trans cube)
  have coefficient : 1 ≤ listTimeCoefficient := by dsimp only [listTimeCoefficient]; omega
  calc
    listSpaceBudget word bytes ticks initialLeft ≤
        U ^ 3 + D * (listTimeCoefficient * U ^ 3) :=
      Nat.add_le_add initial (Nat.mul_le_mul_left D (listFinalBudget_cubic word bytes ticks initialLeft))
    _ = (1 + D * listTimeCoefficient) * U ^ 3 := by ring
    _ ≤ (listTimeCoefficient * (D + 1)) * U ^ 3 := Nat.mul_le_mul_right _ (by nlinarith)

end PDROC.BitVM.Codec.OutputList
