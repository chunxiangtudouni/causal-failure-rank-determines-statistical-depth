module

public import Structure.PA06_A19Prepare_PackedCost049
public import Structure.PA06_A19Prepare_Entry_003
public import Structure.PA06_A19Prepare_ControlBank017_Geometry
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true

/-! Original ROM + actual allocation + fixed encoded program fit together.
The sole static-code premise is to be discharged once for the selected
fixed program. This is word room, not actual execution or correctness.
Candidate until strict validation; no N>0 premise is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFootprint054

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine CompactControllerClaims

theorem original_footprint_fits (q : Nat) (full : List (Finset (Fin q)))
    (used : Finset (Fin q)) (program : List PackingOp) (hq : 0 < q)
    (hcodeSize : (packingCode program).length ≤ 2 ^ 32) :
    Fits (indexWidth 32 full.length q)
      ((controllerInput q full used).size +
        PA06A19PrepareControlBank017.allocation full.length q (treeSize q full)
          (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) +
        (packingCode program).length) := by
  let N := full.length
  let B := N + q + 2
  let t := treeSize q full
  let C := capacityWords 8192 N q t
  let P := packedCapacityWords q C (indexWidth 32 N q)
  have hb : 3 ≤ B := by dsimp only [B]; omega
  have hB6 : 1 ≤ B ^ 6 := Nat.one_le_pow 6 B (by omega)
  have hB : B ≤ B ^ 6 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ B) (by decide : 1 ≤ 6)
  have hB2 : B ^ 2 ≤ B ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hB3 : B ^ 3 ≤ B ^ 6 := Nat.pow_le_pow_right (by omega) (by decide)
  have hc : C ≤ 8194 * B ^ 3 := PA06A19PrepareControlBank017.common_capacity_bound full
  have hp : P ≤ C := PA06A19PreparePackedCost049.actual_packedCapacityWords_le_capacity N q t
  have ht : t + 1 ≤ B := PA06A19PrepareControlBank017.treeSize_bound full
  have dimensions : N + q + 1 + t ≤ 2 * B := by dsimp only [B]; omega
  have hspace := Nat.mul_le_mul_left 8192 dimensions
  have heapBound : PA06A19PrepareControlBank017.allocation N q t P ≤
      8194 * B ^ 3 + 16384 * B + 4 := by
    unfold PA06A19PrepareControlBank017.allocation PA06A19PrepareControlBank017.dimensions
      PA06A19PrepareControlBank017.mass
    omega
  have sourceSquare : N * q + q + 2 ≤ B ^ 2 := by
    dsimp only [B]
    nlinarith [Nat.zero_le (N * q), Nat.zero_le (N ^ 2), Nat.zero_le (q ^ 2)]
  have sourceBound : (controllerInput q full used).size ≤ B ^ 6 := by
    rw [PA06A19PrepareEntry003.controllerInput_size]
    exact sourceSquare.trans hB2
  have lower : 729 ≤ B ^ 6 := by
    simpa using Nat.pow_le_pow_left hb 6
  have codeBound : (packingCode program).length ≤ 6000000 * B ^ 6 := by omega
  apply PA17PackingBounds043.polynomial_fits
  change (controllerInput q full used).size +
    PA06A19PrepareControlBank017.allocation N q t P + (packingCode program).length ≤
      16777216 * B ^ 6
  omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFootprint054
