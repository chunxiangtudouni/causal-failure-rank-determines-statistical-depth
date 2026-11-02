module

public import Structure.PA06_A19Prepare_Footprint054
public import Structure.PA06_A19Prepare_PreBuild044_Layout

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED q0 room for the original all-input preparation. The selected
fixed code must discharge its STATIC size bound. This absorbs the real
8198 extra words even atN0/bits32, instead of using the insufficient bound
codeWords<=2^32 as if it gave total-footprint room. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

theorem zero_allocation_eq (full : List (Finset (Fin 0))) :
    PA06A19PreparePreBuild044.allocation 0 full = 8192 * (full.length + 1) + 4 := by
  have packed : packedCapacityWords 0 0 (indexWidth 32 full.length 0) = 0 :=
    Nat.eq_zero_of_le_zero
      (PA06A19PreparePackedCost049.actual_packedCapacityWords_le_capacity full.length 0 0)
  change 4 + packedCapacityWords 0 0 (indexWidth 32 full.length 0) +
      8192 * (full.length + 0 + 0 + 1) = 8192 * (full.length + 1) + 4
  rw [packed]
  omega

theorem zero_original_footprint_fits (full : List (Finset (Fin 0)))
    (used : Finset (Fin 0)) (code : List PackingOp)
    (staticSize : (packingCode code).length ≤ 2 ^ 29) :
    Fits (indexWidth 32 full.length 0)
      ((controllerInput 0 full used).size + PA06A19PreparePreBuild044.allocation 0 full +
        (packingCode code).length) := by
  let B := full.length + 2
  have base : 2 ≤ B := by dsimp only [B]; omega
  have lower : 64 ≤ B ^ 6 := by
    simpa only [show 2 ^ 6 = 64 from rfl] using Nat.pow_le_pow_left base 6
  have linear : B ≤ B ^ 6 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 1 ≤ B) (by decide : 1 ≤ 6)
  have codeBound : (packingCode code).length ≤ 8388608 * B ^ 6 := by omega
  have source : (controllerInput 0 full used).size = 2 := by
    rw [PA06A19PrepareEntry003.controllerInput_size]
    omega
  apply PA17PackingBounds043.polynomial_fits
  change (controllerInput 0 full used).size + PA06A19PreparePreBuild044.allocation 0 full +
    (packingCode code).length ≤ 16777216 * B ^ 6
  rw [source, zero_allocation_eq]
  have dimension : full.length + 1 ≤ B := by dsimp only [B]; omega
  have heapBound := Nat.mul_le_mul_left 8192 dimension
  omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079
