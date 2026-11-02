module

public import Structure.PA06_A19Prepare_AllQZero083_Run
public import Structure.PA06_A19Prepare_AllQPositive087_Complete

set_option autoImplicit false
set_option warningAsError true

/-! Original raw existential at the pre-mixed ABI boundary. Only the
original wordBits/capacity/allocatedWords abbreviations are expanded.
The ONE constant and program precede every q/full/used. This module
does not import the private PSTR141 ancestry or change the machine model. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQFinal089Expanded

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

private def preprocessingConstant : Nat :=
  max (PA06A19PrepareAllQZero083.costFactor PA06A19PrepareAllQCode082.program)
    PA06A19PrepareAllQPositive087.costFactor

/-- Exact original raw obligation with only its three layout aliases
expanded. No PA06 or PA17 implementation name occurs in the public type. -/
theorem fixed_raw_implementation :
    ∃ (constant : Nat) (code : List PackingOp), 0 < constant ∧
      ∀ (q : Nat) (full : List (Finset (Fin q))), LaminarSchedule full →
        ∀ used : Finset (Fin q), ∃ steps : Nat,
          DynamicRunCorrect
            (4 + packedCapacityWords q
              (capacityWords 8192 full.length q (treeSize q full))
              (indexWidth 32 full.length q) +
              8192 * (full.length + q + treeSize q full + 1))
            (controllerInput q full used) code steps
            (fun _ => BitVec.ofNat (indexWidth 32 full.length q) 0) ∧
          totalCost
            (4 + packedCapacityWords q
              (capacityWords 8192 full.length q (treeSize q full))
              (indexWidth 32 full.length q) +
              8192 * (full.length + q + treeSize q full + 1))
            (controllerInput q full used) code steps
            (fun _ => BitVec.ofNat (indexWidth 32 full.length q) 0) ≤
              constant * preprocessingWork full.length q (treeSize q full) ∧
          HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full))
            ⟨0, used, false⟩
            (packingRun (controllerInput q full used) code steps
              (packingInitial (fun _ => BitVec.ofNat (indexWidth 32 full.length q) 0))).heap := by
  have zero_le : PA06A19PrepareAllQZero083.costFactor PA06A19PrepareAllQCode082.program ≤
      preprocessingConstant := Nat.le_max_left _ _
  have positive_le : PA06A19PrepareAllQPositive087.costFactor ≤
      preprocessingConstant := Nat.le_max_right _ _
  refine ⟨preprocessingConstant, PA06A19PrepareAllQCode082.program,
    (PA06A19PrepareAllQZero083.costFactor_pos _).trans_le zero_le, ?_⟩
  intro q full laminar used
  by_cases zero : q = 0
  · subst q
    obtain ⟨steps, dynamic, cost, represented⟩ :=
      PA06A19PrepareAllQZero083.zero_complete full used
    refine ⟨steps, dynamic, ?_, represented⟩
    change _ ≤ preprocessingConstant * (full.length + 1)
    exact cost.trans (Nat.mul_le_mul_right (full.length + 1) zero_le)
  · obtain ⟨steps, dynamic, cost, represented⟩ :=
      PA06A19PrepareAllQPositive087.positive_complete q full used (Nat.pos_of_ne_zero zero) laminar
    exact ⟨steps, dynamic,
      cost.trans (Nat.mul_le_mul_right (preprocessingWork full.length q (treeSize q full)) positive_le),
      represented⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQFinal089Expanded
