module
public import PaperProofs.Structure.CompactControllerClaims
public import PaperProofs.Structure.RawTreePreprocessingClaims
import Structure.PA06_A19Prepare_AllQFinal089_Expanded

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

public section
namespace RootL01.PHCompat.Preparation
open PaperProofs.Structure.LaminarTree
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

/-- The accepted, concrete, fixed all-q P program, behind its proof component boundary. -/
def program : List PackingOp := PA06A19PrepareAllQCode082.program

def constant : Nat :=
  max (PA06A19PrepareAllQZero083.costFactor PA06A19PrepareAllQCode082.program)
    PA06A19PrepareAllQPositive087.costFactor

theorem constant_pos : 0 < constant :=
  (PA06A19PrepareAllQZero083.costFactor_pos _).trans_le (Nat.le_max_left _ _)

theorem actual (q : Nat) (full : List (Finset (Fin q))) (laminar : LaminarSchedule full)
    (used : Finset (Fin q)) :
    ∃ steps : Nat,
      DynamicRunCorrect
        (4 + packedCapacityWords q
          (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q) +
          8192 * (full.length + q + treeSize q full + 1))
        (controllerInput q full used) program steps
        (fun _ => BitVec.ofNat (indexWidth 32 full.length q) 0) ∧
      totalCost
        (4 + packedCapacityWords q
          (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q) +
          8192 * (full.length + q + treeSize q full + 1))
        (controllerInput q full used) program steps
        (fun _ => BitVec.ofNat (indexWidth 32 full.length q) 0) ≤
          constant * preprocessingWork full.length q (treeSize q full) ∧
      HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full))
        ⟨0, used, false⟩
        (packingRun (controllerInput q full used) program steps
          (packingInitial (fun _ => BitVec.ofNat (indexWidth 32 full.length q) 0))).heap := by
  have zero_le : PA06A19PrepareAllQZero083.costFactor PA06A19PrepareAllQCode082.program ≤
      constant := Nat.le_max_left _ _
  have positive_le : PA06A19PrepareAllQPositive087.costFactor ≤ constant := Nat.le_max_right _ _
  by_cases zero : q = 0
  · subst q
    obtain ⟨steps, dynamic, cost, represented⟩ := PA06A19PrepareAllQZero083.zero_complete full used
    refine ⟨steps, dynamic, ?_, represented⟩
    change _ ≤ constant * (full.length + 1)
    exact cost.trans (Nat.mul_le_mul_right (full.length + 1) zero_le)
  · obtain ⟨steps, dynamic, cost, represented⟩ :=
      PA06A19PrepareAllQPositive087.positive_complete q full used (Nat.pos_of_ne_zero zero) laminar
    exact ⟨steps, dynamic,
      cost.trans (Nat.mul_le_mul_right (preprocessingWork full.length q (treeSize q full)) positive_le),
      represented⟩

end RootL01.PHCompat.Preparation
