module

public import Structure.PA06_A19Prepare_RawActive076_Budget
public import Structure.PA06_A19Prepare_AllQCode082

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED fixed all-q-program charge for its positive branch.
The real skip3 and global HALT1 are added to the actual076 body budget.
No run or correctness result is assumed by these scalar inequalities. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims

def stepFactor : Nat := PA06A19PrepareRawActive076.stepFactor + 4

def costFactor : Nat :=
  12 * stepFactor + 32792 + (5 * PA06A19PrepareAllQCode082.finalEnd + 5)

private theorem cost_factor_pos_local (factor codeLength : Nat) :
    0 < 12 * factor + 32792 + codeLength := by omega

theorem costFactor_pos : 0 < costFactor :=
  cost_factor_pos_local stepFactor (5 * PA06A19PrepareAllQCode082.finalEnd + 5)

theorem raw_steps_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (firstClock builderClock metadataClock : Nat)
    (firstBound : firstClock ≤ PA06A19PreparePreBuild044.clockBound q full)
    (builderBound : builderClock ≤ PA06A19PreparePostDP055.builderClockBound q full)
    (metadataBound : metadataClock ≤ PA06A19PrepareStaticMetadata036.metadataNatBound full.length q
      (PA06A19PrepareChildrenCache023.preparedSize q full)) :
    firstClock + builderClock + (metadataClock + PA06A19PrepareInitialUsed037.clock q + 24) + 3 + 1 ≤
      stepFactor * preprocessingWork full.length q (treeSize q full) := by
  have body := PA06A19PrepareRawActive076.raw_steps_le q full hq firstClock builderClock metadataClock
    firstBound builderBound metadataBound
  have facts := PA06A19PrepareCostBudget051.work_facts full.length q (treeSize q full)
    (PA06A19PrepareControlBank017.treeSize_pos full hq)
  have positive : 1 ≤ preprocessingWork full.length q (treeSize q full) := by
    rw [preprocessingWork, ite_eq_right (Nat.ne_of_gt hq)]
    omega
  have extra : 4 ≤ 4 * preprocessingWork full.length q (treeSize q full) := by omega
  rw [stepFactor, Nat.add_mul]
  omega

private theorem raw_cost_le_local (code : List PackingOp) (factor codeLength : Nat)
    (lengthEq : (packingCode code).length = codeLength)
    (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (steps : Nat)
    (bound : steps ≤ factor * preprocessingWork full.length q (treeSize q full)) :
    totalCost (PA06A19PreparePreBuild044.allocation q full) (controllerInput q full used)
      code steps (fun _ => BitVec.ofNat (indexWidth 32 full.length q) 0) ≤
        (12 * factor + 32792 + codeLength) *
          preprocessingWork full.length q (treeSize q full) := by
  have cost := PA06A19PrepareCostBudget051.totalCost_le_of_steps q full used code steps factor
    (fun _ => BitVec.ofNat (indexWidth 32 full.length q) 0) hq bound
  rw [lengthEq] at cost
  simpa only [PA06A19PrepareRawActive076.allocation_eq_cost] using cost

theorem raw_cost_le (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (steps : Nat)
    (bound : steps ≤ stepFactor * preprocessingWork full.length q (treeSize q full)) :
    totalCost (PA06A19PreparePreBuild044.allocation q full) (controllerInput q full used)
      PA06A19PrepareAllQCode082.program steps
      (fun _ => BitVec.ofNat (indexWidth 32 full.length q) 0) ≤
        costFactor * preprocessingWork full.length q (treeSize q full) := by
  exact raw_cost_le_local PA06A19PrepareAllQCode082.program stepFactor
    (5 * PA06A19PrepareAllQCode082.finalEnd + 5)
    (by rw [packingCode_length, PA06A19PrepareAllQCode082.program_length])
    q full used hq steps bound

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087
