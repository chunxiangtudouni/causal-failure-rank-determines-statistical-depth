module

public import Structure.PA06_A19Prepare_RawActive076_Run
public import Structure.PA06_A19Prepare_StepBudget053

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED real charged prefix of the chosen containing program.
The arbitrary fixed tail has not run. Its encoded loading is nevertheless
included in original totalCost; the constants precede all input instances.
This is an internal positive component, not an all-q implementation claim. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRawActive076

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims RawIncidenceLaminarRAM
open PA06A19PreparePreBuild044 (bits capacity allocation)
open PA06A19PrepareInitialUsed037 (Fetched)

def fixedFactor : Nat := PSTRBuildLower.ASTBudget.factor PA17ProgramTemplates041.fullBuild

def stepFactor : Nat := PA06A19PrepareStepBudget053.stepFactor fixedFactor

def costFactor (right : List PackingOp) : Nat :=
  12 * stepFactor + 32792 + (packingCode (program right)).length

private theorem body_steps_le_complete (first builder metadata used : Nat) :
    first + builder + (metadata + used + 24) ≤
      first + builder + metadata + used + 24 + 1 := by omega

theorem raw_steps_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (firstClock builderClock metadataClock : Nat)
    (firstBound : firstClock ≤ PA06A19PreparePreBuild044.clockBound q full)
    (builderBound : builderClock ≤ PA06A19PreparePostDP055.builderClockBound q full)
    (metadataBound : metadataClock ≤ PA06A19PrepareStaticMetadata036.metadataNatBound full.length q
      (PA06A19PrepareChildrenCache023.preparedSize q full)) :
    firstClock + builderClock + (metadataClock + PA06A19PrepareInitialUsed037.clock q + 24) ≤
      stepFactor * preprocessingWork full.length q (treeSize q full) := by
  have ht : treeSize q full = PSTRBuildLower.PreparedLayout.t q full := by
    simp only [treeSize, Nat.ne_of_gt hq, ite_false]
  have build : builderClock ≤ 64 + (32768 * fixedFactor) * work full.length q (treeSize q full) := by
    have bound := builderBound
    change builderClock ≤ 64 + (fixedFactor * 32768) *
      work full.length q (PSTRBuildLower.PreparedLayout.t q full) at bound
    rw [← ht, Nat.mul_comm fixedFactor 32768] at bound
    exact bound
  have metadata := PA06A19PrepareStaticMetadata036.metadata_steps_treeWork q full hq metadataClock metadataBound
  have complete := PA06A19PrepareStepBudget053.preparation_steps_le q full hq fixedFactor
    firstClock builderClock metadataClock firstBound build metadata
  exact (body_steps_le_complete firstClock builderClock metadataClock
    (PA06A19PrepareInitialUsed037.clock q)).trans complete

theorem allocation_eq_cost (q : Nat) (full : List (Finset (Fin q))) :
    allocation q full = PA06A19PrepareControlBank017.allocation full.length q (treeSize q full)
      (packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full)) (bits q full)) := by
  have dimensionEq : full.length + q + treeSize q full + 1 = full.length + q + 1 + treeSize q full := by omega
  simp only [allocation, PA06A19PrepareRuntimeHeader019.heapWords,
    PA06A19PrepareControlBank017.allocation, PA06A19PrepareControlBank017.dimensions,
    PA06A19PrepareControlBank017.mass, bits, dimensionEq]

theorem raw_cost_le (right : List PackingOp) (q : Nat)
    (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (steps : Nat)
    (bound : steps ≤ stepFactor * preprocessingWork full.length q (treeSize q full)) :
    totalCost (allocation q full) (controllerInput q full used) (program right) steps
      (fun _ => BitVec.ofNat (bits q full) 0) ≤
        costFactor right * preprocessingWork full.length q (treeSize q full) := by
  have cost := PA06A19PrepareCostBudget051.totalCost_le_of_steps q full used (program right)
    steps stepFactor (fun _ => BitVec.ofNat (bits q full) 0) hq bound
  simpa only [allocation_eq_cost, costFactor] using cost

theorem raw_active_with_cost (right : List PackingOp) (q : Nat)
    (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (hcode : WordsFit (bits q full) (packingCode (program right)))
    (hcodePC : Fits (bits q full) (5 * (program right).length)) :
    ∃ firstClock ≤ PA06A19PreparePreBuild044.clockBound q full,
    ∃ builderClock ≤ PA06A19PreparePostDP055.builderClockBound q full,
    ∃ metadataClock ≤ PA06A19PrepareStaticMetadata036.metadataNatBound full.length q
        (PA06A19PrepareChildrenCache023.preparedSize q full),
      let total := firstClock + builderClock +
        (metadataClock + PA06A19PrepareInitialUsed037.clock q + 24)
      let rom := controllerInput q full used
      let after := packingRun rom (program right) total (natInitial.toWord (bits q full))
      HeapRepresents q full (capacity q full) ⟨0, used, false⟩ after.heap ∧
      after.halted = false ∧ after.pc.toNat = 5 * (builderEnd + 691) ∧
      (∀ count < total, Fetched (allocation q full) rom (program right)
        (packingRun rom (program right) count (natInitial.toWord (bits q full)))) ∧
      total ≤ stepFactor * preprocessingWork full.length q (treeSize q full) ∧
      totalCost (allocation q full) rom (program right) total
        (fun _ => BitVec.ofNat (bits q full) 0) ≤
          costFactor right * preprocessingWork full.length q (treeSize q full) := by
  obtain ⟨firstClock, firstBound, builderClock, builderBound, metadataClock, metadataBound, post⟩ :=
    raw_active right q full used hq hl hcode hcodePC
  dsimp only at post
  rcases post with ⟨represents, active, exitPC, prefixes⟩
  have steps := raw_steps_le q full hq firstClock builderClock metadataClock firstBound builderBound metadataBound
  have cost := raw_cost_le right q full used hq _ steps
  refine ⟨firstClock, firstBound, builderClock, builderBound, metadataClock, metadataBound, ?_⟩
  dsimp only
  exact ⟨represents, active, exitPC, prefixes, steps, cost⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRawActive076
