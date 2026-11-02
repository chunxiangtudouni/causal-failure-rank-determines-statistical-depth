module

public import Structure.PA06_A19Prepare_AllQPositive087_Run
public import Structure.PA06_A19Prepare_AllQPositive087_Budget
public import Structure.PA06_A19Prepare_PositiveSkip088
public import Structure.PA06_A19Prepare_Footprint054
public import Structure.PA06_A19Prepare_Access_004

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED complete positive branch of the ONE fixed all-q program.
The actual body, real three-instruction skip and global terminal HALT share
one original zero-heap run. Whole code, allocation and all dynamic events
are charged. There is no extra code/safety/data premise in this theorem. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawIncidenceLaminarRAM RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PrepareAllQCode082 (program)
open PA06A19PrepareRawHeader039Body (wordRun_add)

private theorem initial_zero_eq (width : Nat) :
    natInitial.toWord width = packingInitial (fun _ => BitVec.ofNat width 0) := rfl

theorem positive_complete (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ steps,
      DynamicRunCorrect (allocation q full) (controllerInput q full used) program steps
        (fun _ => BitVec.ofNat (bits q full) 0) ∧
      totalCost (allocation q full) (controllerInput q full used) program steps
        (fun _ => BitVec.ofNat (bits q full) 0) ≤
          costFactor * preprocessingWork full.length q (treeSize q full) ∧
      HeapRepresents q full (capacity q full) ⟨0, used, false⟩
        (packingRun (controllerInput q full used) program steps
          (packingInitial (fun _ => BitVec.ofNat (bits q full) 0))).heap := by
  let rom := controllerInput q full used
  let initial := packingInitial (fun _ => BitVec.ofNat (bits q full) 0)
  have certificate := PA06A19PrepareAllQCode082.selected_certificate full.length q
  obtain ⟨firstClock, firstBound, builderClock, builderBound, metadataClock, metadataBound, post⟩ :=
    positive_body q full used hq hl
  dsimp only at post
  simp only [initial_zero_eq (bits q full)] at post
  rcases post with ⟨represents, active, pc, bodyPrefixes⟩
  let bodyClock := firstClock + builderClock +
    (metadataClock + PA06A19PrepareInitialUsed037.clock q + 24)
  let bodyState := packingRun rom program bodyClock initial
  have skip := PA06A19PreparePositiveSkip088.actual_skip q full used bodyState pc active
  dsimp only at skip
  rcases skip with ⟨skipPC, skipActive, skipHeap, skipPrefixes, _skipTrace⟩
  have skipRun : packingRun rom program (bodyClock + 3) initial =
      packingRun rom program 3 bodyState := wordRun_add rom program bodyClock 3 initial
  have endPC : (packingRun rom program (bodyClock + 3) initial).pc.toNat = 5 * program.length := by
    rw [skipRun]
    exact skipPC
  have endActive : (packingRun rom program (bodyClock + 3) initial).halted = false := by
    rw [skipRun]
    exact skipActive
  have fetched := PA06A19PrepareCompletion060Canonical.fetched_add (allocation q full) rom program initial
    bodyClock 3 bodyPrefixes skipPrefixes
  have completed := PA06A19PrepareCompletion060Canonical.fetched_halt (allocation q full) rom program initial
    (bodyClock + 3) fetched certificate.1 certificate.2 endPC endActive
  have represented : HeapRepresents q full (capacity q full) ⟨0, used, false⟩
      (packingRun rom program (bodyClock + 3 + 1) initial).heap := by
    rw [completed.2.1, skipRun, skipHeap]
    exact represents
  have footprint : Fits (bits q full)
      (rom.size + allocation q full + (packingCode program).length) := by
    simpa only [PA06A19PrepareRawActive076.allocation_eq_cost] using
      PA06A19PrepareFootprint054.original_footprint_fits q full used program hq
        PA06A19PrepareAllQCode082.encoded_length_le32
  have stepBound := raw_steps_le q full hq firstClock builderClock metadataClock
    firstBound builderBound metadataBound
  have cost := raw_cost_le q full used hq (bodyClock + 3 + 1) stepBound
  refine ⟨bodyClock + 3 + 1, ?_, cost, ?_⟩
  · refine ⟨certificate.1,
      PA06A19PrepareAccess004.controllerInput_wordsFit 32 q full used (by decide), footprint, ?_, ?_⟩
    · exact completed.2.2.1
    · exact completed.2.2.2
  · exact represented

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087
