module

public import Structure.PA06_A19Prepare_PostDP055_Run
public import Structure.PSTR_BuildLower_BuilderFetched_161

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED same-clock consumer of the actual161 strong-builder ABI.
The ONE selected witness supplies both the original055 Data endpoint and
every fetched builder prefix. Consumers must await the provider's normal
frozen handoff before validating this candidate. No old source is changed. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStrongBuilder075

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open CompactControllerClaims

theorem allocated_eq_prebuild (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    PSTRBuildLower.PreparedLayout.allocated q full = PA06A19PreparePreBuild044.allocation q full := by
  have ht : treeSize q full = PSTRBuildLower.PreparedLayout.t q full := by
    simp only [treeSize, Nat.ne_of_gt hq, ite_false]
  change
    4 + packedCapacityWords q
        (capacityWords 8192 full.length q (PSTRBuildLower.PreparedLayout.t q full))
        (indexWidth 32 full.length q) +
        8192 * (full.length + q + 1 + PSTRBuildLower.PreparedLayout.t q full) =
      4 + packedCapacityWords q (capacityWords 8192 full.length q (treeSize q full))
        (indexWidth 32 full.length q) + 8192 * (full.length + q + treeSize q full + 1)
  simp only [ht]
  ring

theorem builder_run (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before : WordState (indexWidth 32 full.length q))
    (pre : PA06A19PreparePreBuild044.Data q full before)
    (raw : PA06A19PrepareStaticMetadata036.RawCardData q full
      (PA06A19PreparePreBuild044.controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView before))
    (left right : List PackingOp)
    (hpc : before.pc = BitVec.ofNat _ (5 * left.length)) (ha : before.halted = false)
    (hcode : WordsFit (indexWidth 32 full.length q)
      (packingCode (left ++ PSTRBuildLower.CounterInit.builderCode left.length ++ right)))
    (hpcfit : Fits (indexWidth 32 full.length q)
      (5 * (left ++ PSTRBuildLower.CounterInit.builderCode left.length ++ right).length)) :
    ∃ count ≤ PA06A19PreparePostDP055.builderClockBound q full,
      let code := left ++ PSTRBuildLower.CounterInit.builderCode left.length ++ right
      let after := packingRun (controllerInput q full used) code count before
      PA06A19PreparePostDP055.Data q full after ∧
        after.pc = BitVec.ofNat _
          (5 * (left.length + (PSTRBuildLower.CounterInit.builderCode left.length).length)) ∧
        after.halted = false ∧
        PSTRBuildLower.ResourceTrace.CacheFrame q full before.heap after.heap ∧
        ∀ clock < count, PA06A19PrepareInitialUsed037.Fetched (PA06A19PreparePreBuild044.allocation q full)
          (controllerInput q full used) code
          (packingRun (controllerInput q full used) code clock before) := by
  have entry := PA06A19PrepareSTInput050.st_input_of_data q full hq before pre
  obtain ⟨count, bound, post⟩ := PSTRBuildLower.BuilderFetchedRun.run q full used hq hl
    before entry.2.1 entry.1 entry.2.2 left right hpc ha hcode hpcfit
  dsimp only at post
  rcases post with ⟨source, runtime, pc, active, bounded, frame, prefixes⟩
  refine ⟨count, bound, ?_⟩
  dsimp only
  refine ⟨PA06A19PreparePostDP055.data_of_builder_outputs q full hq hl before _ pre raw
    source runtime bounded frame, pc, active, frame, ?_⟩
  simpa only [allocated_eq_prebuild q full hq] using prefixes

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStrongBuilder075
