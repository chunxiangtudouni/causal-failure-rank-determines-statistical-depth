module

public import Structure.PA06_A19Prepare_AfterParents085_Clear

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED same-clock post-parent assembly for the ONE fixed all-q
program.  No old zero-start raw entry is called.  The supplied081 endpoint
is continued through Header104, Sequence134, Cache144 and ClearVM51. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims
open PA06A19PrepareRawHeader039Body (wordRun_add)

theorem add_parent_clock_le (q : Nat) (full : List (Finset (Fin q))) (parentClock : Nat)
    (bound : parentClock ≤ PA06A19PrepareCompactCandidates007.parentClockBound q full) :
    parentClock + clock q full ≤ PA06A19PreparePreBuild044.clockBound q full := by
  unfold clock PA06A19PreparePreBuild044.clockBound
  omega

/-- The three input representations are exactly the one081 physical
endpoint.  Every prebuild/card/ordinal target is produced by the actual
post-parent blocks in082.program.  Static full-code eligibility is
discharged internally by082.selected_certificate. -/
theorem after_parents (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (before : WordState (bits q full))
    (parents : PA06A19PrepareCompactParents035Entry.WordParents q full before)
    (ordinal : PA06A19PrepareCompactParents035Ord.OrdData q full before)
    (cards : PA06A19PrepareCompactParents035Cards.CardData q full before) :
    let after := packingRun (controllerInput q full used) program (clock q full) before
    PA06A19PreparePreBuild044.Data q full after ∧
      PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) after ∧
      PA06A19PrepareStaticMetadata036.RawCardData q full (controlBase q full)
        (PA06A19PrepareRuntimeHeader019.natView after) ∧
      PA06A19PrepareBankData042.CopiedOrdData q full (controlBase q full) after ∧
      after.pc.toNat = 5 * 1639 ∧ after.halted = false ∧ Safe q full used before (clock q full) := by
  let rom := controllerInput q full used
  let firstClock := PA06A19PrepareRawHeader039Body.headerClock full.length q +
    PA06A19PrepareRuntimeLayout026.sequenceClock full.length q
  let cacheClock := PA06A19PrepareChildrenCache023.totalSteps q full
  let clearClock := PA06A19PrepareClearVM045.clock full.length q (treeSize q full)
  let raw := packingRun rom program firstClock before
  let cached := packingRun rom program (firstClock + cacheClock) before
  have first := header_sequence q full used hq before parents ordinal cards
  dsimp only at first
  rcases first with ⟨relocated, rawPC, rawActive, firstSafe⟩
  have cacheResult := cache_stage q full used hq hl raw rawPC rawActive relocated.header
    relocated.scalars relocated.copiedOrd relocated.input relocated.copiedCards
  dsimp only at cacheResult
  have cacheRun : cached = packingRun rom program cacheClock raw :=
    wordRun_add rom program firstClock cacheClock before
  have cachedData : PA06A19PreparePreBuild044.CachedData q full cached := by
    rw [cacheRun]
    exact cacheResult.1
  have cachedCards : PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) cached := by
    rw [cacheRun]
    exact cacheResult.2.1
  have cachedPC : cached.pc.toNat = 5 * 1588 := by
    rw [cacheRun]
    exact cacheResult.2.2.1
  have cachedActive : cached.halted = false := by
    rw [cacheRun]
    exact cacheResult.2.2.2.1
  have last := clear_stage q full used hq hl cached cachedPC cachedActive cachedData cachedCards
  dsimp only at last
  have finalRun : packingRun rom program (clock q full) before =
      packingRun rom program clearClock cached := by
    change packingRun rom program (firstClock + cacheClock + clearClock) before = _
    exact wordRun_add rom program (firstClock + cacheClock) clearClock before
  have firstTwo : Safe q full used before (firstClock + cacheClock) :=
    firstSafe.add cacheResult.2.2.2.2
  have allSafe : Safe q full used before (clock q full) := firstTwo.add last.2.2.2.2
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, allSafe⟩
  · rw [finalRun]
    exact last.1
  · rw [finalRun]
    exact last.2.1
  · rw [finalRun]
    exact PA06A19PrepareBankData042.rawCardData_of_copied_words q full _ _ last.2.1
      last.1.cached.copiedOrd
  · rw [finalRun]
    exact last.1.cached.copiedOrd
  · rw [finalRun]
    exact last.2.2.1
  · rw [finalRun]
    exact last.2.2.2.1

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085
