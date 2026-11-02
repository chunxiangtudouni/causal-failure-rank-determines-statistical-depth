module

public import Structure.PA06_A19Prepare_AllQPositive087_Layout
public import Structure.PA06_A19Prepare_InitializedFront086_Word
public import Structure.PA06_A19Prepare_AfterParents085
public import Structure.PA06_A19Prepare_Completion060_CanonicalPrefix

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED same-clock positive raw front of the selected all-q
program. ONE initialized-front witness is extended through the compact
retention/sort/parent run and then the physical prebuild continuation.
No old raw-entry existential clock is selected a second time. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawIncidenceLaminarRAM RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PrepareAllQCode082 (program)
open PA06A19PrepareInitialUsed037 (Fetched)
open PA06A19PrepareRawHeader039Body (wordRun_add)

theorem fetched_mono {wordBits : Nat} (rom : PhysicalROM) (code : List PackingOp)
    (small large : Nat) (room : small ≤ large) (state : WordState wordBits)
    (fetched : Fetched small rom code state) : Fetched large rom code state := by
  obtain ⟨active, pc, op, decoded, access⟩ := fetched
  exact ⟨active, pc, op, decoded,
    PA06A19PrepareRawHeader039Body.packingAccess_mono rom small large room state op access⟩

theorem positive_front (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) :
    ∃ firstClock ≤ PA06A19PreparePreBuild044.clockBound q full,
      let after := packingRun (controllerInput q full used) program firstClock
        (natInitial.toWord (bits q full))
      PA06A19PreparePreBuild044.Data q full after ∧
        PA06A19PrepareStaticMetadata036.RawCardData q full
          (PA06A19PreparePreBuild044.controlBase q full)
          (PA06A19PrepareRuntimeHeader019.natView after) ∧
        after.pc.toNat = 5 * 1639 ∧ after.halted = false ∧
        ∀ count < firstClock, Fetched (allocation q full) (controllerInput q full used) program
          (packingRun (controllerInput q full used) program count (natInitial.toWord (bits q full))) := by
  let rom := controllerInput q full used
  let initial := natInitial.toWord (bits q full)
  have certificate := PA06A19PrepareAllQCode082.selected_certificate full.length q
  obtain ⟨frontClock, frontBound, frontPost⟩ :=
    PA06A19PrepareInitializedFront086.initialized_front q full used hq hl
  dsimp only at frontPost
  rcases frontPost with ⟨initialized, frontEq, _frontRefinement, frontPrefixes⟩
  let native := natRun (rawIncidenceROM q full) program frontClock natInitial
  have compactCall := PA06A19PrepareAfterGate081.after_gate_word q full used hq program
    retention ordering parents native initialized certificate.2 certificate.1
  obtain ⟨compactClock, compactBound, compactPost⟩ := compactCall
  dsimp only at compactPost
  rcases compactPost with ⟨_nativeParents, _inverse, _registers,
    wordParents, ordData, cardData, _compactRefinement, compactPrefixes⟩
  let atParents := packingRun rom program (frontClock + compactClock) initial
  have compactRun : atParents = packingRun rom program compactClock (native.toWord (bits q full)) := by
    change packingRun rom program (frontClock + compactClock) initial = _
    rw [wordRun_add, frontEq]
  have actualParents : PA06A19PrepareCompactParents035Entry.WordParents q full atParents := by
    rw [compactRun]
    exact wordParents
  have actualOrd : PA06A19PrepareCompactParents035Ord.OrdData q full atParents := by
    rw [compactRun]
    exact ordData
  have actualCards : PA06A19PrepareCompactParents035Cards.CardData q full atParents := by
    rw [compactRun]
    exact cardData
  have parentBound : frontClock + compactClock ≤
      PA06A19PrepareCompactCandidates007.parentClockBound q full :=
    (Nat.add_le_add_left compactBound frontClock).trans
      (PA06A19PrepareAfterGate081.add_front_clock_le q full frontClock frontBound)
  have parentPrefixes := PA06A19PrepareCompletion060Canonical.fetched_add (allocation q full) rom program
    initial frontClock compactClock frontPrefixes (by
      intro count hc
      rw [frontEq]
      exact fetched_mono rom program _ _
        (PA06A19PrepareRawHeader039Body.compact_room full.length q (treeSize q full) hq) _
        (compactPrefixes count hc).2.2)
  have prebuild := PA06A19PrepareAfterParents085.after_parents q full used hq hl atParents
    actualParents actualOrd actualCards
  dsimp only at prebuild
  rcases prebuild with ⟨data, _copiedCards, rawCards, _copiedOrd, pc, active, lastPrefixes⟩
  let lastClock := PA06A19PrepareAfterParents085.clock q full
  have totalBound := PA06A19PrepareAfterParents085.add_parent_clock_le q full
    (frontClock + compactClock) parentBound
  have allPrefixes := PA06A19PrepareCompletion060Canonical.fetched_add (allocation q full) rom program initial
    (frontClock + compactClock) lastClock parentPrefixes lastPrefixes
  have finalRun : packingRun rom program (frontClock + compactClock + lastClock) initial =
      packingRun rom program lastClock atParents :=
    wordRun_add rom program (frontClock + compactClock) lastClock initial
  refine ⟨frontClock + compactClock + lastClock, totalBound, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, allPrefixes⟩
  · rw [finalRun]
    exact data
  · rw [finalRun]
    exact rawCards
  · rw [finalRun]
    exact pc
  · rw [finalRun]
    exact active

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAllQPositive087
