module

public import Structure.PA06_A19Prepare_PreBuild044
public import Structure.PA06_A19Prepare_PreBuild046_CardsFrames
public import Structure.PA06_A19Prepare_RawCards047

set_option autoImplicit false
set_option warningAsError true

/-! Original raw controller input reaches one prebuild state with actual
cache/card/ordinal words. All data use one clock, transported through
actual144 children and51 clear/VM. Candidate, not yet compiled. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuildCards048
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims
open PA06A19PrepareRawHeader039Body (wordRun_add)
open PA06A19PreparePreBuild044

theorem raw_prebuild_cards_entry (q : Nat) (full : List (Finset (Fin q)))
    (tail : List PackingOp) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (hend : Fits (bits q full) (5 * (program tail).length))
    (hcode : WordsFit (bits q full) (packingCode (program tail))) :
    ∃ clock ≤ clockBound q full,
      let rom := controllerInput q full used
      let after := packingRun rom (program tail) clock (natInitial.toWord (bits q full))
      Data q full after ∧ PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) after ∧
        PA06A19PrepareStaticMetadata036.RawCardData q full (controlBase q full)
          (PA06A19PrepareRuntimeHeader019.natView after) ∧ after.pc.toNat = 5 * 1639 ∧ after.halted = false ∧
        ∀ count < clock,
          let current := packingRun rom (program tail) count (natInitial.toWord (bits q full))
          current.halted = false ∧ current.pc.toNat + 4 < (packingCode (program tail)).length ∧
            ∃ op, PackingOp.decode (fetch (program tail) current) = some op ∧
              packingAccessFits rom (allocation q full) current op := by
  let rom := controllerInput q full used
  let initial := natInitial.toWord (bits q full)
  let cacheClock := PA06A19PrepareChildrenCache023.totalSteps q full
  let clearClock := PA06A19PrepareClearVM045.clock full.length q (treeSize q full)
  obtain ⟨rawClock, rawBound, rawData⟩ :=
    PA06A19PrepareRawCards047.raw_sequence_cards_entry q full (suffix tail) used hq hl hend hcode
  dsimp only at rawData
  rcases rawData with ⟨rawHeader, bank032, bank037, cell3, cell6, cacheInput,
    copiedOrd, copiedCards, rawPC, rawActive, rawSafe⟩
  let raw := packingRun rom (program tail) rawClock initial
  let cached := packingRun rom (program tail) (rawClock + cacheClock) initial
  have cacheRun : cached = packingRun rom (program tail) cacheClock raw := by
    exact wordRun_add rom (program tail) rawClock cacheClock initial
  have cacheResult := cache_stage q full used hq hl tail raw rawPC rawActive rawHeader
    ⟨bank032, bank037, cell3, cell6⟩ copiedOrd cacheInput hcode hend
  dsimp only at cacheResult
  have cachedData : CachedData q full cached := by rw [cacheRun]; exact cacheResult.1
  have cachedPC : cached.pc.toNat = 5 * 1588 := by rw [cacheRun]; exact cacheResult.2.1
  have cachedActive : cached.halted = false := by rw [cacheRun]; exact cacheResult.2.2.1
  have cacheCards := PA06A19PreparePreBuild046CardsFrames.cache_copied_cards q full used hq hl tail
    raw rawPC rawActive cacheInput copiedCards hcode hend
  have cachedCards : PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) cached := by
    rw [cacheRun]
    exact cacheCards
  have clearCards := PA06A19PreparePreBuild046CardsFrames.clear_copied_cards q full used hq tail
    cached cachedPC cachedActive cachedData.scalars.bank032 cachedData.header cachedCards hcode hend
  have clearResult := clear_stage q full used hq hl tail cached cachedPC cachedActive cachedData hcode hend
  dsimp only at clearResult
  have finalRun : packingRun rom (program tail) (rawClock + cacheClock + clearClock) initial =
      packingRun rom (program tail) clearClock cached :=
    wordRun_add rom (program tail) (rawClock + cacheClock) clearClock initial
  rw [← finalRun] at clearResult clearCards
  refine ⟨rawClock + cacheClock + clearClock, ?_, ?_⟩
  · dsimp only [clockBound, cacheClock, clearClock]
    omega
  dsimp only
  refine ⟨clearResult.1, clearCards,
    PA06A19PrepareBankData042.rawCardData_of_copied_words q full _ _ clearCards
      clearResult.1.cached.copiedOrd,
    clearResult.2.1, clearResult.2.2.1, ?_⟩
  intro count hcount
  by_cases early : count < rawClock
  · exact rawSafe count early
  · by_cases middle : count < rawClock + cacheClock
    · have ht : count = rawClock + (count - rawClock) := by omega
      have hs := cacheResult.2.2.2 (count - rawClock) (by omega)
      have hr : packingRun rom (program tail) count initial =
          packingRun rom (program tail) (count - rawClock) raw := by
        calc
          _ = packingRun rom (program tail) (rawClock + (count - rawClock)) initial :=
            congrArg (fun k => packingRun rom (program tail) k initial) ht
          _ = _ := wordRun_add rom (program tail) rawClock (count - rawClock) initial
      rw [← hr] at hs
      exact hs
    · have ht : count = rawClock + cacheClock + (count - (rawClock + cacheClock)) := by omega
      have hs := clearResult.2.2.2 (count - (rawClock + cacheClock)) (by omega)
      have hr : packingRun rom (program tail) count initial =
          packingRun rom (program tail) (count - (rawClock + cacheClock)) cached := by
        calc
          _ = packingRun rom (program tail)
              (rawClock + cacheClock + (count - (rawClock + cacheClock))) initial :=
            congrArg (fun k => packingRun rom (program tail) k initial) ht
          _ = _ := wordRun_add rom (program tail) (rawClock + cacheClock)
            (count - (rawClock + cacheClock)) initial
      rw [← hr] at hs
      exact hs


end PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuildCards048
