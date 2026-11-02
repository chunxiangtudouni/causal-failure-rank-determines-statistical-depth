module

public import Structure.PA06_A19Prepare_AfterParents085_Sequence

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual144-op cache on the fixed patched containing code.
The real Protected frame retains copied card/ordinal and bank words. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims
open PA06A19PreparePreBuild044 (CachedData children_controlBase children_allocation
  cache_retained_frames header_of_frame copiedOrd_of_frame high_cell_fits)

private theorem cache_stage_local (whole : List PackingOp)
    (codeAt : PA06A19PrepareChildrenCache023.CodeAt whole 1444) (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before : WordState (bits q full))
    (hpc : before.pc.toNat = 5 * 1444) (ha : before.halted = false)
    (hheader : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hscalars : PA06A19PreparePreBuild044.ScalarData q full before)
    (hord : PA06A19PrepareBankData042.CopiedOrdData q full (controlBase q full) before)
    (hinput : PA06A19PrepareChildrenCache023.InputData q full (controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView before))
    (cards : PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) before)
    (certificate : WordsFit (bits q full) (packingCode whole) ∧ Fits (bits q full) (5 * whole.length)) :
    let after := packingRun (controllerInput q full used) whole
      (PA06A19PrepareChildrenCache023.totalSteps q full) before
    CachedData q full after ∧
      PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) after ∧ after.pc.toNat = 5 * 1588 ∧ after.halted = false ∧
      (∀ count < PA06A19PrepareChildrenCache023.totalSteps q full,
        PA06A19PrepareInitialUsed037.Fetched (allocation q full) (controllerInput q full used) whole
          (packingRun (controllerInput q full used) whole count before)) := by
  have hi : PA06A19PrepareChildrenCache023.InputData q full
      (PA06A19PrepareChildrenCache023.actualControlBase q full)
      (PA06A19PrepareChildrenCache023.wordView before) := by
    rw [children_controlBase q full hq]
    exact hinput
  have built := PA06A19PrepareChildrenCache023.word_build q full hq hl
    (controllerInput q full used) whole 1444 codeAt
    before hi hpc ha certificate.1 certificate.2
  dsimp only at built
  rcases built with ⟨output, address, pc, active, frame, safe, _stepsBound⟩
  rw [children_controlBase q full hq] at output frame
  have frames := cache_retained_frames q full hq before _ frame
  have newCards : PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full)
      (packingRun (controllerInput q full used) whole (PA06A19PrepareChildrenCache023.totalSteps q full) before) := by
    constructor
    · have fit : Fits (bits q full) (controlBase q full + 528) :=
        high_cell_fits q full hq _ (by
          unfold PA06A19PrepareChildrenCache023.highCacheEnd
          dsimp only [PA06A19PrepareAfterParents085.controlBase, PA06A19PreparePreBuild044.controlBase]
          omega)
      have hprotected : PA06A19PrepareChildrenCache023.Protected q full (controlBase q full)
          (BitVec.ofNat (bits q full) (controlBase q full + 528)).toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
        unfold PA06A19PrepareChildrenCache023.Protected PA06A19PrepareChildrenCache023.degreeBase
        exact ⟨Or.inr (by omega), Or.inl (by omega)⟩
      rw [frame _ hprotected]
      exact cards.mass_cell
    · intro candidate
      let address := controlBase q full + 512 +
        PA06A19PrepareCompactParents035Cards.cardSlot full.length q candidate.val
      have candidateBound := candidate.isLt
      have fit : Fits (bits q full) address := high_cell_fits q full hq _ (by
        unfold address PA06A19PrepareCompactParents035Cards.cardSlot RawCandidateOrderingRAM.arraySlot
          PA06A19PrepareChildrenCache023.highCacheEnd PA06A19PrepareChildrenCache023.mass
        dsimp only [PA06A19PrepareAfterParents085.controlBase, PA06A19PreparePreBuild044.controlBase]
        omega)
      have hprotected : PA06A19PrepareChildrenCache023.Protected q full (controlBase q full)
          (BitVec.ofNat (bits q full) address).toNat := by
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
        unfold PA06A19PrepareChildrenCache023.Protected PA06A19PrepareChildrenCache023.degreeBase
          PA06A19PrepareChildrenCache023.mass address PA06A19PrepareCompactParents035Cards.cardSlot
          RawCandidateOrderingRAM.arraySlot
        exact ⟨Or.inr (by omega), Or.inl (by omega)⟩
      rw [frame _ hprotected]
      exact cards.cards candidate
  refine ⟨⟨header_of_frame hheader frames.2.2,
    hscalars.of_frame address frames.1, copiedOrd_of_frame hord frames.2.1, output⟩,
    newCards, pc, active, ?_⟩
  intro count hc
  have hs := safe count hc
  rw [children_allocation q full hq] at hs
  exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2⟩


theorem cache_stage (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before : WordState (bits q full))
    (hpc : before.pc.toNat = 5 * 1444) (ha : before.halted = false)
    (hheader : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (hscalars : PA06A19PreparePreBuild044.ScalarData q full before)
    (hord : PA06A19PrepareBankData042.CopiedOrdData q full (controlBase q full) before)
    (hinput : PA06A19PrepareChildrenCache023.InputData q full (controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView before))
    (cards : PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) before) :
    let after := packingRun (controllerInput q full used) program
      (PA06A19PrepareChildrenCache023.totalSteps q full) before
    CachedData q full after ∧
      PA06A19PrepareBankData042.CopiedCardData q full (controlBase q full) after ∧ after.pc.toNat = 5 * 1588 ∧ after.halted = false ∧
      Safe q full used before (PA06A19PrepareChildrenCache023.totalSteps q full) := by
  simpa only [Safe] using
    (cache_stage_local PA06A19PrepareAllQCode082.program cache_code q full used hq hl
      before hpc ha hheader hscalars hord hinput cards
      (PA06A19PrepareAllQCode082.selected_certificate full.length q))

end PaperProofs.Structure.LaminarTree.PA06A19PrepareAfterParents085
