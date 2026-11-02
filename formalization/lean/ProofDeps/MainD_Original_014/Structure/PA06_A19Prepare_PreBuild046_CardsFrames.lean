module

public import Structure.PA06_A19Prepare_PreBuild044_Frames
public import Structure.PA06_A19Prepare_BankData042_Cards

set_option autoImplicit false
set_option warningAsError true

/-! Only the existing physical mass/card words are transported through
the actual children and clear/VM segments. Each segment uses the original
containing program, incoming state and clock. No raw-entry assembly or
new data type is introduced. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuild046CardsFrames

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM CompactControllerClaims
open PA06A19PreparePreBuild044 (bits controlBase program cache_code children_controlBase
  high_cell_fits clearFront clearFront_length clear_layout)
open PA06A19PrepareBankData042 (CopiedCardData)

/-- The actual 023 frame at precisely the copied mass and card words.
The input representation is the existing earlier producer's output; the
Protected frame itself is obtained from this same code/state execution. -/
theorem cache_copied_cards (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full) (tail : List PackingOp)
    (before : WordState (bits q full))
    (hpc : before.pc.toNat = 5 * 1444) (ha : before.halted = false)
    (hinput : PA06A19PrepareChildrenCache023.InputData q full (controlBase q full)
      (PA06A19PrepareRuntimeHeader019.natView before))
    (cards : CopiedCardData q full (controlBase q full) before)
    (hcode : WordsFit (bits q full) (packingCode (program tail)))
    (hend : Fits (bits q full) (5 * (program tail).length)) :
    CopiedCardData q full (controlBase q full)
      (packingRun (controllerInput q full used) (program tail)
        (PA06A19PrepareChildrenCache023.totalSteps q full) before) := by
  have hi : PA06A19PrepareChildrenCache023.InputData q full
      (PA06A19PrepareChildrenCache023.actualControlBase q full)
      (PA06A19PrepareChildrenCache023.wordView before) := by
    rw [children_controlBase q full hq]
    exact hinput
  have built := PA06A19PrepareChildrenCache023.word_build q full hq hl
    (controllerInput q full used) (program tail) 1444 (cache_code tail)
    before hi hpc ha hcode hend
  dsimp only at built
  rcases built with ⟨_output, _address, _pc, _active, frame, _safe, _steps⟩
  rw [children_controlBase q full hq] at frame
  constructor
  · have fit : Fits (bits q full) (controlBase q full + 528) :=
      high_cell_fits q full hq _ (by
        unfold PA06A19PrepareChildrenCache023.highCacheEnd
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

/-- The actual 045 permanent frame preserves the same finite mass/card
words, all beyond CB+39. BankData and Header are the preceding real stage's
outputs, rather than new qualifications on the original raw input. -/
theorem clear_copied_cards (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (tail : List PackingOp) (before : WordState (bits q full))
    (hpc : before.pc.toNat = 5 * 1588) (ha : before.halted = false)
    (bank : PA06A19PrepareFiniteInit032.BankData q full before)
    (header : PA06A19PrepareRuntimePacked016.Header q before.heap)
    (cards : CopiedCardData q full (controlBase q full) before)
    (hcode : WordsFit (bits q full) (packingCode (program tail)))
    (hend : Fits (bits q full) (5 * (program tail).length)) :
    CopiedCardData q full (controlBase q full)
      (packingRun (controllerInput q full used) (program tail)
        (PA06A19PrepareClearVM045.clock full.length q (treeSize q full)) before) := by
  have hp : before.pc.toNat = 5 * (clearFront tail).length := by
    rw [clearFront_length]
    exact hpc
  have hc : WordsFit (bits q full)
      (packingCode (clearFront tail ++ PA06A19PrepareClearVM045.programAt (clearFront tail).length ++ tail)) := by
    rw [clear_layout]
    exact hcode
  have he : Fits (bits q full)
      (5 * (clearFront tail ++ PA06A19PrepareClearVM045.programAt (clearFront tail).length ++ tail).length) := by
    rw [clear_layout]
    exact hend
  constructor
  · have fit : Fits (bits q full) (controlBase q full + 528) :=
      high_cell_fits q full hq _ (by
        unfold PA06A19PrepareChildrenCache023.highCacheEnd
        omega)
    have permanent := PA06A19PrepareClearVM045.actual_permanent_frame q full used hq
      (clearFront tail) tail before hp ha bank hc he header
      (BitVec.ofNat (bits q full) (controlBase q full + 528)) (by
        change (controlBase q full ≤ (BitVec.ofNat (bits q full) (controlBase q full + 528)).toNat ∧
          (BitVec.ofNat (bits q full) (controlBase q full + 528)).toNat < controlBase q full + 32) ∨
            controlBase q full + 39 ≤ (BitVec.ofNat (bits q full) (controlBase q full + 528)).toNat
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
        exact Or.inr (by omega))
    rw [clear_layout] at permanent
    rw [permanent]
    exact cards.mass_cell
  · intro candidate
    let address := controlBase q full + 512 +
      PA06A19PrepareCompactParents035Cards.cardSlot full.length q candidate.val
    have candidateBound := candidate.isLt
    have fit : Fits (bits q full) address := high_cell_fits q full hq _ (by
      unfold address PA06A19PrepareCompactParents035Cards.cardSlot RawCandidateOrderingRAM.arraySlot
        PA06A19PrepareChildrenCache023.highCacheEnd PA06A19PrepareChildrenCache023.mass
      omega)
    have permanent := PA06A19PrepareClearVM045.actual_permanent_frame q full used hq
      (clearFront tail) tail before hp ha bank hc he header (BitVec.ofNat (bits q full) address) (by
        change (controlBase q full ≤ (BitVec.ofNat (bits q full) address).toNat ∧
          (BitVec.ofNat (bits q full) address).toNat < controlBase q full + 32) ∨
            controlBase q full + 39 ≤ (BitVec.ofNat (bits q full) address).toNat
        rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt fit]
        apply Or.inr
        unfold address PA06A19PrepareCompactParents035Cards.cardSlot RawCandidateOrderingRAM.arraySlot
        omega)
    rw [clear_layout] at permanent
    rw [permanent]
    exact cards.cards candidate

end PaperProofs.Structure.LaminarTree.PA06A19PreparePreBuild046CardsFrames
