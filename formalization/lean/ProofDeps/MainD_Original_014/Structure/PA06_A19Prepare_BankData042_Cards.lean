module

public import Structure.PA06_A19Prepare_BankData042_CacheInput
public import Structure.PA06_A19Prepare_CompactParents035Cards

set_option autoImplicit false
set_option warningAsError true

/-! Actual physical card words after the existing 134-op relocation.
Only the current physical mass/card words are described. Their producer
uses the actual copy theorem, including its true source interval. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA06A19PrepareRuntimeLayout026

structure CopiedCardData (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (state : WordState (indexWidth 32 full.length q)) : Prop where
  mass_cell : (state.heap (BitVec.ofNat _ (CB + 528))).toNat = full.length + q + 1
  cards : ∀ candidate : Fin (full.length + q + 1),
    (state.heap (BitVec.ofNat _ (CB + 512 +
      PA06A19PrepareCompactParents035Cards.cardSlot full.length q candidate.val))).toNat =
        RawCandidateStableOrder.candidateCard q full candidate.val

/-- Card and mass words in the reached physical heap of the same sequence.
The raw CardData is an earlier real producer output, not a prefilled target. -/
theorem embedded_copied_cards (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (cards : PA06A19PrepareCompactParents035Cards.CardData q full state)
    (hpc : state.pc.toNat = 5 * left.length) (ha : state.halted = false)
    (hM : (state.heap (BitVec.ofNat _ 16)).toNat = full.length + q + 1)
    (ht : (state.heap (BitVec.ofNat _ (20 + 4 * (full.length + q + 1)))).toNat = treeSize q full)
    (hh : PA06A19PrepareRuntimePacked016.Header q state.heap)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode (left ++ sequence left.length ++ right)))
    (hend : Fits (indexWidth 32 full.length q) (5 * (left ++ sequence left.length ++ right).length)) :
    let bits := indexWidth 32 full.length q
    let t := treeSize q full
    let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
    let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
    CopiedCardData q full CB (packingRun (controllerInput q full used)
      (left ++ sequence left.length ++ right) (sequenceClock full.length q) state) := by
  let bits := indexWidth 32 full.length q
  let t := treeSize q full
  let P := packedCapacityWords q (capacityWords 8192 full.length q t) bits
  let CB := PA06A19PrepareControlBank017.controlBase full.length q t P
  have copied (source : Nat) (h16 : 16 ≤ source)
      (hL : source < PA06A19PrepareControlBank017.cacheLength full.length q) :
      ((packingRun (controllerInput q full used) (left ++ sequence left.length ++ right)
        (sequenceClock full.length q) state).heap (BitVec.ofNat bits (CB + 512 + source))).toNat =
          (state.heap (BitVec.ofNat bits source)).toNat := by
    exact congrArg BitVec.toNat (embedded_sequence_copied_word q full used hq left right state
      hpc ha hM ht hh hcode hend source h16 hL)
  dsimp only
  constructor
  · have h := copied 16 (by decide) (by
      unfold PA06A19PrepareControlBank017.cacheLength
      omega)
    rw [show CB + 512 + 16 = CB + 528 by omega, hM] at h
    exact h
  · intro candidate
    let source := PA06A19PrepareCompactParents035Cards.cardSlot full.length q candidate.val
    have h16 : 16 ≤ source := by
      unfold source PA06A19PrepareCompactParents035Cards.cardSlot RawCandidateOrderingRAM.arraySlot
      omega
    have hL : source < PA06A19PrepareControlBank017.cacheLength full.length q := by
      have bound := PA06A19PrepareCompactCandidates007.candidate_array_address_lt
        full.length q 0 candidate.val (by decide) candidate.isLt
      exact bound
    exact (copied source h16 hL).trans (cards candidate)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042
