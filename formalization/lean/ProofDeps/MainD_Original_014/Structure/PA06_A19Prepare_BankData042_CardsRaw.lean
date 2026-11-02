module

public import Structure.PA06_A19Prepare_BankData042_Cards
public import Structure.PA06_A19Prepare_BankData042_Ordinal
public import Structure.PA06_A19Prepare_StaticMetadata036_Fields

set_option autoImplicit false
set_option warningAsError true

/-! The actual high-cache words are the metadata producer's RawCardData.
NatView reads those same words at BitVec.ofNat addresses. No native heap
fit or target-table assumption is needed to recover their exact values. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA06A19PrepareRuntimeLayout026
open PA06A19PrepareStaticMetadata036 (RawCardData rawCardAddress rawOrdAddress)
open PA06A19PrepareChildrenCache023 (mass)

/-- Combine the current physical card and ord words without inventing a
cardinality cache from support equality. The latter only interprets ord. -/
theorem rawCardData_of_copied_words (q : Nat) (full : List (Finset (Fin q))) (CB : Nat)
    (state : WordState (indexWidth 32 full.length q))
    (cards : CopiedCardData q full CB state) (ord : CopiedOrdData q full CB state) :
    RawCardData q full CB (PA06A19PrepareRuntimeHeader019.natView state) := by
  constructor
  · exact cards.mass_cell
  · intro candidate
    have address : rawCardAddress CB candidate.val = CB + 512 +
        PA06A19PrepareCompactParents035Cards.cardSlot full.length q candidate.val := by
      unfold rawCardAddress PA06A19PrepareCompactParents035Cards.cardSlot RawCandidateOrderingRAM.arraySlot
      omega
    change (state.heap (BitVec.ofNat _ (rawCardAddress CB candidate.val))).toNat = _
    rw [address]
    exact cards.cards candidate
  · intro node
    let source := PA06A19PrepareCompactParents035Ord.ordSlot full.length q node.val
    let value := (state.heap (BitVec.ofNat (indexWidth 32 full.length q) (CB + 512 + source))).toNat
    have ordinal : value ∈ RawCandidateOrder.retainedCandidateIndices q full ∧
        value < full.length + q + 1 ∧
        RawCandidateParents.candidateSupport q full value = (prepareNormalization q full).indexed.decode node :=
      ord node
    let candidate : Fin (mass q full) := ⟨value, ordinal.2.1⟩
    refine ⟨candidate, ?_, ordinal.2.2⟩
    have address : rawOrdAddress CB (mass q full) node.val = CB + 512 + source := by
      unfold rawOrdAddress source PA06A19PrepareCompactParents035Ord.ordSlot RawCandidateOrderingRAM.arraySlot mass
      omega
    change (state.heap (BitVec.ofNat _ (rawOrdAddress CB (mass q full) node.val))).toNat = value
    rw [address]

/-- Metadata's raw input record in the NatView of the actual 134-op result.
Both physical data certificates refer to this one reached Word state. -/
theorem embedded_raw_card_data (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (left right : List PackingOp) (state : WordState (indexWidth 32 full.length q))
    (cards : PA06A19PrepareCompactParents035Cards.CardData q full state)
    (ord : PA06A19PrepareCompactParents035Ord.OrdData q full state)
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
    RawCardData q full CB (PA06A19PrepareRuntimeHeader019.natView (packingRun (controllerInput q full used)
      (left ++ sequence left.length ++ right) (sequenceClock full.length q) state)) := by
  have copiedCards := embedded_copied_cards q full used hq left right state cards hpc ha hM ht hh hcode hend
  have copiedOrd := embedded_copied_ord q full used hq left right state ord hpc ha hM ht hh hcode hend
  dsimp only at copiedCards copiedOrd ⊢
  exact rawCardData_of_copied_words q full _ _ copiedCards copiedOrd

end PaperProofs.Structure.LaminarTree.PA06A19PrepareBankData042
