module

public import Structure.PA06_A19Prepare_CompactParents035Ord

set_option autoImplicit false
set_option warningAsError true

/-! Exact card words from the native InputTables of the same parent run.
The value bound is the actual candidate-support cardinality bound. No
arbitrary native heap value is assumed to fit, and no loop is reproved. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Cards

open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety

abbrev program := PA06A19PrepareCompactParents035Ord.program
abbrev linearLimit := PA06A19PrepareCompactWord008.linearLimit
abbrev ParentEntry := PA06A19PrepareCompactCandidates007.ParentEntry
abbrev WordParents := PA06A19PrepareCompactParents035Entry.WordParents
abbrev OrdData := PA06A19PrepareCompactParents035Ord.OrdData
abbrev ordSlot := PA06A19PrepareCompactParents035Ord.ordSlot

def cardSlot (N q candidate : Nat) : Nat :=
  RawCandidateOrderingRAM.arraySlot 16 (N + q + 1) 0 candidate

/-- Every original candidate has its real cardinality in physical array 0. -/
def CardData (q : Nat) (full : List (Finset (Fin q)))
    (state : WordState (indexWidth 32 full.length q)) : Prop :=
  ∀ candidate : Fin (full.length + q + 1),
    (state.heap (BitVec.ofNat _ (cardSlot full.length q candidate.val))).toNat =
      RawCandidateStableOrder.candidateCard q full candidate.val

theorem card_address_fits (q : Nat) (full : List (Finset (Fin q)))
    (candidate : Fin (full.length + q + 1)) :
    Fits (indexWidth 32 full.length q) (cardSlot full.length q candidate.val) := by
  have address := PA06A19PrepareCompactCandidates007.candidate_array_address_lt
    full.length q 0 candidate.val (by decide) candidate.isLt
  apply lt_trans address
  apply lt_of_le_of_lt _ (PA06A19PrepareCompactArrays018.linearLimit_fits full.length q)
  change PA06A19PrepareCompactCandidates007.workspaceEnd full.length q ≤ linearLimit full.length q
  unfold PA06A19PrepareCompactCandidates007.workspaceEnd linearLimit PA06A19PrepareCompactWord008.linearLimit
  omega

theorem card_value_fits (q : Nat) (full : List (Finset (Fin q))) (candidate : Nat) :
    Fits (indexWidth 32 full.length q) (RawCandidateStableOrder.candidateCard q full candidate) := by
  have bound : RawCandidateStableOrder.candidateCard q full candidate ≤ q := by
    simpa only [RawCandidateStableOrder.candidateCard, Fintype.card_fin] using
      Finset.card_le_univ ((RawCandidateOrder.candidateSupports q full).getD candidate ∅)
  exact PA06A19PrepareCompactArrays018.value_le_count_fits _ _ _ (by omega)

/-- Native provenance plus exact refinement, rather than an assumed word
cache: both address and actual cardinality are proved to avoid wrapping. -/
theorem card_data_of_native (q : Nat) (full : List (Finset (Fin q)))
    (native : NatState) (actual : WordState (indexWidth 32 full.length q))
    (entry : ParentEntry q full native)
    (refinement : actual = native.toWord (indexWidth 32 full.length q)) :
    CardData q full actual := by
  obtain ⟨order, inverse, tables, _support⟩ := entry.tables
  rw [refinement]
  intro candidate
  have stored : native.heap (cardSlot full.length q candidate.val) =
      RawCandidateStableOrder.candidateCard q full candidate.val :=
    tables.cards candidate.val candidate.isLt
  change (BitVec.ofNat _ (native.heap (BitVec.ofNat (indexWidth 32 full.length q)
    (cardSlot full.length q candidate.val)).toNat)).toNat = _
  simp only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (card_address_fits q full candidate),
    stored, Nat.mod_eq_of_lt (card_value_fits q full candidate.val)]

theorem card_data_frame (q : Nat) (full : List (Finset (Fin q)))
    (before after : WordState (indexWidth 32 full.length q))
    (frame : ∀ address : BitVec (indexWidth 32 full.length q),
      16 ≤ address.toNat → after.heap address = before.heap address)
    (data : CardData q full before) : CardData q full after := by
  intro candidate
  have above : 16 ≤ (BitVec.ofNat (indexWidth 32 full.length q)
      (cardSlot full.length q candidate.val)).toNat := by
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (card_address_fits q full candidate)]
    unfold cardSlot RawCandidateOrderingRAM.arraySlot
    omega
  rw [frame _ above]
  exact data candidate

/-- The unchanged Ord entry's chosen clock, augmented with all true raw
card words. Every previous native, Word, ord and prefix output is kept. -/
theorem parent_entry (q : Nat) (full : List (Finset (Fin q))) (tail : List PackingOp)
    (initialUsed : Finset (Fin q)) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (hend : Fits (indexWidth 32 full.length q) (5 * (program tail).length))
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode (program tail))) :
    ∃ clock ≤ PA06A19PrepareCompactCandidates007.parentClockBound q full,
      let native := natRun (rawIncidenceROM q full) (program tail) clock natInitial
      let actual := packingRun (CompactControllerClaims.controllerInput q full initialUsed) (program tail) clock
        (natInitial.toWord (indexWidth 32 full.length q))
      ParentEntry q full native ∧ PA06A19PrepareCompactArrays018.InverseValuesBound q full native ∧
        RegistersFit (indexWidth 32 full.length q) native ∧ WordParents q full actual ∧ OrdData q full actual ∧
        CardData q full actual ∧
        (∀ node : (prepareNormalization q full).indexed.NodeId,
          (actual.heap (BitVec.ofNat _ (ordSlot full.length q node.val))).toNat =
            RawCandidateParentRAM.observedOrder q full 16 native node.val) ∧
        (∀ count ≤ clock,
          packingRun (CompactControllerClaims.controllerInput q full initialUsed) (program tail) count
            (natInitial.toWord (indexWidth 32 full.length q)) =
              (natRun (rawIncidenceROM q full) (program tail) count natInitial).toWord (indexWidth 32 full.length q)) ∧
        ∀ count < clock,
          let current := packingRun (CompactControllerClaims.controllerInput q full initialUsed) (program tail) count
            (natInitial.toWord (indexWidth 32 full.length q))
          current.halted = false ∧ current.pc.toNat + 4 < (packingCode (program tail)).length ∧
            ∃ op, PackingOp.decode (fetch (program tail) current) = some op ∧
              packingAccessFits (CompactControllerClaims.controllerInput q full initialUsed)
                (linearLimit full.length q) current op := by
  obtain ⟨clock, bound, entry, inverse, registers, parents, ordinal, ordTransport, wordPrefix, prefixSafe⟩ :=
    PA06A19PrepareCompactParents035Ord.parent_entry q full tail initialUsed hq hlaminar hend hwords
  refine ⟨clock, bound, entry, inverse, registers, parents, ordinal, ?_, ordTransport, wordPrefix, prefixSafe⟩
  exact card_data_of_native q full _ _ entry (wordPrefix clock le_rfl)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareCompactParents035Cards
