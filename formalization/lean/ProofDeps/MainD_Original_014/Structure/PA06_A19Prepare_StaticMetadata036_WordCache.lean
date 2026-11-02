module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordCopy

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Discharge copy-source word/room bounds from the real023 cache output.
No source-word range or extra heap capacity is a new original input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareChildrenCache023
  (preparedSize mass parentAddress degreeBase childrenBase OutputData highCacheEnd actualControlBase actualAllocation mass_fits32)

theorem adjacency_source_words_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (CB : Nat) (state : NatState) (output : OutputData q full CB state) :
    (∀ index < preparedSize q full,
      state.heap (parentAddress CB (mass q full) 0 + index) ≤ mass q full) ∧
    (∀ index < 2 * preparedSize q full - 1,
      state.heap (degreeBase CB (mass q full) + index) ≤ mass q full) := by
  have internalLength : (givenTreeROM q full).internal.length = 2 * preparedSize q full :=
    RawTreeSerialization.givenTreeROM_internal_length q full
  have childrenLength : (givenTreeROM q full).children.length = preparedSize q full - 1 :=
    RawTreeSerialization.givenTreeROM_children_length q full hq hl
  constructor
  · intro index hi
    have he : parentAddress CB (mass q full) 0 + index = parentAddress CB (mass q full) index := by
      unfold parentAddress
      omega
    have hbound : index < (givenTreeROM q full).internal.length := by
      rw [internalLength]
      omega
    rw [he, output.1.parents index hi, PA06A19PrepareChildrenCache023.parentWord,
      List.getD_eq_getElem _ 0 hbound]
    exact RawTreeOutputWords.givenTreeROM_word_le q full .internal _ (List.getElem_mem hbound)
  · intro index hi
    by_cases hdegree : index < preparedSize q full
    · have hword : state.heap (degreeBase CB (mass q full) + index) =
          (givenTreeROM q full).internal.getD (preparedSize q full + index) 0 :=
        output.2.1 (⟨index, hdegree⟩ : (prepareNormalization q full).indexed.NodeId)
      have hbound : preparedSize q full + index < (givenTreeROM q full).internal.length := by
        rw [internalLength]
        omega
      rw [hword, List.getD_eq_getElem _ 0 hbound]
      exact RawTreeOutputWords.givenTreeROM_word_le q full .internal _ (List.getElem_mem hbound)
    · let child := index - preparedSize q full
      have hc : child < (givenTreeROM q full).children.length := by
        rw [childrenLength]
        dsimp only [child]
        omega
      have he : degreeBase CB (mass q full) + index = childrenBase CB (mass q full) (preparedSize q full) + child := by
        unfold childrenBase child
        omega
      rw [he, output.2.2 child hc, List.getD_eq_getElem _ 0 hc]
      exact RawTreeOutputWords.givenTreeROM_word_le q full .children _ (List.getElem_mem hc)

theorem adjacency_source_ends (q : Nat) (full : List (Finset (Fin q))) (CB : Nat) :
    parentAddress CB (mass q full) 0 + preparedSize q full ≤ highCacheEnd CB (mass q full) ∧
      degreeBase CB (mass q full) + (2 * preparedSize q full - 1) ≤ highCacheEnd CB (mass q full) := by
  have ht := prepared_indexed_size_le q full
  change preparedSize q full ≤ mass q full at ht
  unfold parentAddress degreeBase highCacheEnd
  omega

/-- All internal obligations used by the real9-op copy safety are derived
at the original common32/8192 source addresses. -/
theorem actual_adjacency_source_bounds (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (state : NatState) (output : OutputData q full (actualControlBase q full) state) :
    (parentAddress (actualControlBase q full) (mass q full) 0 + preparedSize q full < actualAllocation q full) ∧
    (degreeBase (actualControlBase q full) (mass q full) + (2 * preparedSize q full - 1) < actualAllocation q full) ∧
    (∀ index < preparedSize q full,
      state.heap (parentAddress (actualControlBase q full) (mass q full) 0 + index) ≤
        metadataWordLimit (indexWidth 32 full.length q)) ∧
    (∀ index < 2 * preparedSize q full - 1,
      state.heap (degreeBase (actualControlBase q full) (mass q full) + index) ≤
        metadataWordLimit (indexWidth 32 full.length q)) := by
  have room := PA06A19PrepareChildrenCache023.highCacheEnd_actual_fits q full hq
  have ends := adjacency_source_ends q full (actualControlBase q full)
  have values := adjacency_source_words_le q full hq hl (actualControlBase q full) state output
  refine ⟨ends.1.trans_lt room.1, ends.2.trans_lt room.1, ?_, ?_⟩
  · intro index hi
    exact metadata_le_wordLimit ((values.1 index hi).trans_lt (mass_fits32 q full))
  · intro index hi
    exact metadata_le_wordLimit ((values.2 index hi).trans_lt (mass_fits32 q full))

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
