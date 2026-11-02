module

public import Structure.PA06_A19Prepare_FinalRepresentation059_MetadataFrame
public import Structure.PA06_A19Prepare_MetadataController058

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED one selected actual058 clock with original logical table,
NEW-C capacity, permanent data and temporary-header transfer functions.
No table, bound, metadata answer or full HeapRepresents enters this call. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation059
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims
open PA06A19PreparePreBuild044 (bits capacity packedWords controlBase ScalarData)
open PA06A19PrepareStaticMetadata036 (ScanInput MetadataAllowed metadataProgramAt metadataNatBound)
open PA06A19PrepareChildrenCache023
  (preparedSize actualControlBase actualPackedWords actualAllocation OutputData)
open PA06A19PrepareBankNodeBit022 (wordView)

theorem actual_metadata_resources (left right : List PackingOp)
    (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before : WordState (bits q full))
    (input : ScanInput q full (actualControlBase q full) (actualPackedWords q full) (wordView before))
    (children : OutputData q full (actualControlBase q full) (wordView before))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hcode : WordsFit (bits q full) (packingCode (left ++ metadataProgramAt left.length ++ right)))
    (hcodePC : Fits (bits q full) (5 * (left ++ metadataProgramAt left.length ++ right).length)) :
    ∃ clock ≤ metadataNatBound full.length q (preparedSize q full),
      let code := left ++ metadataProgramAt left.length ++ right
      let rom := controllerInput q full used
      let after := packingRun rom code clock before
      (∀ position < (staticMetadata q full).length,
        (wordView after).heap (6 + actualPackedWords q full + position) =
          (staticMetadata q full).getD position 0) ∧
      (∀ position (hp : position < (staticMetadata q full).length),
        logicalHeap q (capacity q full) after.heap (capacity q full + 2 + position) =
          (staticMetadata q full)[position]'hp) ∧
      (∀ position < (staticMetadata q full).length,
        6 + packedWords q full + position < controlBase q full ∧
          Fits (bits q full) (6 + packedWords q full + position)) ∧
      (∀ address < capacity q full,
        logicalHeap q (capacity q full) after.heap address = logicalHeap q (capacity q full) before.heap address) ∧
      (PhysicalTableCorrect q full (logicalHeap q (capacity q full) before.heap) →
        PhysicalTableCorrect q full (logicalHeap q (capacity q full) after.heap)) ∧
      (CapacityPrefixBounded q (capacity q full) (logicalHeap q (capacity q full) before.heap) →
        CapacityPrefixBounded q (capacity q full) (logicalHeap q (capacity q full) after.heap)) ∧
      (ScalarData q full before → ScalarData q full after) ∧
      (PA06A19PrepareRuntimePacked016.Header q before.heap → PA06A19PrepareRuntimePacked016.Header q after.heap) ∧
      after.register .address = before.register .address ∧
      after.pc.toNat = 5 * (left.length + 532) ∧ after.halted = false ∧
      (∀ point : BitVec (bits q full),
        ¬ MetadataAllowed q full (actualControlBase q full) (actualPackedWords q full) point.toNat →
          after.heap point = before.heap point) ∧
      (∀ count < clock,
        let state := packingRun rom code count before
        state.register .address = before.register .address ∧ state.halted = false ∧
          state.pc.toNat + 4 < (packingCode code).length ∧
          ∃ op, PackingOp.decode (fetch code state) = some op ∧
            packingAccessFits rom (actualAllocation q full) state op) := by
  obtain ⟨clock, bound, words, address, pc, active, frame, prefixes⟩ :=
    PA06A19PrepareMetadataController058.metadata_controller_build left right q full used hq hl before
      input children hpc ha hcode hcodePC
  let after := packingRun (controllerInput q full used)
    (left ++ metadataProgramAt left.length ++ right) clock before
  refine ⟨clock, bound, ?_⟩
  dsimp only
  exact ⟨words, metadata_words_to_logical q full hq after words,
    metadata_actual_address_bounds q full hq hl,
    metadata_logical_capacity_frame q full hq before after frame,
    metadata_table_correct q full hq before after frame,
    metadata_logical_bounded q full hq before after frame,
    metadata_scalarData q full hq before after frame address,
    metadata_header_frame q full hq before after frame,
    address, pc, active, frame, prefixes⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareFinalRepresentation059
