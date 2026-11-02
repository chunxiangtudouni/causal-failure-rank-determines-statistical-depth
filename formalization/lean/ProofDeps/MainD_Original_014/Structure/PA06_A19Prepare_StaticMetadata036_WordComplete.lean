module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordCompleteTransport

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNVALIDATED physical producer for the unchanged532 metadata program.
All four producers execute in their original order on one actual state.
The original raw/023 caches are the only entry data. Actual postDP delivery
of that entry data and the surrounding full preprocessor remain separate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass OutputData actualPackedWords actualControlBase actualAllocation RunFacts)
open PA06A19PrepareBankNodeBit022 (wordView)

/-- All nine original staticMetadata segments are actually written in the
original common32/8192 allocation. The entry assumptions are actual source
cells and starting code/PC facts, never a future output or whole-run oracle. -/
theorem metadata_word_build (left right : List PackingOp) (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (before : WordState (indexWidth 32 full.length q))
    (input : ScanInput q full (actualControlBase q full) (actualPackedWords q full) (wordView before))
    (children : OutputData q full (actualControlBase q full) (wordView before))
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hcode : WordsFit (indexWidth 32 full.length q)
      (packingCode (left ++ metadataProgramAt left.length ++ right)))
    (hcodePC : Fits (indexWidth 32 full.length q)
      (5 * (left ++ metadataProgramAt left.length ++ right).length)) :
    ∃ clock ≤ metadataNatBound full.length q (preparedSize q full),
      let code := left ++ metadataProgramAt left.length ++ right
      let rom := rawIncidenceROM q full
      let native := natRun rom code clock (wordView before)
      let after := packingRun rom code clock before
      (∀ count ≤ clock, packingRun rom code count before =
        (natRun rom code count (wordView before)).toWord (indexWidth 32 full.length q)) ∧
      (∀ position < (staticMetadata q full).length,
        (wordView after).heap (6 + actualPackedWords q full + position) =
          (staticMetadata q full).getD position 0) ∧
      after.register .address = before.register .address ∧
      after.pc.toNat = 5 * (left.length + 532) ∧ after.halted = false ∧
      (∀ address : BitVec (indexWidth 32 full.length q),
        ¬ MetadataAllowed q full (actualControlBase q full) (actualPackedWords q full) address.toNat →
          after.heap address = before.heap address) ∧
      ScanInput q full (actualControlBase q full) (actualPackedWords q full) native ∧
      CompleteMetadataWritten q full hq (actualPackedWords q full) native ∧
      RunFacts (metadataWordLimit (indexWidth 32 full.length q)) (actualAllocation q full)
        rom code clock (wordView before) ∧
      (∀ count < clock,
        let state := packingRun rom code count before
        state.register .address = before.register .address ∧ state.halted = false ∧
          state.pc.toNat + 4 < (packingCode code).length ∧
          ∃ op, PackingOp.decode (fetch code state) = some op ∧
            packingAccessFits rom (actualAllocation q full) state op) := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let code := left ++ metadataProgramAt left.length ++ right
  let initial := wordView before
  have initialRegs : RegistersFit bits initial := fun reg => (before.register reg).isLt
  obtain ⟨clock, clockBound, nativeInput, nativeComplete, nativeWords, nativeFrame,
    _nativeAddress, nativePC, nativeActive, safe⟩ :=
    metadata_actual_joint left right q full hq hl initial input children initialRegs hpc ha hcodePC
  have transported := metadata_word_run_transport q full code before clock safe hcode hcodePC
  rcases transported with ⟨word, address, pc, active, prefixes⟩
  refine ⟨clock, clockBound, ?_⟩
  dsimp only
  refine ⟨word, ?_, address, pc.trans nativePC, active.trans nativeActive, ?_,
    nativeInput, nativeComplete, safe, prefixes⟩
  · intro position hp
    rw [word clock le_rfl]
    exact metadata_output_toWord q full hq hl (natRun rom code clock initial) nativeWords position hp
  · exact metadata_word_frame_transport before (packingRun rom code clock before)
      (natRun rom code clock initial) (fun address => ¬ MetadataAllowed q full CB P address)
      (word clock le_rfl) nativeFrame

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
