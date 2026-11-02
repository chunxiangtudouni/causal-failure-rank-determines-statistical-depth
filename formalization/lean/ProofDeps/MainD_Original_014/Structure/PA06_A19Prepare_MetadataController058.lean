module

public import Structure.PA06_A19Prepare_ROMWord058
public import Structure.PA06_A19Prepare_StaticMetadata036_WordComplete

set_option autoImplicit false
set_option warningAsError true

/-! The same joint532 clock runs on the ORIGINAL controllerInput, whose
used-bit tail extends the raw incidence ROM. This does not choose another
metadata witness and does not assume tail-insensitivity from an output.
Every real old ROM-load bound comes from that producer's own prefixes.
Candidate until strict validation. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareMetadataController058

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims CompactControllerClaims RawIncidenceLaminarRAM
open PA06A19PrepareStaticMetadata036
open PA06A19PrepareChildrenCache023
  (preparedSize actualControlBase actualPackedWords actualAllocation OutputData)
open PA06A19PrepareBankNodeBit022 (wordView)

theorem metadata_controller_build (left right : List PackingOp)
    (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
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
      let rom := controllerInput q full used
      let after := packingRun rom code clock before
      (∀ position < (staticMetadata q full).length,
        (wordView after).heap (6 + actualPackedWords q full + position) =
          (staticMetadata q full).getD position 0) ∧
      after.register .address = before.register .address ∧
      after.pc.toNat = 5 * (left.length + 532) ∧ after.halted = false ∧
      (∀ address : BitVec (indexWidth 32 full.length q),
        ¬ MetadataAllowed q full (actualControlBase q full) (actualPackedWords q full) address.toNat →
          after.heap address = before.heap address) ∧
      (∀ count < clock,
        let state := packingRun rom code count before
        state.register .address = before.register .address ∧ state.halted = false ∧
          state.pc.toNat + 4 < (packingCode code).length ∧
          ∃ op, PackingOp.decode (fetch code state) = some op ∧
            packingAccessFits rom (actualAllocation q full) state op) := by
  let code := left ++ metadataProgramAt left.length ++ right
  let raw := rawIncidenceROM q full
  let runtime := controllerInput q full used
  have hprefix : PA06A19PrepareROM001.ROMPrefix raw runtime :=
    PA06A19PrepareROM001.inputTail_prefix raw
      ((List.finRange q).map (fun tool => bit (decide (tool ∈ used))))
  obtain ⟨clock, bound, post⟩ :=
    metadata_word_build left right q full hq hl before input children hpc ha hcode hcodePC
  dsimp only at post
  rcases post with ⟨_word, words, address, pc, active, frame, _input, _complete, _safe, prefixes⟩
  have equal (count : Nat) (hc : count ≤ clock) :
      packingRun runtime code count before = packingRun raw code count before := by
    apply PA06A19PrepareROMWord058.run_eq_of_prefix hprefix (actualAllocation q full)
    intro k hk
    exact (prefixes k (by omega)).2.2.2
  have finalEq := equal clock le_rfl
  refine ⟨clock, bound, ?_⟩
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [finalEq]
    exact words
  · rw [finalEq]
    exact address
  · rw [finalEq]
    exact pc
  · rw [finalEq]
    exact active
  · rw [finalEq]
    exact frame
  · intro count hc
    rw [equal count (Nat.le_of_lt hc)]
    have old := prefixes count hc
    obtain ⟨op, decoded, access⟩ := old.2.2.2
    exact ⟨old.1, old.2.1, old.2.2.1, op, decoded,
      PA06A19PrepareROMWord058.access_of_prefix hprefix (actualAllocation q full) _ op access⟩

end PaperProofs.Structure.LaminarTree.PA06A19PrepareMetadataController058
