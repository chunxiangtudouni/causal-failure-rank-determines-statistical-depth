module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordAdjacency
public import Structure.PA06_A19Prepare_ChildrenCache023_Word

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Physical common32 execution of the real55-op adjacency producer.
Every fetched prefix refines its real Nat execution, preserves hardwareCB,
stays ACTIVE and has a valid access. The first four original metadata
segments are actual word-heap output. Whole staticMetadata remains open. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass actualPackedWords actualControlBase actualAllocation OutputData)
open PA06A19PrepareBankNodeBit022 (wordView)

theorem adjacency_word_build (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hl : LaminarSchedule full) (rom : PhysicalROM)
    (left right : List PackingOp) (before : WordState (indexWidth 32 full.length q))
    (output : OutputData q full (actualControlBase q full) (wordView before))
    (hpermanentT : (wordView before).heap (actualControlBase q full + 2) = preparedSize q full)
    (hpermanentBase : (wordView before).heap (actualControlBase q full + 6) = 4 + actualPackedWords q full)
    (hpc : before.pc.toNat = 5 * left.length) (ha : before.halted = false)
    (hcode : WordsFit (indexWidth 32 full.length q)
      (packingCode (left ++ adjacencyProgramAt left.length ++ right)))
    (hcodePC : Fits (indexWidth 32 full.length q)
      (5 * (left ++ adjacencyProgramAt left.length ++ right).length)) :
    let code := left ++ adjacencyProgramAt left.length ++ right
    let steps := adjacencyTotalSteps (preparedSize q full)
    let after := packingRun rom code steps before
    (∀ count ≤ steps, packingRun rom code count before =
      (natRun rom code count (wordView before)).toWord (indexWidth 32 full.length q)) ∧
      (∀ position < 3 * preparedSize q full,
        (wordView after).heap (6 + actualPackedWords q full + position) = (staticMetadata q full).getD position 0) ∧
      after.register .address = before.register .address ∧
      after.pc.toNat = 5 * (left.length + 55) ∧ after.halted = false ∧
      (∀ address : BitVec (indexWidth 32 full.length q),
        address.toNat < 6 + actualPackedWords q full ∨
          6 + actualPackedWords q full + 3 * preparedSize q full ≤ address.toNat →
        after.heap address = before.heap address) ∧
      (∀ count < steps,
        let state := packingRun rom code count before
        state.register .address = before.register .address ∧ state.halted = false ∧
          state.pc.toNat + 4 < (packingCode code).length ∧
          ∃ op, PackingOp.decode (fetch code state) = some op ∧ packingAccessFits rom (actualAllocation q full) state op) := by
  let bits := indexWidth 32 full.length q
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let H := actualAllocation q full
  let initial := wordView before
  let steps := adjacencyTotalSteps (preparedSize q full)
  let code := left ++ adjacencyProgramAt left.length ++ right
  have layout : CB = 4 + P + 4096 * (mass q full + preparedSize q full) := rfl
  have initialRegs : RegistersFit bits initial := fun reg => (before.register reg).isLt
  have safe := adjacency_actual_runFacts q full hq hl rom left right initial output
    hpermanentT hpermanentBase initialRegs hpc ha hcodePC
  have native := adjacency_build rom left right q full hq hl CB P initial output
    hpermanentT hpermanentBase layout hpc ha
  have rfit (count : Nat) (hc : count ≤ steps) : RegistersFit bits (natRun rom code count initial) := by
    intro reg
    exact ((safe.1.1 count hc).1 reg).trans_lt (metadata_wordLimit_fits bits)
  have pfit (count : Nat) (hc : count ≤ steps) : Fits bits (natRun rom code count initial).pc := by
    obtain ⟨_regs, _active, index, hi, hp⟩ := safe.1.1 count hc
    rw [hp]
    exact (Nat.mul_le_mul_left 5 hi).trans_lt hcodePC
  have word (count : Nat) (hc : count ≤ steps) :
      packingRun rom code count before = (natRun rom code count initial).toWord bits := by
    rw [← PA06A19PrepareBankNodeBit022.wordView_toWord before]
    exact natRun_toWord rom code initial count hcode
      (fun k hk => ⟨rfit k (by omega), pfit k (by omega)⟩)
  dsimp only
  refine ⟨word, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro position hp
    rw [word _ le_rfl]
    have hposition : position < (staticMetadata q full).length := by
      rw [metadata_length_exact q full hq hl]
      omega
    have written := adjacencyWritten_static q full hq hl P _ native.1 position hp
    have addressFit := (actual_metadata_output_bounds q full hq hl).2.2 position hposition
    have valueFit : Fits bits ((natRun rom code steps initial).heap (6 + P + position)) := by
      rw [written, List.getD_eq_getElem _ 0 hposition]
      exact metadata_wordsFit32 q full hq hl _ (List.getElem_mem hposition)
    rw [PA06A19PrepareChildrenCache023.wordView_cell _ (6 + P + position) addressFit.2 valueFit]
    exact written
  · rw [word _ le_rfl]
    change BitVec.ofNat bits _ = _
    rw [safe.2 _ le_rfl]
    simp only [initial, PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [word _ le_rfl]
    change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pfit _ le_rfl), native.2.2.2.2.2.2.1]
  · rw [word _ le_rfl]
    exact native.2.2.2.2.2.2.2
  · intro address hprotected
    rw [word _ le_rfl]
    change BitVec.ofNat bits ((natRun rom code steps initial).heap address.toNat) = before.heap address
    rw [native.2.1 address.toNat hprotected]
    simp only [initial, PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro count hc
    obtain ⟨index, hi, hp, access⟩ := safe.1.2 count hc
    rw [word count hc.le]
    have pcWord : ((natRun rom code count initial).toWord bits).pc.toNat = 5 * index := by
      change (BitVec.ofNat bits _).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pfit count hc.le), hp]
    refine ⟨?_, (safe.1.1 count hc.le).2.1, ?_, code[index], ?_, ?_⟩
    · change BitVec.ofNat bits _ = _
      rw [safe.2 count hc.le]
      simp only [initial, PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [pcWord, packingCode_length]
      omega
    · change PackingOp.decode (physicalFetch bits (packingCode code)
        ((natRun rom code count initial).toWord bits).pc.toNat) = _
      rw [pcWord, physicalFetch_eq _ _ _ hcode]
      change PackingOp.decode (natFetch code (5 * index)) = _
      rw [natFetch_body code index hi, decode_encode]
    · exact physical_access_of_nat rom H _ _ (rfit count hc.le) access

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
