module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordStageOuter
public import Structure.PA06_A19Prepare_ChildrenCache023_Word

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNVALIDATED common32 physical refinement of the unchanged complete
202-op stage producer. Its single joint Nat clock supplies semantics,
frame and all-prefix safety simultaneously. This is the stage segment; all532 composition remains separate.
No Laminar assumption is needed by this segment alone. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass actualPackedWords actualControlBase actualAllocation mass_fits32)
open PA06A19PrepareBankNodeBit022 (wordView)

theorem originalStage_le_mass (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin full.length) :
    encodedNode (prepareNormalization q full).indexed
      ((IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage) ≤ mass q full := by
  cases hstage : (IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage with
  | none =>
    simp only [encodedNode]
    omega
  | some node =>
    simp only [encodedNode]
    have hn : node.val < preparedSize q full := node.isLt
    have ht : preparedSize q full ≤ mass q full := prepared_indexed_size_le q full
    omega

/-- Every original stage value is physically written by the actual
202-op scan. The selected clock also certifies every prefix, the actual
hardware control-base register, proper fetch/access and finite write frame.
Incoming registers are arbitrary words; the caller supplies only the real
copied raw-card/ord cells, dimensions, code and starting PC. -/
theorem stage_word_build (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (code : StageCodeAt containing start)
    (before : WordState (indexWidth 32 full.length q))
    (input : ScanInput q full (actualControlBase q full) (actualPackedWords q full) (wordView before))
    (hpc : before.pc.toNat = 5 * start) (ha : before.halted = false)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    ∃ clock ≤ 13 + full.length * (50 + preparedSize q full * (63 + 90 * q)),
      let after := packingRun (rawIncidenceROM q full) containing clock before
      (∀ count ≤ clock, packingRun (rawIncidenceROM q full) containing count before =
        (natRun (rawIncidenceROM q full) containing count (wordView before)).toWord
          (indexWidth 32 full.length q)) ∧
      (∀ stage : Fin full.length,
        (wordView after).heap
          (fieldAddress (actualPackedWords q full) full.length (preparedSize q full) .stage stage.val) =
            encodedNode (prepareNormalization q full).indexed
              ((IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage)) ∧
      after.register .address = before.register .address ∧
      after.pc.toNat = 5 * (start + 202) ∧ after.halted = false ∧
      (∀ address : BitVec (indexWidth 32 full.length q),
        ¬ StageAllowed q full (actualControlBase q full) (actualPackedWords q full) address.toNat →
          after.heap address = before.heap address) ∧
      (∀ count < clock,
        let state := packingRun (rawIncidenceROM q full) containing count before
        state.register .address = before.register .address ∧ state.halted = false ∧
          state.pc.toNat + 4 < (packingCode containing).length ∧
          ∃ op, PackingOp.decode (fetch containing state) = some op ∧
            packingAccessFits (rawIncidenceROM q full) (actualAllocation q full) state op) := by
  let rom := rawIncidenceROM q full
  let bits := indexWidth 32 full.length q
  let CB := actualControlBase q full
  let P := actualPackedWords q full
  let H := actualAllocation q full
  let initial := wordView before
  have initialRegs : RegistersFit bits initial := fun reg => (before.register reg).isLt
  obtain ⟨clock, clockBound, nativeInput, nativeStages, nativeFrame,
    nativeAddress, nativePC, nativeActive, safe⟩ :=
    stage_actual_joint q full hq containing start code initial input initialRegs hpc ha hcodePC
  have rfit (count : Nat) (hc : count ≤ clock) : RegistersFit bits (natRun rom containing count initial) := by
    intro reg
    exact ((safe.1.1 count hc).1 reg).trans_lt (metadata_wordLimit_fits bits)
  have pfit (count : Nat) (hc : count ≤ clock) : Fits bits (natRun rom containing count initial).pc := by
    obtain ⟨_regs, _active, index, hi, hp⟩ := safe.1.1 count hc
    rw [hp]
    exact (Nat.mul_le_mul_left 5 hi).trans_lt hcodePC
  have word (count : Nat) (hc : count ≤ clock) :
      packingRun rom containing count before = (natRun rom containing count initial).toWord bits := by
    rw [← PA06A19PrepareBankNodeBit022.wordView_toWord before]
    exact natRun_toWord rom containing initial count hcode
      (fun k hk => ⟨rfit k (by omega), pfit k (by omega)⟩)
  have control := actual_metadata_control_slot q full hq 0 (by decide)
  simp only [Nat.add_zero] at control
  refine ⟨clock, clockBound, ?_⟩
  dsimp only
  refine ⟨word, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro stage
    have addressFit : Fits bits (fieldAddress P full.length (preparedSize q full) .stage stage.val) :=
      lt_trans (fieldAddress_lt_control full.length q (preparedSize q full) P .stage stage.val stage.isLt) control.2
    have valueFit : Fits bits ((natRun rom containing clock initial).heap
        (fieldAddress P full.length (preparedSize q full) .stage stage.val)) := by
      rw [nativeStages stage]
      exact (originalStage_le_mass q full hq stage).trans_lt (mass_fits32 q full)
    rw [word _ le_rfl]
    rw [PA06A19PrepareChildrenCache023.wordView_cell _ _ addressFit valueFit]
    exact nativeStages stage
  · rw [word _ le_rfl]
    change BitVec.ofNat bits _ = _
    rw [safe.2 _ le_rfl]
    simp only [initial, PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [word _ le_rfl]
    change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pfit _ le_rfl), nativePC]
  · rw [word _ le_rfl]
    exact nativeActive
  · intro address hprotected
    rw [word _ le_rfl]
    change BitVec.ofNat bits ((natRun rom containing clock initial).heap address.toNat) = before.heap address
    rw [nativeFrame address.toNat hprotected]
    simp only [initial, PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro count hc
    obtain ⟨index, hi, hp, access⟩ := safe.1.2 count hc
    rw [word count hc.le]
    have pcWord : ((natRun rom containing count initial).toWord bits).pc.toNat = 5 * index := by
      change (BitVec.ofNat bits _).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pfit count hc.le), hp]
    refine ⟨?_, (safe.1.1 count hc.le).2.1, ?_, containing[index], ?_, ?_⟩
    · change BitVec.ofNat bits _ = _
      rw [safe.2 count hc.le]
      simp only [initial, PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [pcWord, packingCode_length]
      omega
    · change PackingOp.decode (physicalFetch bits (packingCode containing)
        ((natRun rom containing count initial).toWord bits).pc.toNat) = _
      rw [pcWord, physicalFetch_eq _ _ _ hcode]
      change PackingOp.decode (natFetch containing (5 * index)) = _
      rw [natFetch_body containing index hi, decode_encode]
    · exact physical_access_of_nat rom H _ _ (rfit count hc.le) access

end PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
