module

public import Structure.PA06_A19Prepare_StaticMetadata036_WordCardsRun
public import Structure.PA06_A19Prepare_ChildrenCache023_Word

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! UNCOMPILED physical common32 corollary for the actual84-op card and
internal-bit producer, at the original13+80t Nat clock. All prefixes refine
the same Nat run; raw cache data is consumed rather than future outputs. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareStaticMetadata036
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
  RawTreePreprocessingClaims PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareChildrenCache023
  (preparedSize mass actualPackedWords actualControlBase actualAllocation mass_fits32)
open PA06A19PrepareBankNodeBit022 (wordView)

theorem cards_word_build (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (containing : List PackingOp) (start : Nat) (code : CardsCodeAt containing start)
    (before : WordState (indexWidth 32 full.length q))
    (input : ScanInput q full (actualControlBase q full) (actualPackedWords q full) (wordView before))
    (hpc : before.pc.toNat = 5 * start) (ha : before.halted = false)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    let steps := 13 + 80 * preparedSize q full
    let after := packingRun (rawIncidenceROM q full) containing steps before
    (∀ count ≤ steps, packingRun (rawIncidenceROM q full) containing count before =
      (natRun (rawIncidenceROM q full) containing count (wordView before)).toWord (indexWidth 32 full.length q)) ∧
      (∀ node : (prepareNormalization q full).indexed.NodeId,
        (wordView after).heap (fieldAddress (actualPackedWords q full) full.length (preparedSize q full) .cardinality node.val) =
          (prepareNormalization q full).indexed.metadata.cardinalities.get node ∧
        (wordView after).heap (fieldAddress (actualPackedWords q full) full.length (preparedSize q full) .internal node.val) =
          bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) ∧
      after.register .address = before.register .address ∧
      after.pc.toNat = 5 * (start + 84) ∧ after.halted = false ∧
      (∀ address : BitVec (indexWidth 32 full.length q),
        ¬ CardsAllowed q full (actualControlBase q full) (actualPackedWords q full) address.toNat →
          after.heap address = before.heap address) ∧
      (∀ count < steps,
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
  let steps := 13 + 80 * preparedSize q full
  have layout : CB = 4 + P + 4096 * (mass q full + preparedSize q full) := rfl
  have initialRegs : RegistersFit bits initial := fun reg => (before.register reg).isLt
  have safe := cards_actual_runFacts q full hq containing start code initial input initialRegs hpc ha hcodePC
  have native := cards_build q full CB P containing start code initial input layout hpc ha
  have rfit (count : Nat) (hc : count ≤ steps) : RegistersFit bits (natRun rom containing count initial) := by
    intro reg
    exact ((safe.1.1 count hc).1 reg).trans_lt (metadata_wordLimit_fits bits)
  have pfit (count : Nat) (hc : count ≤ steps) : Fits bits (natRun rom containing count initial).pc := by
    obtain ⟨_regs, _active, index, hi, hp⟩ := safe.1.1 count hc
    rw [hp]
    exact (Nat.mul_le_mul_left 5 hi).trans_lt hcodePC
  have word (count : Nat) (hc : count ≤ steps) :
      packingRun rom containing count before = (natRun rom containing count initial).toWord bits := by
    rw [← PA06A19PrepareBankNodeBit022.wordView_toWord before]
    exact natRun_toWord rom containing initial count hcode
      (fun k hk => ⟨rfit k (by omega), pfit k (by omega)⟩)
  dsimp only
  refine ⟨word, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro node
    have values := native.2.1 node
    have control := actual_metadata_control_slot q full hq 0 (by decide)
    simp only [Nat.add_zero] at control
    have cardAddress : Fits bits (fieldAddress P full.length (preparedSize q full) .cardinality node.val) :=
      lt_trans (fieldAddress_lt_control full.length q (preparedSize q full) P .cardinality node.val node.isLt) control.2
    have internalAddress : Fits bits (fieldAddress P full.length (preparedSize q full) .internal node.val) :=
      lt_trans (fieldAddress_lt_control full.length q (preparedSize q full) P .internal node.val node.isLt) control.2
    have cardValue : Fits bits ((natRun rom containing steps initial).heap
        (fieldAddress P full.length (preparedSize q full) .cardinality node.val)) := by
      rw [values.1]
      have hq' := metadata_cardinality_le_q q (prepareNormalization q full).indexed node
      exact (show (prepareNormalization q full).indexed.metadata.cardinalities.get node ≤ mass q full by unfold mass; omega).trans_lt
        (mass_fits32 q full)
    have internalValue : Fits bits ((natRun rom containing steps initial).heap
        (fieldAddress P full.length (preparedSize q full) .internal node.val)) := by
      rw [values.2]
      have small : bit ((prepareNormalization q full).indexed.metadata.isInternal.get node) ≤ mass q full := by
        cases h : (prepareNormalization q full).indexed.metadata.isInternal.get node <;> simp [bit]
      exact small.trans_lt (mass_fits32 q full)
    rw [word _ le_rfl]
    constructor
    · rw [PA06A19PrepareChildrenCache023.wordView_cell _ _ cardAddress cardValue]
      exact values.1
    · rw [PA06A19PrepareChildrenCache023.wordView_cell _ _ internalAddress internalValue]
      exact values.2
  · rw [word _ le_rfl]
    change BitVec.ofNat bits _ = _
    rw [safe.2 _ le_rfl]
    simp only [initial, PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · rw [word _ le_rfl]
    change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pfit _ le_rfl), native.2.2.2.2.1]
  · rw [word _ le_rfl]
    exact native.2.2.2.2.2
  · intro address hprotected
    rw [word _ le_rfl]
    change BitVec.ofNat bits ((natRun rom containing steps initial).heap address.toNat) = before.heap address
    rw [native.2.2.1 address.toNat hprotected]
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
