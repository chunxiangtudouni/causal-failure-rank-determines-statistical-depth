module

public import Structure.PA06_A19Prepare_ChildrenCache023_WordLoops
public import Structure.PA06_A19Prepare_BankNodeBit022
public import PaperProofs.Structure.PackingExecutionCost

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 30000
set_option maxHeartbeats 3000000

/-! Private uncompiled concrete width32 upgrade of the actual144-op children
cache builder. The original same8192 allocation supplies room; the caller
provides only the actual copied-cache representation and code location,
with arbitrary full-width hardware registers. Whole prepare remains separate. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m

abbrev wordView {bits : Nat} (state : WordState bits) : NatState :=
  PA06A19PrepareBankNodeBit022.wordView state

def wordLimit (bits : Nat) : Nat := 2 ^ bits - 1

theorem le_wordLimit {bits value : Nat} (hv : Fits bits value) : value ≤ wordLimit bits := by
  unfold Fits wordLimit at *
  omega

theorem wordLimit_fits (bits : Nat) : Fits bits (wordLimit bits) :=
  Nat.sub_lt (pow_pos (by decide : 0 < (2 : Nat)) bits) (by decide : 0 < (1 : Nat))

/-- The proof-side Nat view is exactly the same finite-word heap at each
fitting address. This function never changes or initializes runtime memory. -/
theorem wordView_cell {bits : Nat} (state : NatState) (address : Nat)
    (ha : Fits bits address) (hv : Fits bits (state.heap address)) :
    (wordView (state.toWord bits)).heap address = state.heap address := by
  simp only [PA06A19PrepareBankNodeBit022.wordView, NatState.toWord,
    BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hv]

theorem inputData_toWord (q : Nat) (full : List (Finset (Fin q))) (CB H : Nat) (state : NatState)
    (input : InputData q full CB state) (hroom : highCacheEnd CB (mass q full) < H)
    (hH : Fits (indexWidth 32 full.length q) H) :
    InputData q full CB (wordView (state.toWord (indexWidth 32 full.length q))) := by
  have fit (address : Nat) (ha : address ≤ highCacheEnd CB (mass q full)) :
      Fits (indexWidth 32 full.length q) address := ha.trans_lt (hroom.trans hH)
  constructor
  · change (BitVec.ofNat _ (state.register .address)).toNat = CB
    rw [input.address, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (fit CB (by unfold highCacheEnd; omega))]
  · rw [wordView_cell state (CB + 528) (fit _ (by unfold highCacheEnd; omega))
      (by rw [input.mass_cell]; exact mass_fits32 q full)]
    exact input.mass_cell
  · rw [wordView_cell state (CB + 532 + 4 * mass q full) (fit _ (by unfold highCacheEnd; omega))
      (by rw [input.node_cell]; exact preparedSize_fits32 q full)]
    exact input.node_cell
  · intro child hc
    have hchild : child < mass q full := hc.trans_le (preparedSize_le_mass q full)
    have haddress := fit (parentAddress CB (mass q full) child) (by unfold parentAddress highCacheEnd; omega)
    have hvalue : Fits (indexWidth 32 full.length q) (state.heap (parentAddress CB (mass q full) child)) := by
      rw [input.parents child hc, parentWord, RawCandidateChildrenLayout.givenTreeROM_parentWords q full child hc]
      exact ((UniformNormalizationRAM.encodedNode_le _ _).trans (preparedSize_le_mass q full)).trans_lt (mass_fits32 q full)
    rw [wordView_cell state _ haddress hvalue]
    exact input.parents child hc

theorem outputData_toWord (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (CB H : Nat) (state : NatState) (output : OutputData q full CB state)
    (hroom : highCacheEnd CB (mass q full) < H) (hH : Fits (indexWidth 32 full.length q) H) :
    OutputData q full CB (wordView (state.toWord (indexWidth 32 full.length q))) := by
  have fit (address : Nat) (ha : address ≤ highCacheEnd CB (mass q full)) :
      Fits (indexWidth 32 full.length q) address := ha.trans_lt (hroom.trans hH)
  have ht : preparedSize q full ≤ mass q full := preparedSize_le_mass q full
  refine ⟨inputData_toWord q full CB H state output.1 hroom hH, ?_, ?_⟩
  · intro node
    have hn : node.val < mass q full := node.isLt.trans_le ht
    have ha := fit (degreeBase CB (mass q full) + node.val) (by unfold degreeBase highCacheEnd; omega)
    have hv : Fits (indexWidth 32 full.length q) (state.heap (degreeBase CB (mass q full) + node.val)) := by
      have hdegree := UniformNormalizationRAM.givenTreeROM_degree q full node
      change (givenTreeROM q full).internal.getD (preparedSize q full + node.val) 0 = _ at hdegree
      rw [output.2.1 node, hdegree]
      exact ((RawTreeOutputWords.prepared_child_size_le q full node).trans ht).trans_lt (mass_fits32 q full)
    rw [wordView_cell state _ ha hv]
    exact output.2.1 node
  · intro position hp
    have hlen : (givenTreeROM q full).children.length = preparedSize q full - 1 :=
      RawTreeSerialization.givenTreeROM_children_length q full hq hl
    have hpos : position < mass q full := by
      rw [hlen] at hp
      have hsmall : position < preparedSize q full := by omega
      exact hsmall.trans_le ht
    have ha := fit (childrenBase CB (mass q full) (preparedSize q full) + position)
      (by unfold childrenBase degreeBase highCacheEnd; omega)
    have hv : Fits (indexWidth 32 full.length q)
        (state.heap (childrenBase CB (mass q full) (preparedSize q full) + position)) := by
      rw [output.2.2 position hp, List.getD_eq_getElem _ _ hp]
      exact PA17WordBounds023.givenTreeROM_wordsFit q full .children _ (List.getElem_mem hp)
    rw [wordView_cell state _ ha hv]
    exact output.2.2 position hp

/-- Genuine original-layout factory. This discharges allocation room
without making it an extra outer preprocessor input. -/
theorem original_layout (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (hpc : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    Layout q full (actualControlBase q full) (wordLimit (indexWidth 32 full.length q))
      (actualAllocation q full) containing start := by
  have h := highCacheEnd_actual_fits q full hq
  exact ⟨hq, hl, code, h.1, le_wordLimit h.2.1, le_wordLimit hpc⟩

/-- Concrete physical children-cache construction on the original same
allocation. No all-prefix safety or final OutputData is a caller premise. -/
theorem word_build (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hl : LaminarSchedule full)
    (rom : PhysicalROM) (containing : List PackingOp) (start : Nat) (code : CodeAt containing start)
    (before : WordState (indexWidth 32 full.length q))
    (input : InputData q full (actualControlBase q full) (wordView before))
    (hpc : before.pc.toNat = 5 * start) (hactive : before.halted = false)
    (hcode : WordsFit (indexWidth 32 full.length q) (packingCode containing))
    (hcodePC : Fits (indexWidth 32 full.length q) (5 * containing.length)) :
    let after := packingRun rom containing (totalSteps q full) before
    OutputData q full (actualControlBase q full) (wordView after) ∧
      after.register .address = before.register .address ∧
      after.pc.toNat = 5 * (start + 144) ∧ after.halted = false ∧
      (∀ address : BitVec (indexWidth 32 full.length q),
        Protected q full (actualControlBase q full) address.toNat → after.heap address = before.heap address) ∧
      (∀ count < totalSteps q full,
        let state := packingRun rom containing count before
        state.register .address = before.register .address ∧ state.halted = false ∧
        state.pc.toNat + 4 < (packingCode containing).length ∧
        ∃ op, PackingOp.decode (fetch containing state) = some op ∧ packingAccessFits rom (actualAllocation q full) state op) ∧
      totalSteps q full ≤ 200 * (preparedSize q full + 1) ^ 2 := by
  let bits := indexWidth 32 full.length q
  let CB := actualControlBase q full
  let H := actualAllocation q full
  let B := wordLimit bits
  let initial := wordView before
  have layout := original_layout q full hq hl containing start code hcodePC
  have regs : RegistersLE B initial := fun reg => le_wordLimit (before.register reg).isLt
  have safe := build_safe rom q full CB B H containing start layout initial input regs hpc hactive
  have native := build rom q full hq hl CB containing start code initial input hpc hactive
  have rfit (count : Nat) (hc : count ≤ totalSteps q full) :
      RegistersFit bits (natRun rom containing count initial) := by
    intro reg
    exact ((safe.1.1 count hc).1 reg).trans_lt (wordLimit_fits bits)
  have pfit (count : Nat) (hc : count ≤ totalSteps q full) : Fits bits (natRun rom containing count initial).pc := by
    obtain ⟨_reg, _active, index, hi, hp⟩ := safe.1.1 count hc
    rw [hp]
    exact (Nat.mul_le_mul_left 5 hi).trans_lt hcodePC
  have word (count : Nat) (hc : count ≤ totalSteps q full) :
      packingRun rom containing count before = (natRun rom containing count initial).toWord bits := by
    rw [← PA06A19PrepareBankNodeBit022.wordView_toWord before]
    exact natRun_toWord rom containing initial count hcode (fun k hk => ⟨rfit k (by omega), pfit k (by omega)⟩)
  rw [word _ le_rfl]
  refine ⟨?_, ?_, ?_, native.2.2.2, ?_, ?_, totalSteps_le q full⟩
  · have h := highCacheEnd_actual_fits q full hq
    exact outputData_toWord q full hq hl CB H _ native.1 h.1 h.2.1
  · change BitVec.ofNat bits _ = _
    rw [safe.2 _ le_rfl]
    simp only [initial, PA06A19PrepareBankNodeBit022.wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (pfit _ le_rfl), native.2.2.1]
  · intro address hprotected
    change BitVec.ofNat bits ((natRun rom containing (totalSteps q full) initial).heap address.toNat) = before.heap address
    rw [native.2.1 address.toNat hprotected]
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

theorem word_dynamicTrace_bound {bits : Nat} (q : Nat) (full : List (Finset (Fin q)))
    (rom : PhysicalROM) (containing : List PackingOp) (before : WordState bits) :
    (packingDynamicTrace rom containing (totalSteps q full) before).length ≤ 2400 * (preparedSize q full + 1) ^ 2 := by
  have h := packingDynamicTrace_length_le rom containing (totalSteps q full) before
  have hs := totalSteps_le q full
  omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareChildrenCache023
