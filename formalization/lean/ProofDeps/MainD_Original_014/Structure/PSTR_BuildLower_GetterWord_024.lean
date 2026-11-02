module

public import Structure.PSTR_BuildLower_GetterFrame_023

set_option maxHeartbeats 3000000
set_option maxRecDepth 30000

/-! Full-width actual Word getter with heap/fresh/base preservation at EVERY
clock through the same proved return. Raw-ROM transport uses actual decoded
accesses, never an assumed same-run or a supplied prefix-frame oracle. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput.GetterFrame
open IndexedRAM IndexedClosureRAM AlgorithmClaims RawTreePreprocessingClaims
  PackingMachine RawIncidenceLaminarRAM RawIncidenceScanSafety
open PA06A19PrepareBankNodeBit022

private theorem input_prefix (q : Nat) (full : List (Finset (Fin q))) (initialUsed : Finset (Fin q)) :
    PA06A19PrepareROM001.ROMPrefix (rawIncidenceROM q full)
      (CompactControllerClaims.controllerInput q full initialUsed) :=
  PA06A19PrepareROM001.inputTail_prefix _
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ initialUsed))))

/-- The old-range access proof is enough for the actual tail-bearing input;
no hypothesis of equal runs or a correct bit is introduced. -/
private theorem transport_nat (factor q : Nat) (full : List (Finset (Fin q)))
    (initialUsed : Finset (Fin q)) (containing : List PackingOp) (start heapWords : Nat)
    (before : NatState) (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (count : Nat) (result : NatResult factor q full containing start heapWords before node tool count)
    (k : Nat) (hk : k ≤ count) :
    natRun (CompactControllerClaims.controllerInput q full initialUsed) containing k before =
      natRun (rawIncidenceROM q full) containing k before := by
  apply PA06A19PrepareROM001.natRun_eq_of_romPrefix (input_prefix q full initialUsed) heapWords
  intro clock hclock _active op hd
  obtain ⟨index, hi, pc, access⟩ := (result.prefix_safe clock (by omega)).2.2.2 (by omega)
  have actualDecode : PackingOp.decode (natFetch containing
      (natRun (rawIncidenceROM q full) containing clock before).pc) = some (containing[index]) := by
    rw [pc, natFetch_body containing index hi, decode_encode]
  have hop : op = containing[index] := Option.some.inj (hd.symm.trans actualDecode)
  subst op
  exact access

theorem word_query_framed (factor q : Nat) (full : List (Finset (Fin q))) (hf : 16 ≤ factor)
    (initialUsed : Finset (Fin q)) (containing : List PackingOp) (start : Nat)
    (code : CodeAt containing start) (base heapWords : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (before : WordState (indexWidth factor full.length q))
    (hpc : before.pc.toNat = 5 * start) (hactive : before.halted = false)
    (hnode : (before.register .old).toNat = node.val)
    (htool : (before.register .fresh).toNat = tool.val)
    (hbase : (before.register .address).toNat = base)
    (cached : CachedWordNode full base node before.heap)
    (hroom : ordAddress full.length q base node.val < heapWords)
    (hheap : Fits (indexWidth factor full.length q) heapWords)
    (hend : Fits (indexWidth factor full.length q) (5 * (start + 46)))
    (hcode : WordsFit (indexWidth factor full.length q) (packingCode containing)) :
    ∃ count ≤ 35,
      let runtime := CompactControllerClaims.controllerInput q full initialUsed
      let after := packingRun runtime containing count before
      (after.register .value).toNat = bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) ∧
      after.register .fresh = before.register .fresh ∧ after.register .address = before.register .address ∧ after.heap = before.heap ∧
      after.pc.toNat = 5 * (start + 46) ∧ after.halted = false ∧
      (∀ k ≤ count,
        let current := packingRun runtime containing k before
        current.heap = before.heap ∧ current.register .fresh = before.register .fresh ∧
          current.register .address = before.register .address) ∧
      ∀ k < count,
        let state := packingRun runtime containing k before
        state.halted = false ∧ state.register .address = before.register .address ∧
        state.pc.toNat + 4 < (packingCode containing).length ∧
        ∃ op, PackingOp.decode (fetch containing state) = some op ∧ packingAccessFits runtime heapWords state op := by
  let bits := indexWidth factor full.length q
  let runtime := CompactControllerClaims.controllerInput q full initialUsed
  let initial := wordView before
  have regs : RegistersFit bits initial := fun register => (before.register register).isLt
  obtain ⟨count, bound, result, frames⟩ := nat_query_framed factor q full hf containing start code base heapWords node tool initial
    hpc hactive hnode htool hbase cached regs hroom hheap hend
  have eq (k : Nat) (hk : k ≤ count) :=
    transport_nat factor q full initialUsed containing start heapWords initial node tool count result k hk
  have word (k : Nat) (hk : k ≤ count) : packingRun runtime containing k before =
      (natRun (rawIncidenceROM q full) containing k initial).toWord bits := by
    rw [← wordView_toWord before]
    have hrun := natRun_toWord runtime containing initial k hcode (by
      intro c hc
      rw [eq c (by omega)]
      exact ⟨(result.prefix_safe c (by omega)).1, (result.prefix_safe c (by omega)).2.1⟩)
    exact hrun.trans (congrArg (NatState.toWord bits) (eq k hk))
  refine ⟨count, bound, ?_⟩
  dsimp only
  rw [word count le_rfl]
  refine ⟨?_, ?_, ?_, ?_, ?_, result.active, ?_, ?_⟩
  · change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ((result.prefix_safe count le_rfl).1 .value), result.value]
  · change BitVec.ofNat bits _ = _
    rw [result.fresh]
    simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change BitVec.ofNat bits _ = _
    rw [result.address]
    simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · funext address
    change BitVec.ofNat bits ((natRun (rawIncidenceROM q full) containing count initial).heap address.toNat) = before.heap address
    rw [result.heap]
    simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · change (BitVec.ofNat bits _).toNat = _
    rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (result.prefix_safe count le_rfl).2.1, result.pc]
  · intro k hk
    rw [word k hk]
    have frame := frames k hk
    refine ⟨?_, ?_, ?_⟩
    · funext address
      change BitVec.ofNat bits ((natRun (rawIncidenceROM q full) containing k initial).heap address.toNat) = before.heap address
      rw [frame.1]
      simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change BitVec.ofNat bits _ = _
      rw [frame.2.1]
      simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · change BitVec.ofNat bits _ = _
      rw [frame.2.2]
      simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  · intro k hk
    obtain ⟨index, hi, pc, access⟩ := (result.prefix_safe k hk.le).2.2.2 hk
    rw [word k hk.le]
    have pcWord : ((natRun (rawIncidenceROM q full) containing k initial).toWord bits).pc.toNat = 5 * index := by
      change (BitVec.ofNat bits _).toNat = _
      rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt (result.prefix_safe k hk.le).2.1, pc]
    refine ⟨(result.prefix_safe k hk.le).2.2.1, ?_, ?_, containing[index], ?_, ?_⟩
    · change BitVec.ofNat bits _ = _
      rw [result.prefix_address k hk.le]
      simp only [initial, wordView, bits, BitVec.ofNat_toNat, BitVec.setWidth_eq]
    · rw [pcWord, packingCode_length]
      omega
    · change PackingOp.decode (physicalFetch bits (packingCode containing)
        ((natRun (rawIncidenceROM q full) containing k initial).toWord bits).pc.toNat) = _
      rw [pcWord, physicalFetch_eq _ _ _ hcode]
      change PackingOp.decode (natFetch containing (5 * index)) = _
      rw [natFetch_body containing index hi, decode_encode]
    · apply physical_access_of_nat runtime heapWords _ _ (result.prefix_safe k hk.le).1
      cases hop : containing[index] with
      | base op =>
        exact PA06A19PrepareROM001.accessFits_of_romPrefix (input_prefix q full initialUsed) heapWords _ op
          (by simpa only [hop, NatAccessFits] using access)
      | arithmetic operation target left right => trivial
      | jumpIfZero condition target => trivial

end PaperProofs.Structure.LaminarTree.PSTRBuildLower.NodeInput.GetterFrame
