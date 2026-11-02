module

public import Structure.PSTR_HD_HeadsZeroInitialSafe_112
public import Structure.PSTR_HD_HeadsUniformInitialSafe_114

/-! q0 SAME uniform code first-return initialization, now with SAME-witness
every proper-clock safety. Actual dispatch5 then actual stage/init33 (bound41)
uses only original query ROM and endpoint46; N0 and arbitrary scratch covered. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_uniform_initial_scan_safe {bits : Nat} (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (heapWords : Nat) (queryBody : List PackingOp)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false)
    (hvalue : state.register .value = BitVec.ofNat bits (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)))
    (he : Fits bits (46 + 10 + full.length)) (hroom : 46 + 10 + full.length < heapWords) :
    ∃ steps ≤ 41,
    (let after := packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps state;
      after.pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) ∧ after.halted = false ∧
      HeapRepresents 0 full 0 ⟨0, used, false⟩ after.heap ∧
      RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) (scanPrefix 0 full used 0) after.heap ∧
      after.register .old = BitVec.ofNat bits 0 ∧ after.register .index = BitVec.ofNat bits full.length ∧
      after.register .fresh = state.register .fresh ∧ after.register .address = BitVec.ofNat bits 46) ∧
    (∀ clock < steps, AtSafe (callInput 0 full .query) (uniformHeadsProgram queryBody) heapWords
      (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) clock state)) := by
  let rom := callInput 0 full .query
  let whole := uniformHeadsProgram queryBody
  obtain ⟨d, hd, dispatch⟩ := containing_uniform_dispatch_safe rom whole queryBody.length 0 heapWords
    (by rw [uniformDispatch_length, uniformHeadsProgram_length]; omega) (uniform_dispatch_code queryBody)
    hwords hpcfit state hp ha hb (by unfold Fits; positivity) rfl
    (by simp [rom, callInput, RawTreePreprocessingClaims.rawIncidenceROM, PhysicalROM.words])
  dsimp only at dispatch
  obtain ⟨pcD, activeD, heapD, valueD, _oldD, freshD, _indexD, addressD, safeD⟩ := dispatch
  let entered := packingRun rom whole d state
  have repD : HeapRepresents 0 full 0 ⟨0, used, false⟩ entered.heap := by
    change HeapRepresents 0 full 0 ⟨0, used, false⟩ (packingRun rom whole d state).heap
    rw [heapD]
    exact rep
  have entered_pc : entered.pc = BitVec.ofNat bits (5 * ((queryBody.length + 8) + 31)) := by
    simpa only [↓reduceIte, Nat.add_assoc] using pcD
  have initialized := zero_original_initial_scan_safe full hl used (queryBody.length + 8) heapWords whole
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit entered hb repD entered_pc activeD
    addressD (valueD.trans hvalue) he hroom
  refine ⟨d + 33, by omega, ?_, ?_⟩
  · dsimp only
    rw [run_add]
    exact ⟨by simpa only [Nat.add_assoc] using initialized.1.1, initialized.1.2.1,
      initialized.1.2.2.1, initialized.1.2.2.2.1, initialized.1.2.2.2.2.1,
      initialized.1.2.2.2.2.2.1, initialized.1.2.2.2.2.2.2.1.trans freshD,
      initialized.1.2.2.2.2.2.2.2⟩
  · exact heads_safe_add rom whole heapWords d 33 state (fun clock hc => (safeD clock hc).1) initialized.2

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
