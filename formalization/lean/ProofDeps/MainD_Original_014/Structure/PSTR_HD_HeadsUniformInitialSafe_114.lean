module

public import Structure.PSTR_HD_HeadsOriginalInitialSafe_111
public import Structure.PSTR_HD_HeadsUniformEntry_081

/-! Positive-q actual uniform dispatch then original64op initialization,
with ONE clock witness for data and EVERY proper-clock safety. Query body
occurs once atPC0; the input state is its actual active return at queryEnd. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem uniform_initial_scan_safe {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (capWords heapWords : Nat) (queryBody : List PackingOp)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨0, used, false⟩ state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false)
    (hvalue : state.register .value = BitVec.ofNat bits (encodeRank q (PSTRHeadScan.initialRank q full used)))
    (hqfit : Fits bits (q + 3))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + full.length))
    (hroom : endpoint full capWords bits + 10 + full.length < heapWords) :
    ∃ steps ≤ 72,
    (let after := packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps state;
      after.pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) ∧ after.halted = false ∧
      HeapRepresents q full capWords ⟨0, used, false⟩ after.heap ∧
      RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
        (scanPrefix q full used 0) after.heap ∧ after.register .old = BitVec.ofNat bits 0 ∧
      after.register .index = BitVec.ofNat bits full.length ∧ after.register .fresh = state.register .fresh ∧
      after.register .address = BitVec.ofNat bits (endpoint full capWords bits)) ∧
    (∀ clock < steps, AtSafe (callInput q full .query) (uniformHeadsProgram queryBody) heapWords
      (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) clock state)) := by
  let rom := callInput q full .query
  let whole := uniformHeadsProgram queryBody
  obtain ⟨d, hd, dispatch⟩ := containing_uniform_dispatch_safe rom whole queryBody.length q heapWords
    (by rw [uniformDispatch_length, uniformHeadsProgram_length]; omega) (uniform_dispatch_code queryBody)
    hwords hpcfit state hp ha hb ((show q ≤ q + 3 by omega).trans_lt hqfit) rfl
    (by simp [rom, callInput, RawTreePreprocessingClaims.rawIncidenceROM, PhysicalROM.words])
  dsimp only at dispatch
  obtain ⟨pcD, activeD, heapD, valueD, _oldD, freshD, _indexD, _addressD, safeD⟩ := dispatch
  let entered := packingRun rom whole d state
  have repD : HeapRepresents q full capWords ⟨0, used, false⟩ entered.heap := by
    change HeapRepresents q full capWords ⟨0, used, false⟩ (packingRun rom whole d state).heap
    rw [heapD]
    exact rep
  have entered_pc : entered.pc = BitVec.ofNat bits (5 * (queryBody.length + 8)) := by
    simpa only [Nat.ne_of_gt hq, ↓reduceIte] using pcD
  have initialized := original_initial_scan_safe full hl used capWords (queryBody.length + 8) heapWords whole
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit entered hb hq repD entered_pc activeD
    (valueD.trans hvalue) hqfit bitmap hr he hroom
  refine ⟨d + 64, by omega, ?_, ?_⟩
  · dsimp only
    rw [run_add]
    exact ⟨by simpa only [Nat.add_assoc] using initialized.1.1, initialized.1.2.1,
      initialized.1.2.2.1, initialized.1.2.2.2.1, initialized.1.2.2.2.2.1,
      initialized.1.2.2.2.2.2.1, initialized.1.2.2.2.2.2.2.1.trans freshD,
      initialized.1.2.2.2.2.2.2.2⟩
  · exact heads_safe_add rom whole heapWords d 64 state (fun clock hc => (safeD clock hc).1) initialized.2

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
