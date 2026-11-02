module

public import Structure.PSTR_HD_HeadsZeroUniformInitialSafe_115

/-! Real positive later-return dispatch/locator/probe, with one witness for
the common-stage data and all proper-clock fetch/access. It preserves the
ENTIRE actual heap and the real ordered heads record; no query is invoked. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem uniform_later_scan_safe {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (stage capWords heapWords : Nat) (queryBody : List PackingOp)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨stage, used, false⟩ state.heap)
    (recorded : RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used stage) state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false)
    (hpos : 0 < stage) (hstage : stage ≤ full.length) (hqfit : Fits bits q) (hN : Fits bits full.length)
    (hroom : PSTRCountWorkspace.base q full capWords bits < heapWords) :
    ∃ steps ≤ 48,
    (let after := packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps state;
      after.pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) ∧ after.halted = false ∧ after.heap = state.heap ∧
      HeapRepresents q full capWords ⟨stage, used, false⟩ after.heap ∧
      RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
        (scanPrefix q full used stage) after.heap ∧ after.register .old = BitVec.ofNat bits stage ∧
      after.register .index = BitVec.ofNat bits full.length ∧ after.register .fresh = state.register .fresh ∧
      after.register .address = BitVec.ofNat bits (endpoint full capWords bits)) ∧
    (∀ clock < steps, AtSafe (callInput q full .query) (uniformHeadsProgram queryBody) heapWords
      (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) clock state)) := by
  let rom := callInput q full .query
  let whole := uniformHeadsProgram queryBody
  obtain ⟨d, hd, dispatch⟩ := containing_uniform_dispatch_safe rom whole queryBody.length q heapWords
    (by rw [uniformDispatch_length, uniformHeadsProgram_length]; omega) (uniform_dispatch_code queryBody)
    hwords hpcfit state hp ha hb hqfit rfl (by simp [rom, callInput, RawTreePreprocessingClaims.rawIncidenceROM, PhysicalROM.words])
  dsimp only at dispatch
  obtain ⟨pcD, activeD, heapD, _valueD, _oldD, freshD, _indexD, _addressD, safeD⟩ := dispatch
  let entered := packingRun rom whole d state
  have entered_rep : HeapRepresents q full capWords ⟨stage, used, false⟩ entered.heap := by
    change HeapRepresents q full capWords ⟨stage, used, false⟩ (packingRun rom whole d state).heap
    rw [heapD]
    exact rep
  have entered_pc : entered.pc = BitVec.ofNat bits (5 * (queryBody.length + 8)) := by
    simpa only [Nat.ne_of_gt hq, ↓reduceIte] using pcD
  have returned := query_return_prefix full ⟨stage, used, false⟩ capWords (queryBody.length + 8) whole
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit entered hb hq hqfit hstage hN entered_rep entered_pc activeD
  have returned_pc : (packingRun rom whole 40 entered).pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) := by
    simpa only [ne_of_gt hpos, ↓reduceIte] using returned.1
  have hheap : (packingRun rom whole 40 entered).heap = state.heap := returned.2.2.1.trans heapD
  have returnSafe (clock : Nat) (hc : clock < 40) : AtSafe rom whole heapWords (packingRun rom whole clock entered) :=
    (query_return_prefix_safe full ⟨stage, used, false⟩ capWords (queryBody.length + 8) heapWords whole
      (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit entered hb entered_rep entered_pc activeD hroom clock hc).1
  refine ⟨d + 40, by omega, ?_, heads_safe_add rom whole heapWords d 40 state (fun clock hc => (safeD clock hc).1) returnSafe⟩
  dsimp only
  rw [run_add]
  refine ⟨returned_pc, returned.2.1, hheap, ?_, ?_, returned.2.2.2.2.1,
    returned.2.2.2.2.2.2.1, returned.2.2.2.2.2.1.trans freshD, returned.2.2.2.2.2.2.2⟩
  · rw [hheap]; exact rep
  · rw [hheap]; exact recorded

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
