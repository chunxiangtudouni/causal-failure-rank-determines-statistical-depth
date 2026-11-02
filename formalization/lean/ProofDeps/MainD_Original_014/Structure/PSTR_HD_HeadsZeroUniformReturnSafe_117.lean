module

public import Structure.PSTR_HD_HeadsUniformReturnSafe_116

/-! q0 later-return counterpart in the SAME uniform whole program. Actual
dispatch5 plus stage return9 (exported bound17), original low6 representation,
all proper clocks safe and ENTIRE heap retained. No query body is assumed. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_uniform_later_scan_safe {bits : Nat} (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (stage heapWords : Nat) (queryBody : List PackingOp)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 ⟨stage, used, false⟩ state.heap)
    (recorded : RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) (scanPrefix 0 full used stage) state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false)
    (hpos : 0 < stage) (hstage : stage ≤ full.length) (hN : Fits bits full.length) (hroom : 6 ≤ heapWords) :
    ∃ steps ≤ 17,
    (let after := packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps state;
      after.pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) ∧ after.halted = false ∧ after.heap = state.heap ∧
      HeapRepresents 0 full 0 ⟨stage, used, false⟩ after.heap ∧
      RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) (scanPrefix 0 full used stage) after.heap ∧
      after.register .old = BitVec.ofNat bits stage ∧ after.register .index = BitVec.ofNat bits full.length ∧
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
  obtain ⟨pcD, activeD, heapD, _valueD, _oldD, freshD, _indexD, addressD, safeD⟩ := dispatch
  let entered := packingRun rom whole d state
  have entered_rep : HeapRepresents 0 full 0 ⟨stage, used, false⟩ entered.heap := by
    change HeapRepresents 0 full 0 ⟨stage, used, false⟩ (packingRun rom whole d state).heap
    rw [heapD]
    exact rep
  have entered_pc : entered.pc = BitVec.ofNat bits (5 * ((queryBody.length + 8) + 31)) := by
    simpa only [↓reduceIte, Nat.add_assoc] using pcD
  have returned := zero_return_prefix full ⟨stage, used, false⟩ (queryBody.length + 8) whole
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit entered hb entered_rep entered_pc activeD hstage hN
  have returned_pc : (packingRun rom whole 9 entered).pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) := by
    simpa only [ne_of_gt hpos, ↓reduceIte] using returned.1
  have hheap : (packingRun rom whole 9 entered).heap = state.heap := returned.2.2.1.trans heapD
  have returnSafe (clock : Nat) (hc : clock < 9) : AtSafe rom whole heapWords (packingRun rom whole clock entered) :=
    (zero_return_prefix_safe full ⟨stage, used, false⟩ (queryBody.length + 8) heapWords whole
      (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit entered hb entered_rep entered_pc activeD hroom clock hc).1
  refine ⟨d + 9, by omega, ?_, heads_safe_add rom whole heapWords d 9 state (fun clock hc => (safeD clock hc).1) returnSafe⟩
  dsimp only
  rw [run_add]
  refine ⟨returned_pc, returned.2.1, hheap, ?_, ?_, returned.2.2.2.2.1,
    returned.2.2.2.2.2.2.1, returned.2.2.2.2.2.1.trans freshD, returned.2.2.2.2.2.2.2.trans addressD⟩
  · rw [hheap]; exact rep
  · rw [hheap]; exact recorded

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
