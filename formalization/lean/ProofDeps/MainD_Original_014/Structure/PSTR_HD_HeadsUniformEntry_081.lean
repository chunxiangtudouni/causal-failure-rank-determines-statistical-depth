module

public import Structure.PSTR_HD_HeadsUniformDispatch_080

/-! Actual uniform-dispatch and ORIGINAL first-return initialization are
connected in the SAME uniformHeadsProgram. No reset or second query body is
inserted. This is a post-query entry component, not a supplied query producer. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem uniform_dispatch_code (queryBody : List PackingOp) :
    ∀ i (hi : i < (uniformDispatch queryBody.length).length),
      (uniformHeadsProgram queryBody)[queryBody.length + i]'(by rw [uniformHeadsProgram_length, uniformDispatch_length] at *; omega) =
        (uniformDispatch queryBody.length)[i] := by
  intro i hi
  exact PSTRCountKernel.middle_get queryBody (uniformDispatch queryBody.length) (tailAt (queryBody.length + 8)) i hi

theorem uniform_tail_bound (queryBody : List PackingOp) :
    (queryBody.length + 8) + (tailAt (queryBody.length + 8)).length ≤ (uniformHeadsProgram queryBody).length := by
  rw [tailAt_length, uniformHeadsProgram_length]

theorem uniform_dispatch_positive {bits q : Nat} (full : List (Finset (Fin q))) (queryBody : List PackingOp)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false)
    (hb : 8 ≤ bits) (hq : 0 < q) (hqfit : Fits bits q) :
    ∃ steps ≤ 8,
    let after := packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps state
    after.pc = BitVec.ofNat bits (5 * (queryBody.length + 8)) ∧ after.halted = false ∧ after.heap = state.heap ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
    after.register .address = BitVec.ofNat bits 46 := by
  obtain ⟨steps, hsteps, result⟩ := containing_uniform_dispatch (callInput q full .query) (uniformHeadsProgram queryBody)
    queryBody.length q (by rw [uniformDispatch_length, uniformHeadsProgram_length]; omega)
    (uniform_dispatch_code queryBody) hwords hpcfit state hp ha hb hqfit rfl
  exact ⟨steps, hsteps, by simpa only [ne_of_gt hq, ↓reduceIte] using result⟩

theorem uniform_initial_scan {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (capWords : Nat) (queryBody : List PackingOp)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨0, used, false⟩ state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false)
    (hvalue : state.register .value = BitVec.ofNat bits (encodeRank q (PSTRHeadScan.initialRank q full used)))
    (hqfit : Fits bits (q + 3))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + full.length)) :
    ∃ steps ≤ 72,
    let after := packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps state
    after.pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) ∧ after.halted = false ∧
    HeapRepresents q full capWords ⟨0, used, false⟩ after.heap ∧
    RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used 0) after.heap ∧
    after.register .old = BitVec.ofNat bits 0 ∧ after.register .index = BitVec.ofNat bits full.length ∧
    after.register .fresh = state.register .fresh ∧ after.register .address = BitVec.ofNat bits (endpoint full capWords bits) := by
  let rom := callInput q full .query
  let whole := uniformHeadsProgram queryBody
  obtain ⟨d, hd, dispatch⟩ := uniform_dispatch_positive full queryBody hwords hpcfit state hp ha hb hq
    ((show q ≤ q + 3 by omega).trans_lt hqfit)
  dsimp only at dispatch
  let entered := packingRun rom whole d state
  have entered_rep : HeapRepresents q full capWords ⟨0, used, false⟩ entered.heap := by
    change HeapRepresents q full capWords ⟨0, used, false⟩ (packingRun rom whole d state).heap
    rw [dispatch.2.2.1]
    exact rep
  have initialized := original_initial_scan full hl used capWords (queryBody.length + 8) whole
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit entered hb hq entered_rep dispatch.1 dispatch.2.1
    (dispatch.2.2.2.1.trans hvalue) hqfit bitmap hr he
  refine ⟨d + 64, by omega, ?_⟩
  dsimp only
  rw [run_add]
  exact ⟨initialized.1, initialized.2.1, initialized.2.2.1, initialized.2.2.2.1,
    initialized.2.2.2.2.1, initialized.2.2.2.2.2.1,
    initialized.2.2.2.2.2.2.1.trans dispatch.2.2.2.2.2.1, initialized.2.2.2.2.2.2.2⟩

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
