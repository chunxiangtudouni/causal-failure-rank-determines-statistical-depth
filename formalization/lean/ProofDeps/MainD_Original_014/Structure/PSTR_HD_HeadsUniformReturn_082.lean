module

public import Structure.PSTR_HD_HeadsUniformEntry_081

/-! An actual later query return reenters the common scan in <=48 real
uniform-program instructions. Only stage>0 distinguishes it from the real
first-return initialization. Query frame/record production remain upstream. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem uniform_later_scan {bits q : Nat} (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (stage capWords : Nat) (queryBody : List PackingOp)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨stage, used, false⟩ state.heap)
    (recorded : RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used stage) state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false)
    (hpos : 0 < stage) (hstage : stage ≤ full.length) (hqfit : Fits bits q) (hN : Fits bits full.length) :
    ∃ steps ≤ 48,
    let after := packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps state
    after.pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) ∧ after.halted = false ∧ after.heap = state.heap ∧
    HeapRepresents q full capWords ⟨stage, used, false⟩ after.heap ∧
    RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used stage) after.heap ∧
    after.register .old = BitVec.ofNat bits stage ∧ after.register .index = BitVec.ofNat bits full.length ∧
    after.register .fresh = state.register .fresh ∧ after.register .address = BitVec.ofNat bits (endpoint full capWords bits) := by
  let rom := callInput q full .query
  let whole := uniformHeadsProgram queryBody
  obtain ⟨d, hd, dispatch⟩ := uniform_dispatch_positive full queryBody hwords hpcfit state hp ha hb hq hqfit
  dsimp only at dispatch
  let entered := packingRun rom whole d state
  have entered_rep : HeapRepresents q full capWords ⟨stage, used, false⟩ entered.heap := by
    change HeapRepresents q full capWords ⟨stage, used, false⟩ (packingRun rom whole d state).heap
    rw [dispatch.2.2.1]
    exact rep
  have returned := query_return_prefix full ⟨stage, used, false⟩ capWords (queryBody.length + 8) whole
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit entered hb hq hqfit hstage hN
    entered_rep dispatch.1 dispatch.2.1
  have returned_pc : (packingRun rom whole 40 entered).pc = BitVec.ofNat bits (5 * (queryBody.length + 48)) := by
    simpa only [ne_of_gt hpos, ↓reduceIte] using returned.1
  have hheap : (packingRun rom whole 40 entered).heap = state.heap := returned.2.2.1.trans dispatch.2.2.1
  refine ⟨d + 40, by omega, ?_⟩
  dsimp only
  rw [run_add]
  refine ⟨returned_pc, returned.2.1, hheap, ?_, ?_, returned.2.2.2.2.1,
    returned.2.2.2.2.2.2.1, returned.2.2.2.2.2.1.trans dispatch.2.2.2.2.2.1, returned.2.2.2.2.2.2.2⟩
  · rw [hheap]
    exact rep
  · rw [hheap]
    exact recorded

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
