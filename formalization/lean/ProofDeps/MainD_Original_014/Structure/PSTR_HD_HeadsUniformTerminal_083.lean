module

public import Structure.PSTR_HD_HeadsUniformReturn_082

/-! Actual final11 instructions of the ONE uniform heads program yield the
ORIGINAL headWords and ORIGINAL final stageN/used/failed representation. All
value/count/index fits are derived, not new input assumptions or ROM fields. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM RawTreePreprocessingClaims
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem uniform_terminal_output {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (capWords : Nat) (queryBody : List PackingOp) (state : WordState bits)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (hb : 0 < bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨full.length, used, false⟩ state.heap)
    (recorded : RecordedHeads (endpoint full capWords bits) q
      (encodeRank q (PSTRHeadScan.initialRank q full used)) (scanPrefix q full used full.length) state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (queryBody.length + 48))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits (endpoint full capWords bits))
    (hindex : state.register .index = BitVec.ofNat bits full.length)
    (hold : state.register .old = BitVec.ofNat bits full.length) (hqfit : Fits bits (q + 3))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + full.length)) :
    let after := packingRun (callInput q full .query) (uniformHeadsProgram queryBody) 11 state
    after.halted = true ∧ (after.register .index).toNat = outputBase (endpoint full capWords bits) ∧
    HeapRepresents q full capWords ⟨full.length, used, false⟩ after.heap ∧
    heapWordsAt after.heap (outputBase (endpoint full capWords bits)) (headWords q full used).length = headWords q full used := by
  dsimp only
  let rom := callInput q full .query
  let whole := uniformHeadsProgram queryBody
  let E := endpoint full capWords bits
  let entries := scanPrefix q full used full.length
  have hlen : entries.length ≤ full.length := scanPrefix_length_le q full used full.length
  have hN : Fits bits full.length := (show full.length ≤ E + 10 + full.length by omega).trans_lt he
  have heEntries : Fits bits (E + 10 + entries.length) := (show E + 10 + entries.length ≤ E + 10 + full.length by omega).trans_lt he
  have he9 : Fits bits (E + 9) := (show E + 9 ≤ E + 10 + full.length by omega).trans_lt he
  have hrank : Fits bits (encodeRank q (PSTRHeadScan.initialRank q full used)) :=
    (initial_encoded_bound q full hl used).trans_lt ((show q + 2 ≤ q + 3 by omega).trans_lt hqfit)
  have hcount : Fits bits entries.length := hlen.trans_lt hN
  have hentries (position : Nat) (hposition : position < entries.length) : Fits bits (entries.getD position 0) := by
    have hm : entries.getD position 0 ∈ entries := by
      rw [List.getD_eq_getElem entries 0 hposition]
      exact List.getElem_mem hposition
    exact (scanPrefix_mem_lt q full used full.length _ hm).trans hN
  have hexit := terminal_scan_exit rom whole (queryBody.length + 8) E full.length entries.length
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit state hp ha haddr hindex hold recorded.count hN
  have hhalt := terminal_scan_halt rom whole (queryBody.length + 8) E full.length entries.length
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) (by rw [uniformHeadsProgram_length])
    hwords hpcfit state hp ha haddr hindex hold recorded.count hN
  have hheap : (packingRun rom whole 11 state).heap = (executeOps rom headsFinish state).heap := by
    rw [hhalt]
    exact hexit.2.2.1.trans (execute_headsFinish rom E entries.length state haddr recorded.count).1.symm
  refine ⟨congrArg WordState.halted hhalt, ?_, ?_, ?_⟩
  · rw [hhalt]
    change ((packingRun rom whole 10 state).register .index).toNat = outputBase E
    rw [hexit.2.2.2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((show outputBase E ≤ E + 9 by unfold outputBase; omega).trans_lt he9)
  · rw [hheap]
    exact headsFinish_prefix_rep full ⟨full.length, used, false⟩ capWords state hb hq rep bitmap hr he9 haddr 7 (by decide)
  · rw [hheap]
    exact finish_original_headWords full hl used E state recorded haddr heEntries hrank hcount hentries

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
