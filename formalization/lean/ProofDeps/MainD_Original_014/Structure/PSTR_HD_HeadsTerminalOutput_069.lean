module

public import Structure.PSTR_HD_HeadsTerminal_068

/-! ORIGINAL terminal output from actual SAME heads-program execution.
The recorded scan at stageN must be produced by the preceding real run;
this component proves the final11 actual instructions, not that producer. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM RawTreePreprocessingClaims
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem terminal_original_output {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (capWords : Nat) (queryBody : List PackingOp) (state : WordState bits)
    (hwords : WordsFit bits (packingCode (headsProgram queryBody)))
    (hpcfit : Fits bits (5 * (headsProgram queryBody).length))
    (hb : 0 < bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨full.length, used, false⟩ state.heap)
    (recorded : RecordedHeads (endpoint full capWords bits) q
      (encodeRank q (PSTRHeadScan.initialRank q full used)) (scanPrefix q full used full.length) state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (queryBody.length + 40))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits (endpoint full capWords bits))
    (hindex : state.register .index = BitVec.ofNat bits full.length)
    (hold : state.register .old = BitVec.ofNat bits full.length) (hN : Fits bits full.length)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + (scanPrefix q full used full.length).length))
    (hrank : Fits bits (encodeRank q (PSTRHeadScan.initialRank q full used)))
    (hcount : Fits bits (scanPrefix q full used full.length).length)
    (hentries : ∀ position < (scanPrefix q full used full.length).length,
      Fits bits ((scanPrefix q full used full.length).getD position 0)) :
    let after := packingRun (callInput q full .query) (headsProgram queryBody) 11 state
    after.halted = true ∧ (after.register .index).toNat = outputBase (endpoint full capWords bits) ∧
    HeapRepresents q full capWords ⟨full.length, used, false⟩ after.heap ∧
    heapWordsAt after.heap (outputBase (endpoint full capWords bits)) (headWords q full used).length = headWords q full used := by
  dsimp only
  let rom := callInput q full .query
  let whole := headsProgram queryBody
  let E := endpoint full capWords bits
  have hbound : queryBody.length + (tailAt queryBody.length).length ≤ whole.length := by
    change queryBody.length + (tailAt queryBody.length).length ≤ (headsProgram queryBody).length
    simpa only [tailAt_length, headsProgram_length] using (le_refl (queryBody.length + 111))
  have hexit := terminal_scan_exit rom whole queryBody.length E full.length _ hbound
    (heads_tail_code queryBody) hwords hpcfit state hp ha haddr hindex hold recorded.count hN
  have hhalt := terminal_scan_halt rom whole queryBody.length E full.length _ hbound
    (heads_tail_code queryBody) (headsProgram_length queryBody) hwords hpcfit state hp ha haddr hindex hold recorded.count hN
  have hheap : (packingRun rom whole 11 state).heap = (executeOps rom headsFinish state).heap := by
    rw [hhalt]
    exact hexit.2.2.1.trans (execute_headsFinish rom E _ state haddr recorded.count).1.symm
  have he9 : Fits bits (E + 9) := (show E + 9 ≤ E + 10 + (scanPrefix q full used full.length).length by omega).trans_lt he
  refine ⟨congrArg WordState.halted hhalt, ?_, ?_, ?_⟩
  · rw [hhalt]
    change ((packingRun rom whole 10 state).register .index).toNat = outputBase E
    rw [hexit.2.2.2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((show outputBase E ≤ E + 9 by unfold outputBase; omega).trans_lt he9)
  · rw [hheap]
    exact headsFinish_prefix_rep full ⟨full.length, used, false⟩ capWords state hb hq rep bitmap hr he9 haddr 7 (by decide)
  · rw [hheap]
    exact finish_original_headWords full hl used E state recorded haddr he hrank hcount hentries

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
