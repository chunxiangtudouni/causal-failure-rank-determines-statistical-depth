module

public import Structure.PSTR_HD_HeadsZeroUniformInitial_098

/-! ORIGINAL q0 final11 actual instructions of the SAME uniform heads code:
true HALT, actual base54, exact headWords, stageN/used/failed retained. All
rank/count/entry fits and physical output room are derived from original bounds. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open RawTreePreprocessingClaims PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_uniform_terminal_output {bits : Nat} (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (queryBody : List PackingOp) (state : WordState bits)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 ⟨full.length, used, false⟩ state.heap)
    (recorded : RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) (scanPrefix 0 full used full.length) state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (queryBody.length + 48))) (ha : state.halted = false)
    (haddr : state.register .address = BitVec.ofNat bits 46)
    (hindex : state.register .index = BitVec.ofNat bits full.length) (hold : state.register .old = BitVec.ofNat bits full.length)
    (he : Fits bits (46 + 10 + full.length)) :
    let after := packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) 11 state
    after.halted = true ∧ HeapRepresents 0 full 0 ⟨full.length, used, false⟩ after.heap ∧
    (after.register .index).toNat = outputBase 46 ∧
    (after.register .index).toNat + (headWords 0 full used).length ≤
      physicalHeaderWords + packedCapacityWords 0 0 bits + 8192 * (full.length + 0 + treeSize 0 full + 1) ∧
    heapWordsAt after.heap (after.register .index).toNat (headWords 0 full used).length = headWords 0 full used := by
  dsimp only
  let rom := callInput 0 full .query
  let whole := uniformHeadsProgram queryBody
  let entries := scanPrefix 0 full used full.length
  have hpow : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have hq2 : Fits bits 2 := by unfold Fits; omega
  have hrank : Fits bits (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) :=
    (initial_encoded_bound 0 full hl used).trans_lt hq2
  have hlen : entries.length ≤ full.length := scanPrefix_length_le 0 full used full.length
  have hN : Fits bits full.length := (show full.length ≤ 46 + 10 + full.length by omega).trans_lt he
  have hcount : Fits bits entries.length := hlen.trans_lt hN
  have heEntries : Fits bits (46 + 10 + entries.length) := (show 46 + 10 + entries.length ≤ 46 + 10 + full.length by omega).trans_lt he
  have he9 : Fits bits (46 + 9) := (show 46 + 9 ≤ 46 + 10 + full.length by omega).trans_lt he
  have hentries (position : Nat) (hposition : position < entries.length) : Fits bits (entries.getD position 0) := by
    have hm : entries.getD position 0 ∈ entries := by
      rw [List.getD_eq_getElem entries 0 hposition]
      exact List.getElem_mem hposition
    exact (scanPrefix_mem_lt 0 full used full.length _ hm).trans hN
  have hexit := terminal_scan_exit rom whole (queryBody.length + 8) 46 full.length entries.length
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit state hp ha haddr hindex hold recorded.count hN
  have hhalt := terminal_scan_halt rom whole (queryBody.length + 8) 46 full.length entries.length
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) (by rw [uniformHeadsProgram_length])
    hwords hpcfit state hp ha haddr hindex hold recorded.count hN
  have hheap : (packingRun rom whole 11 state).heap = (executeOps rom headsFinish state).heap := by
    rw [hhalt]
    exact hexit.2.2.1.trans (execute_headsFinish rom 46 entries.length state haddr recorded.count).1.symm
  have hbase : ((packingRun rom whole 11 state).register .index).toNat = outputBase 46 := by
    rw [hhalt]
    change ((packingRun rom whole 10 state).register .index).toNat = outputBase 46
    rw [hexit.2.2.2, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((show outputBase 46 ≤ 46 + 9 by unfold outputBase; omega).trans_lt he9)
  refine ⟨congrArg WordState.halted hhalt, ?_, hbase, ?_, ?_⟩
  · rw [hheap]
    exact zero_finish_prefix_rep full ⟨full.length, used, false⟩ state rep he9 haddr 7 (by decide)
  · rw [hbase, headWords_scan 0 full hl used]
    have hc := scanPrefix_length_le 0 full used full.length
    have hroom := zero_heads_room8192 full (bits := bits)
    simp only [List.length_append, List.length_cons, List.length_nil]
    unfold outputBase
    omega
  · rw [hbase, hheap]
    exact finish_original_headWords full hl used 46 state recorded haddr heEntries hrank hcount hentries

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
