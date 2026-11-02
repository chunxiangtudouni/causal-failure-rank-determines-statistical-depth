module

public import PaperProofs.Structure.PSTR_HD_HeadsOriginalIteration_078

/-! Original first query return -> actual64-instruction initialization of
the common scan state. Only the incoming query's actual value register is
specified; heads scratch is arbitrary and no reset is performed. N=0 allowed. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem original_initial_scan {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (capWords origin : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨0, used, false⟩ state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false)
    (hvalue : state.register .value = BitVec.ofNat bits (encodeRank q (PSTRHeadScan.initialRank q full used)))
    (hqfit : Fits bits (q + 3))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + full.length)) :
    let after := packingRun (callInput q full .query) whole 64 state
    after.pc = BitVec.ofNat bits (5 * (origin + 40)) ∧ after.halted = false ∧
    HeapRepresents q full capWords ⟨0, used, false⟩ after.heap ∧
    RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used 0) after.heap ∧
    after.register .old = BitVec.ofNat bits 0 ∧ after.register .index = BitVec.ofNat bits full.length ∧
    after.register .fresh = state.register .fresh ∧ after.register .address = BitVec.ofNat bits (endpoint full capWords bits) := by
  dsimp only
  let rom := callInput q full .query
  let E := endpoint full capWords bits
  let R := encodeRank q (PSTRHeadScan.initialRank q full used)
  let returned := packingRun rom whole 40 state
  have hN : Fits bits full.length := (show full.length ≤ E + 10 + full.length by omega).trans_lt he
  have hq2 : Fits bits (q + 2) := (show q + 2 ≤ q + 3 by omega).trans_lt hqfit
  have hR : Fits bits R := (initial_encoded_bound q full hl used).trans_lt hq2
  have he3 : Fits bits (E + 3) := (show E + 3 ≤ E + 10 + full.length by omega).trans_lt he
  have he8 : Fits bits (E + 8) := (show E + 8 ≤ E + 10 + full.length by omega).trans_lt he
  have he9 : Fits bits (E + 9) := (show E + 9 ≤ E + 10 + full.length by omega).trans_lt he
  have ht := query_return_prefix full ⟨0, used, false⟩ capWords origin whole hbound hcode hwords hpcfit state hb hq
    ((show q ≤ q + 3 by omega).trans_lt hqfit) (by change 0 ≤ full.length; exact Nat.zero_le _) hN rep hp ha
  have returned_pc : returned.pc = BitVec.ofNat bits (5 * (origin + 80)) := by simpa only [↓reduceIte] using ht.1
  have returned_rep : HeapRepresents q full capWords ⟨0, used, false⟩ returned.heap := by
    change HeapRepresents q full capWords ⟨0, used, false⟩ (packingRun rom whole 40 state).heap
    rw [ht.2.2.1]
    exact rep
  have returned_value : returned.register .value = BitVec.ofNat bits R := ht.2.2.2.1.trans hvalue
  have returned_addr : returned.register .address = BitVec.ofNat bits E := ht.2.2.2.2.2.2.2
  have hinit := initial_scan_entry full origin E R whole hbound hcode hwords hpcfit returned hb he8 hR hq2
    returned_pc ht.2.1 returned_addr returned_value
  have initialized_rep : HeapRepresents q full capWords ⟨0, used, false⟩ (packingRun rom whole 24 returned).heap := by
    rw [hinit.2.2.1]
    have hpure := headsInit_prefix_rep full ⟨0, used, false⟩ capWords returned hb hq returned_rep bitmap hr he9 returned_addr 21 (by decide)
    change HeapRepresents q full capWords ⟨0, used, false⟩ (executeOps rom headsInit returned).heap at hpure
    rw [(execute_headsInit rom E q R returned hb he3 hR hq2 returned_addr returned_value rfl).1] at hpure
    exact hpure
  rw [show 64 = 40 + 24 from rfl, run_add]
  refine ⟨hinit.1, hinit.2.1, initialized_rep, ?_, hinit.2.2.2.2.2.1.trans ht.2.2.2.2.1,
    hinit.2.2.2.2.2.2.2.1.trans ht.2.2.2.2.2.2.1,
    hinit.2.2.2.2.2.2.1.trans ht.2.2.2.2.2.1, hinit.2.2.2.2.2.2.2.2⟩
  simpa only [scanPrefix_zero] using hinit.2.2.2.1

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
