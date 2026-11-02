module

public import Structure.PSTR_HD_HeadsOriginalIterationSafe_109

/-! Original first query return -> actual64-instruction initialization of
the common scan state. Only the incoming query's actual value register is
specified; heads scratch is arbitrary and no reset is performed. N=0 allowed. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem original_initial_scan_safe {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (capWords origin heapWords : Nat) (whole : List PackingOp)
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
    (he : Fits bits (endpoint full capWords bits + 10 + full.length))
    (hroom : endpoint full capWords bits + 10 + full.length < heapWords) :
    (let after := packingRun (callInput q full .query) whole 64 state;
    after.pc = BitVec.ofNat bits (5 * (origin + 40)) ∧ after.halted = false ∧
    HeapRepresents q full capWords ⟨0, used, false⟩ after.heap ∧
    RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used 0) after.heap ∧
    after.register .old = BitVec.ofNat bits 0 ∧ after.register .index = BitVec.ofNat bits full.length ∧
    after.register .fresh = state.register .fresh ∧ after.register .address = BitVec.ofNat bits (endpoint full capWords bits)) ∧
    (∀ clock < 64, AtSafe (callInput q full .query) whole heapWords
      (packingRun (callInput q full .query) whole clock state)) := by
  constructor
  · exact original_initial_scan full hl used capWords origin whole hbound hcode hwords hpcfit state hb hq rep hp ha hvalue hqfit bitmap hr he
  · let rom := callInput q full .query
    let E := endpoint full capWords bits
    let returned := packingRun rom whole 40 state
    have hN : Fits bits full.length := (show full.length ≤ E + 10 + full.length by omega).trans_lt he
    have ht := query_return_prefix full ⟨0, used, false⟩ capWords origin whole hbound hcode hwords hpcfit state hb hq
      ((show q ≤ q + 3 by omega).trans_lt hqfit) (by change 0 ≤ full.length; exact Nat.zero_le _) hN rep hp ha
    have returned_pc : returned.pc = BitVec.ofNat bits (5 * (origin + 80)) := by simpa only [↓reduceIte] using ht.1
    have returned_addr : returned.register .address = BitVec.ofNat bits E := ht.2.2.2.2.2.2.2
    have hbase : PSTRCountWorkspace.base q full capWords bits < heapWords := by
      have hbelow : PSTRCountWorkspace.base q full capWords bits ≤ E := by
        dsimp only [E, endpoint]
        rw [PSTRQueryLayout.endpoint_eq]
        omega
      omega
    have returnSafe (clock : Nat) (hc : clock < 40) : AtSafe rom whole heapWords (packingRun rom whole clock state) :=
      (query_return_prefix_safe full ⟨0, used, false⟩ capWords origin heapWords whole hbound hcode hwords hpcfit
        state hb rep hp ha hbase clock hc).1
    have initSafe (clock : Nat) (hc : clock < 24) : AtSafe rom whole heapWords (packingRun rom whole clock returned) :=
      (initial_prefix_safe full origin E heapWords whole hbound hcode hwords hpcfit returned hb
        ((show E + 8 ≤ E + 10 + full.length by omega).trans_lt he) (by omega) returned_addr returned_pc ht.2.1 clock hc).1
    exact heads_safe_add rom whole heapWords 40 24 state returnSafe initSafe

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
