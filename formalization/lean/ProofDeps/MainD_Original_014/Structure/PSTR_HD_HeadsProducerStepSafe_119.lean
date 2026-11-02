module

public import Structure.PSTR_HD_HeadsProducerInitialSafe_118

/-! Conditional INTERNAL consumer: actual controller<=40, SAME query body
from arbitrary post-controller registers, actual dispatch/return<=48. The
combined witness is an actual single uniform packingRun, not external calls. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem producer_next_common_safe {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (capWords heapWords budget : Nat) (queryBody : List PackingOp)
    (producer : InternalQueryProducer full used capWords heapWords budget queryBody (bits := bits))
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (stage : Nat) (state : WordState bits) (common : CommonScan full used capWords queryBody stage state)
    (hs : stage < full.length) (hb : 8 ≤ bits) (hq : 0 < q) (hqfit : Fits bits (q + 3))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + full.length))
    (hroom : endpoint full capWords bits + 10 + full.length < heapWords) :
    ∃ steps ≤ budget + 88,
      CommonScan full used capWords queryBody (stage + 1)
        (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps state) ∧
      (∀ clock < steps, AtSafe (callInput q full .query) (uniformHeadsProgram queryBody) heapWords
        (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) clock state)) := by
  let rom := callInput q full .query
  let whole := uniformHeadsProgram queryBody
  have hN : Fits bits full.length := (show full.length ≤ endpoint full capWords bits + 10 + full.length by omega).trans_lt he
  obtain ⟨ctrlSteps, hctrlSteps, controlled, safeCtrl⟩ := original_scan_iteration_safe full hl used ⟨stage, hs⟩ capWords
    (queryBody.length + 8) heapWords whole (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit state hb hq
    common.represented common.recorded common.pc common.active common.address common.old common.index (common.bad hs)
    hN hqfit bitmap hr he hroom
  dsimp only at controlled
  let atQuery := packingRun rom whole ctrlSteps state
  have hsnext : stage + 1 ≤ full.length := Nat.succ_le_of_lt hs
  obtain ⟨querySteps, hquerySteps, queryExit, safeQuery, prefixQuery⟩ := producer (stage + 1) hsnext atQuery
    controlled.2.2.1 controlled.1 controlled.2.1
  let queried := packingRun rom whole querySteps atQuery
  have kept : RecordedHeads (endpoint full capWords bits) q (encodeRank q (PSTRHeadScan.initialRank q full used))
      (scanPrefix q full used (stage + 1)) queried.heap := by
    have hlen := scanPrefix_length_le q full used (stage + 1)
    exact recorded_of_query_frame _ q _ _ atQuery.heap queried.heap controlled.2.2.2
      ((show endpoint full capWords bits + 10 + (scanPrefix q full used (stage + 1)).length ≤
        endpoint full capWords bits + 10 + full.length by omega).trans_lt he) (prefixQuery querySteps le_rfl).2
  have hbase : PSTRCountWorkspace.base q full capWords bits < heapWords := by
    have hbelow : PSTRCountWorkspace.base q full capWords bits ≤ endpoint full capWords bits := by
      unfold endpoint
      rw [PSTRQueryLayout.endpoint_eq]
      omega
    omega
  obtain ⟨returnSteps, hreturnSteps, returned, safeReturn⟩ := uniform_later_scan_safe full used (stage + 1) capWords heapWords queryBody hwords hpcfit
    queried hb hq (prefixQuery querySteps le_rfl).1 kept queryExit.pc queryExit.active (by omega) hsnext
    ((show q ≤ q + 3 by omega).trans_lt hqfit) hN hbase
  dsimp only at returned
  have safeTail := heads_safe_add rom whole heapWords querySteps returnSteps atQuery safeQuery safeReturn
  have safeAll := heads_safe_add rom whole heapWords ctrlSteps (querySteps + returnSteps) state safeCtrl safeTail
  refine ⟨ctrlSteps + (querySteps + returnSteps), by omega, ?_, safeAll⟩
  rw [run_add, run_add]
  refine ⟨returned.1, returned.2.1, returned.2.2.2.1, returned.2.2.2.2.1,
    returned.2.2.2.2.2.1, returned.2.2.2.2.2.2.1, returned.2.2.2.2.2.2.2.2, ?_⟩
  intro hbad
  simpa only [badAt] using returned.2.2.2.2.2.2.2.1.trans queryExit.bad

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
