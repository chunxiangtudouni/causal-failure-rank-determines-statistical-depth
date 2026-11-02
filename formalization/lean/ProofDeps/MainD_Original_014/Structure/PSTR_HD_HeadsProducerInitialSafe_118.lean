module

public import Structure.PSTR_HD_HeadsQueryContract_084
public import Structure.PSTR_HD_HeadsZeroUniformReturnSafe_117

/-! Conditional INTERNAL consumer of the pending actual-query producer:
first actual query + actual uniform initialization in the SAME whole run.
No implementation or original claim is concluded until that producer is proved. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem producer_initial_common_safe {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (capWords heapWords budget : Nat) (queryBody : List PackingOp)
    (producer : InternalQueryProducer full used capWords heapWords budget queryBody (bits := bits))
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨0, used, false⟩ state.heap)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (hqfit : Fits bits (q + 3))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + full.length))
    (hroom : endpoint full capWords bits + 10 + full.length < heapWords) :
    ∃ steps ≤ budget + 72,
      CommonScan full used capWords queryBody 0
        (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps state) ∧
      (∀ clock < steps, AtSafe (callInput q full .query) (uniformHeadsProgram queryBody) heapWords
        (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) clock state)) := by
  let rom := callInput q full .query
  let whole := uniformHeadsProgram queryBody
  obtain ⟨querySteps, hquerySteps, queryExit, safeQuery, prefixQuery⟩ := producer 0 (Nat.zero_le _) state rep hp ha
  let queried := packingRun rom whole querySteps state
  have queryRep : HeapRepresents q full capWords ⟨0, used, false⟩ queried.heap := (prefixQuery querySteps le_rfl).1
  have queryRank : queried.register .value = BitVec.ofNat bits (encodeRank q (PSTRHeadScan.initialRank q full used)) := by
    simpa only [PSTRHeadScan.initialRank] using queryExit.rank
  obtain ⟨initSteps, hinitSteps, initialized, safeInit⟩ := uniform_initial_scan_safe full hl used capWords heapWords queryBody hwords hpcfit queried hb hq
    queryRep queryExit.pc queryExit.active queryRank hqfit bitmap hr he hroom
  dsimp only at initialized
  refine ⟨querySteps + initSteps, by omega, ?_, heads_safe_add rom whole heapWords querySteps initSteps state safeQuery safeInit⟩
  rw [run_add]
  refine ⟨initialized.1, initialized.2.1, initialized.2.2.1, initialized.2.2.2.1,
    initialized.2.2.2.2.1, initialized.2.2.2.2.2.1, initialized.2.2.2.2.2.2.2, ?_⟩
  intro hs
  simpa only [badAt] using initialized.2.2.2.2.2.2.1.trans queryExit.bad

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
