module

public import Structure.PSTR_HD_HeadsZeroProducerInitial_123

/-! CONDITIONAL INTERNAL q0 actual controller<=40, SAME actual query from
arbitrary post-controller registers, and real later-return<=17. One witness
has original common(stage+1) and all proper-clock safety; no reset occurs. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_producer_next_common_safe {bits : Nat} (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (heapWords budget : Nat) (queryBody : List PackingOp)
    (producer : InternalZeroQueryProducer full used heapWords budget queryBody (bits := bits))
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (stage : Nat) (state : WordState bits) (common : ZeroCommonScan full used queryBody stage state)
    (hs : stage < full.length) (hb : 8 ≤ bits)
    (he : Fits bits (46 + 10 + full.length)) (hroom : 46 + 10 + full.length < heapWords) :
    ∃ steps ≤ budget + 57,
      ZeroCommonScan full used queryBody (stage + 1)
        (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps state) ∧
      (∀ clock < steps, AtSafe (callInput 0 full .query) (uniformHeadsProgram queryBody) heapWords
        (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) clock state)) := by
  let rom := callInput 0 full .query
  let whole := uniformHeadsProgram queryBody
  have hN : Fits bits full.length := (show full.length ≤ 46 + 10 + full.length by omega).trans_lt he
  obtain ⟨ctrlSteps, hctrlSteps, controlled, safeCtrl⟩ := zero_original_scan_iteration_safe full hl used ⟨stage, hs⟩
    (queryBody.length + 8) heapWords whole (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit state hb
    common.represented common.recorded common.pc common.active common.address common.old common.index (common.bad hs) he hroom
  dsimp only at controlled
  let atQuery := packingRun rom whole ctrlSteps state
  have hsnext : stage + 1 ≤ full.length := Nat.succ_le_of_lt hs
  obtain ⟨querySteps, hquerySteps, queryExit, safeQuery, prefixQuery⟩ := producer (stage + 1) hsnext atQuery
    controlled.2.2.1 controlled.1 controlled.2.1
  let queried := packingRun rom whole querySteps atQuery
  have queryHeap : queried.heap = atQuery.heap := prefixQuery querySteps le_rfl
  have queryRep : HeapRepresents 0 full 0 ⟨stage + 1, used, false⟩ queried.heap := by
    rw [queryHeap]
    exact controlled.2.2.1
  have kept : RecordedHeads 46 0 (encodeRank 0 (PSTRHeadScan.initialRank 0 full used))
      (scanPrefix 0 full used (stage + 1)) queried.heap := by
    rw [queryHeap]
    exact controlled.2.2.2
  obtain ⟨returnSteps, hreturnSteps, returned, safeReturn⟩ := zero_uniform_later_scan_safe full used (stage + 1) heapWords queryBody
    hwords hpcfit queried hb queryRep kept queryExit.pc queryExit.active (by omega) hsnext hN (by omega)
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
