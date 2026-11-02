module

public import Structure.PSTR_HD_HeadsZeroQueryContract_122

/-! CONDITIONAL INTERNAL q0 first-query consumer. One actual query clock
and the real uniform initialization give common stage0 and all proper-clock
safety; no producer existence or original HeadExtraction claim is asserted. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_producer_initial_common_safe {bits : Nat} (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (heapWords budget : Nat) (queryBody : List PackingOp)
    (producer : InternalZeroQueryProducer full used heapWords budget queryBody (bits := bits))
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ state.heap)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (he : Fits bits (46 + 10 + full.length)) (hroom : 46 + 10 + full.length < heapWords) :
    ∃ steps ≤ budget + 41,
      ZeroCommonScan full used queryBody 0
        (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps state) ∧
      (∀ clock < steps, AtSafe (callInput 0 full .query) (uniformHeadsProgram queryBody) heapWords
        (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) clock state)) := by
  let rom := callInput 0 full .query
  let whole := uniformHeadsProgram queryBody
  obtain ⟨querySteps, hquerySteps, queryExit, safeQuery, prefixQuery⟩ := producer 0 (Nat.zero_le _) state rep hp ha
  let queried := packingRun rom whole querySteps state
  have queryRep : HeapRepresents 0 full 0 ⟨0, used, false⟩ queried.heap := by
    change HeapRepresents 0 full 0 ⟨0, used, false⟩ (packingRun rom whole querySteps state).heap
    rw [prefixQuery querySteps le_rfl]
    exact rep
  have queryRank : queried.register .value = BitVec.ofNat bits (encodeRank 0 (PSTRHeadScan.initialRank 0 full used)) := by
    simpa only [PSTRHeadScan.initialRank] using queryExit.rank
  obtain ⟨initSteps, hinitSteps, initialized, safeInit⟩ := zero_uniform_initial_scan_safe full hl used heapWords queryBody hwords hpcfit
    queried hb queryRep queryExit.pc queryExit.active queryRank he hroom
  dsimp only at initialized
  refine ⟨querySteps + initSteps, by omega, ?_, heads_safe_add rom whole heapWords querySteps initSteps state safeQuery safeInit⟩
  rw [run_add]
  refine ⟨initialized.1, initialized.2.1, initialized.2.2.1, initialized.2.2.2.1,
    initialized.2.2.2.2.1, initialized.2.2.2.2.2.1, initialized.2.2.2.2.2.2.2, ?_⟩
  intro hs
  simpa only [badAt] using initialized.2.2.2.2.2.2.1.trans queryExit.bad

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
