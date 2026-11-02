module

public import Structure.PSTR_HD_HeadsProducerStepSafe_119

/-! Conditional INTERNAL globalN induction over actual runs of the SAME
uniform instruction array. Induction composes the real step counts using
packingRun_add; it never creates packingInitial between stages or calls a
host query/update function. The actual-query producer premise remains open. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel

theorem producer_all_common_safe {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
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
    ∀ stage ≤ full.length, ∃ steps ≤ budget + 72 + stage * (budget + 88),
      CommonScan full used capWords queryBody stage
        (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps state) ∧
      (∀ clock < steps, AtSafe (callInput q full .query) (uniformHeadsProgram queryBody) heapWords
        (packingRun (callInput q full .query) (uniformHeadsProgram queryBody) clock state)) := by
  intro stage
  induction stage with
  | zero =>
    intro _hstage
    obtain ⟨steps, hsteps, common, safe⟩ := producer_initial_common_safe full hl used capWords heapWords budget queryBody producer
      hwords hpcfit state hb hq rep hp ha hqfit bitmap hr he hroom
    exact ⟨steps, by simpa only [Nat.zero_mul, Nat.add_zero] using hsteps, common, safe⟩
  | succ stage ih =>
    intro hstage
    have hs : stage < full.length := by omega
    obtain ⟨beforeSteps, hbefore, beforeCommon, beforeSafe⟩ := ih hs.le
    obtain ⟨nextSteps, hnext, nextCommon, nextSafe⟩ := producer_next_common_safe full hl used capWords heapWords budget queryBody producer
      hwords hpcfit stage _ beforeCommon hs hb hq hqfit bitmap hr he hroom
    have safeAll := heads_safe_add (callInput q full .query) (uniformHeadsProgram queryBody) heapWords
      beforeSteps nextSteps state beforeSafe nextSafe
    refine ⟨beforeSteps + nextSteps, ?_, ?_, safeAll⟩
    · rw [Nat.succ_mul]
      omega
    · rw [run_add]
      exact nextCommon

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
