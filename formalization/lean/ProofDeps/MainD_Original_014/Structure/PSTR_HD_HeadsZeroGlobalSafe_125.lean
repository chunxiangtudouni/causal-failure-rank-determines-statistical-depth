module

public import Structure.PSTR_HD_HeadsZeroProducerStep_124

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

theorem zero_producer_all_common_safe {bits : Nat} (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (heapWords budget : Nat) (queryBody : List PackingOp)
    (producer : InternalZeroQueryProducer full used heapWords budget queryBody (bits := bits))
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hb : 8 ≤ bits)
    (rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ state.heap)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (he : Fits bits (46 + 10 + full.length)) (hroom : 46 + 10 + full.length < heapWords) :
    ∀ stage ≤ full.length, ∃ steps ≤ budget + 41 + stage * (budget + 57),
      ZeroCommonScan full used queryBody stage
        (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps state) ∧
      (∀ clock < steps, AtSafe (callInput 0 full .query) (uniformHeadsProgram queryBody) heapWords
        (packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) clock state)) := by
  intro stage
  induction stage with
  | zero =>
    intro _hstage
    obtain ⟨steps, hsteps, common, safe⟩ := zero_producer_initial_common_safe full hl used heapWords budget queryBody producer
      hwords hpcfit state hb rep hp ha he hroom
    exact ⟨steps, by simpa only [Nat.zero_mul, Nat.add_zero] using hsteps, common, safe⟩
  | succ stage ih =>
    intro hstage
    have hs : stage < full.length := by omega
    obtain ⟨beforeSteps, hbefore, beforeCommon, beforeSafe⟩ := ih hs.le
    obtain ⟨nextSteps, hnext, nextCommon, nextSafe⟩ := zero_producer_next_common_safe full hl used heapWords budget queryBody producer
      hwords hpcfit stage _ beforeCommon hs hb he hroom
    have safeAll := heads_safe_add (callInput 0 full .query) (uniformHeadsProgram queryBody) heapWords
      beforeSteps nextSteps state beforeSafe nextSafe
    refine ⟨beforeSteps + nextSteps, ?_, ?_, safeAll⟩
    · rw [Nat.succ_mul]
      omega
    · rw [run_add]
      exact nextCommon

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
