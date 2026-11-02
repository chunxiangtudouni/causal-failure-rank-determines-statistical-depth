module

public import Structure.PSTR_HD_HeadsZeroGlobalSafe_125
public import Structure.PSTR_HD_HeadsCost_113

/-! CONDITIONAL INTERNAL consumer, never an implementation or existence
claim: an actual same-body query producer gives a SAME-witness real heads
run, original DynamicRunCorrect/callCost/headWords/final configuration. The
producer, original ROM/total room and preprocessor still require real proofs. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments
open PSTRCountKernel RawTreePreprocessingClaims
open PaperProofs.Common.Native.CompactPrice
open PaperProofs.Common.Native.CompactPrice.PSTRHeadScan

theorem zero_heads_dynamic_given_actual_query {bits : Nat} (full : List (Finset (Fin 0))) (hl : LaminarSchedule full)
    (used : Finset (Fin 0)) (heapWords budget constant : Nat) (queryBody : List PackingOp)
    (producer : InternalZeroQueryProducer full used heapWords budget queryBody (bits := bits))
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (hrom : ∀ region, WordsFit bits ((callInput 0 full .query).words region))
    (hfoot : Fits bits ((callInput 0 full .query).size + heapWords + (packingCode (uniformHeadsProgram queryBody)).length))
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (rep : HeapRepresents 0 full 0 ⟨0, used, false⟩ heap)
    (he : Fits bits (46 + 10 + full.length)) (hroom : 46 + 10 + full.length < heapWords)
    (hbudget : budget ≤ constant * liveWork 0 (treeSize 0 full)) :
    ∃ steps ≤ (full.length + 1) * (budget + 57),
      DynamicRunCorrect heapWords (callInput 0 full .query) (uniformHeadsProgram queryBody) steps heap ∧
      callCost 0 full (uniformHeadsProgram queryBody) .query steps heap ≤
        (12 * constant + 5 * queryBody.length + 1665) * headWork 0 full ∧
      (let after := packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps (packingInitial heap);
        HeapRepresents 0 full 0 ⟨full.length, used, false⟩ after.heap ∧
        (after.register .index).toNat + (headWords 0 full used).length ≤ heapWords ∧
        heapWordsAt after.heap (after.register .index).toNat (headWords 0 full used).length = headWords 0 full used) := by
  let rom := callInput 0 full .query
  let whole := uniformHeadsProgram queryBody
  let initial : WordState bits := packingInitial heap
  let E := 46
  obtain ⟨commonSteps, hcommon, common, safeCommon⟩ := zero_producer_all_common_safe full hl used heapWords budget queryBody
    producer hwords hpcfit initial hb rep rfl rfl he hroom full.length le_rfl
  let terminal := packingRun rom whole commonSteps initial
  have final := zero_uniform_terminal_output full hl used queryBody terminal hwords hpcfit hb
    common.represented common.recorded common.pc common.active common.address common.index common.old he
  have hsteps : commonSteps + 11 ≤ (full.length + 1) * (budget + 57) := by
    rw [Nat.succ_mul]
    omega
  have hN : Fits bits full.length := (show full.length ≤ E + 10 + full.length by omega).trans_lt he
  have he9 : Fits bits (E + 9) := (show E + 9 ≤ E + 10 + full.length by omega).trans_lt he
  have haltExit := terminal_scan_exit rom whole (queryBody.length + 8) E full.length (scanPrefix 0 full used full.length).length
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit terminal common.pc common.active common.address
    common.index common.old common.recorded.count hN
  have lastPC : (packingRun rom whole 10 terminal).pc = BitVec.ofNat bits (5 * whole.length) := by
    simpa only [whole, uniformHeadsProgram_length, Nat.add_assoc] using haltExit.1
  have hcoarse : commonSteps + 11 ≤ (full.length + 1) * (budget + 88) :=
    hsteps.trans (Nat.mul_le_mul_left _ (by omega))
  refine ⟨commonSteps + 11, hsteps, ?_, actual_heads_callCost_le full queryBody heap _ budget constant hcoarse hbudget, ?_⟩
  · refine ⟨hwords, hrom, hfoot, ?_, ?_⟩
    · rw [run_add]
      exact final.1
    · intro clock hc
      change HeadsClockCorrect rom whole heapWords (packingRun rom whole clock initial)
      by_cases hfirst : clock < commonSteps
      · exact heads_clock_of_atSafe rom whole heapWords _ (safeCommon clock hfirst)
      · have hclock : clock = commonSteps + (clock - commonSteps) := by omega
        rw [hclock, run_add]
        by_cases hlead : clock - commonSteps < 10
        · exact heads_clock_of_atSafe rom whole heapWords _
            (terminal_scan_prefix_safe rom whole (queryBody.length + 8) E full.length heapWords
              (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit terminal common.pc common.active
              common.address common.index common.old hN he9 (by omega) _ hlead).1
        · have heq : clock - commonSteps = 10 := by omega
          rw [heq]
          exact heads_clock_at_halt rom whole heapWords _ hwords hpcfit lastPC haltExit.2.1
  · dsimp only
    rw [run_add]
    refine ⟨final.2.1, ?_, ?_⟩
    · rw [final.2.2.1, headWords_scan 0 full hl used]
      have hlen := scanPrefix_length_le 0 full used full.length
      simp only [List.length_append, List.length_cons, List.length_nil]
      unfold outputBase
      omega
    · exact final.2.2.2.2

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
