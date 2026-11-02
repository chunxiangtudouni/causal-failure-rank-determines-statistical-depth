module

public import Structure.PSTR_HD_HeadsGlobalSafe_120
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

def HeadsClockCorrect {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (heapWords : Nat) (state : WordState bits) : Prop :=
  state.halted = false ∧ state.pc.toNat + 4 < (packingCode whole).length ∧
    match PackingOp.decode (fetch whole state) with
    | none => fetch whole state = haltWords
    | some op => packingAccessFits rom heapWords state op

theorem heads_clock_of_atSafe {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (heapWords : Nat)
    (state : WordState bits) (safe : AtSafe rom whole heapWords state) :
    HeadsClockCorrect rom whole heapWords state := by
  obtain ⟨active, pc, op, decoded, access⟩ := safe
  exact ⟨active, pc, by rw [decoded]; exact access⟩

theorem heads_clock_at_halt {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (heapWords : Nat)
    (state : WordState bits) (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (hp : state.pc = BitVec.ofNat bits (5 * whole.length)) (ha : state.halted = false) :
    HeadsClockCorrect rom whole heapWords state := by
  have pc : state.pc.toNat = 5 * whole.length := by
    rw [hp, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt hpcfit
  have fetched : fetch whole state = natFetch whole (5 * whole.length) := by
    change physicalFetch bits (packingCode whole) _ = _
    rw [physicalFetch_eq bits _ _ hwords, pc]
    rfl
  refine ⟨ha, ?_, ?_⟩
  · rw [pc, packingCode_length]
    omega
  · rw [fetched, natFetch_halt, decode_halt]

theorem heads_dynamic_given_actual_query {bits q : Nat} (full : List (Finset (Fin q))) (hl : LaminarSchedule full)
    (used : Finset (Fin q)) (capWords heapWords budget constant : Nat) (queryBody : List PackingOp)
    (producer : InternalQueryProducer full used capWords heapWords budget queryBody (bits := bits))
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (hrom : ∀ region, WordsFit bits ((callInput q full .query).words region))
    (hfoot : Fits bits ((callInput q full .query).size + heapWords + (packingCode (uniformHeadsProgram queryBody)).length))
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords ⟨0, used, false⟩ heap) (hqfit : Fits bits (q + 3))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (he : Fits bits (endpoint full capWords bits + 10 + full.length))
    (hroom : endpoint full capWords bits + 10 + full.length < heapWords)
    (hbudget : budget ≤ constant * liveWork q (treeSize q full)) :
    ∃ steps ≤ (full.length + 1) * (budget + 88),
      DynamicRunCorrect heapWords (callInput q full .query) (uniformHeadsProgram queryBody) steps heap ∧
      callCost q full (uniformHeadsProgram queryBody) .query steps heap ≤
        (12 * constant + 5 * queryBody.length + 1665) * headWork q full ∧
      (let after := packingRun (callInput q full .query) (uniformHeadsProgram queryBody) steps (packingInitial heap);
        HeapRepresents q full capWords ⟨full.length, used, false⟩ after.heap ∧
        (after.register .index).toNat + (headWords q full used).length ≤ heapWords ∧
        heapWordsAt after.heap (after.register .index).toNat (headWords q full used).length = headWords q full used) := by
  let rom := callInput q full .query
  let whole := uniformHeadsProgram queryBody
  let initial : WordState bits := packingInitial heap
  let E := endpoint full capWords bits
  obtain ⟨commonSteps, hcommon, common, safeCommon⟩ := producer_all_common_safe full hl used capWords heapWords budget queryBody
    producer hwords hpcfit initial hb hq rep rfl rfl hqfit bitmap hr he hroom full.length le_rfl
  let terminal := packingRun rom whole commonSteps initial
  have final := uniform_terminal_output full hl used capWords queryBody terminal hwords hpcfit (by omega) hq
    common.represented common.recorded common.pc common.active common.address common.index common.old hqfit bitmap hr he
  have hsteps : commonSteps + 11 ≤ (full.length + 1) * (budget + 88) := by
    rw [Nat.succ_mul]
    omega
  have hN : Fits bits full.length := (show full.length ≤ E + 10 + full.length by omega).trans_lt he
  have he9 : Fits bits (E + 9) := (show E + 9 ≤ E + 10 + full.length by omega).trans_lt he
  have haltExit := terminal_scan_exit rom whole (queryBody.length + 8) E full.length (scanPrefix q full used full.length).length
    (uniform_tail_bound queryBody) (uniform_tail_code queryBody) hwords hpcfit terminal common.pc common.active common.address
    common.index common.old common.recorded.count hN
  have lastPC : (packingRun rom whole 10 terminal).pc = BitVec.ofNat bits (5 * whole.length) := by
    simpa only [whole, uniformHeadsProgram_length, Nat.add_assoc] using haltExit.1
  refine ⟨commonSteps + 11, hsteps, ?_, actual_heads_callCost_le full queryBody heap _ budget constant hsteps hbudget, ?_⟩
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
    refine ⟨final.2.2.1, ?_, ?_⟩
    · rw [final.2.1, headWords_scan q full hl used]
      have hlen := scanPrefix_length_le q full used full.length
      simp only [List.length_append, List.length_cons, List.length_nil]
      unfold outputBase
      omega
    · rw [final.2.1]
      exact final.2.2.2

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
