module

public import Structure.PSTR_HD_HeadsZeroAdvance_090

/-! q=0 reaches this shared stage probe by the ACTUAL dispatch jump,
skipping the positive locator. Nine actual instructions read the real stage
and rawN, then branch to the same init80/common40 labels as positive q. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem zero_return_prefix {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (origin : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * (origin + 31))) (ha : state.halted = false)
    (hstage : configuration.stage ≤ full.length) (hN : Fits bits full.length) :
    let after := packingRun (callInput 0 full .query) whole 9 state
    after.pc = (if configuration.stage = 0 then BitVec.ofNat bits (5 * (origin + 80)) else BitVec.ofNat bits (5 * (origin + 40))) ∧
    after.halted = false ∧ after.heap = state.heap ∧ after.register .value = state.register .value ∧
    after.register .old = BitVec.ofNat bits configuration.stage ∧ after.register .fresh = state.register .fresh ∧
    after.register .index = BitVec.ofNat bits full.length ∧ after.register .address = state.register .address := by
  dsimp only
  let rom := callInput 0 full .query
  let probed := executeOps rom stageProbe state
  have probed_result := zero_query_stageProbe full configuration state hb rep
  have probed_pc : probed.pc = BitVec.ofNat bits (5 * (origin + 38)) := by
    change (executeOps rom stageProbe state).pc = _
    rw [executeOps_pc rom stageProbe state stageProbe_straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
  have probed_halt : probed.halted = false := probed_result.2.2.2.2.2.2.trans ha
  have run7 : packingRun rom whole 7 state = probed :=
    containing_stageProbe rom whole (origin + 31) (by have h := tailAt_length origin; rw [stageProbe_length]; omega)
      (stageProbe_tail_code whole origin hbound hcode) hwords hpcfit state hp ha
  have run2 := firstReturn_fetched rom whole origin configuration.stage
    (by have h := tailAt_length origin; omega) (hcode 38 (by change 38 < 111; decide)) (hcode 39 (by change 39 < 111; decide))
    hwords hpcfit probed probed_pc probed_halt probed_result.1 (hstage.trans_lt hN)
  rw [show 9 = 7 + 2 from rfl, run_add, run7, run2]
  exact ⟨rfl, probed_halt, probed_result.2.2.2.2.2.1, probed_result.2.2.1,
    probed_result.1, probed_result.2.2.2.1, probed_result.2.1, probed_result.2.2.2.2.1⟩

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
