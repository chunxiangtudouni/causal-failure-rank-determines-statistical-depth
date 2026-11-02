module

public import PaperProofs.Structure.PSTR_HD_HeadsFrames_065

/-! Actual query-return tail prefix:31 endpoint instructions,7 real-stage
instructions,2 real stage0-branch instructions. The incoming state may have
arbitrary reply registers; actual heap metadata produces the control values. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem query_return_prefix {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords origin : Nat) (whole : List PackingOp)
    (hbound : origin + (tailAt origin).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (tailAt origin).length), whole[origin + i]'(by omega) = (tailAt origin)[i])
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hb : 8 ≤ bits) (hq : 0 < q) (hqfit : Fits bits q)
    (hstage : configuration.stage ≤ full.length) (hN : Fits bits full.length)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let after := packingRun (callInput q full .query) whole 40 state
    after.pc = (if configuration.stage = 0 then BitVec.ofNat bits (5 * (origin + 80))
      else BitVec.ofNat bits (5 * (origin + 40))) ∧
    after.halted = false ∧ after.heap = state.heap ∧
    after.register .value = state.register .value ∧
    after.register .old = BitVec.ofNat bits configuration.stage ∧
    after.register .fresh = state.register .fresh ∧
    after.register .index = BitVec.ofNat bits full.length ∧
    after.register .address = BitVec.ofNat bits (endpoint full capWords bits) := by
  dsimp only
  let rom := callInput q full .query
  let located := executeOps rom endpointProgram state
  let probed := executeOps rom stageProbe located
  have located_result := execute_endpoint full .query configuration capWords state hb hq hqfit rep
  have located_pc : located.pc = BitVec.ofNat bits (5 * (origin + 31)) := by
    change (executeOps rom endpointProgram state).pc = _
    rw [executeOps_pc rom endpointProgram state endpointProgram_straight, hp, BitVec.ofNat_add_ofNat]
    congr 1
  have located_halt : located.halted = false := located_result.2.2.2.2.2.2.trans ha
  have located_rep : HeapRepresents q full capWords configuration located.heap := by
    rw [located_result.2.2.2.2.2.1]
    exact rep
  have probed_result := query_stageProbe full configuration capWords located hq located_rep
  have probed_pc : probed.pc = BitVec.ofNat bits (5 * (origin + 38)) := by
    change (executeOps rom stageProbe located).pc = _
    rw [executeOps_pc rom stageProbe located stageProbe_straight, located_pc, BitVec.ofNat_add_ofNat]
    congr 1
  have probed_halt : probed.halted = false := probed_result.2.2.2.2.2.2.trans located_halt
  have run31 : packingRun rom whole 31 state = located :=
    containing_endpoint rom whole origin (by have h := tailAt_length origin; rw [endpointProgram_length]; omega)
      (endpoint_tail_code whole origin hbound hcode) hwords hpcfit state hp ha
  have run7 : packingRun rom whole 7 located = probed :=
    containing_stageProbe rom whole (origin + 31) (by have h := tailAt_length origin; rw [stageProbe_length]; omega)
      (stageProbe_tail_code whole origin hbound hcode) hwords hpcfit located located_pc located_halt
  have run38 : packingRun rom whole 38 state = probed := by
    rw [show 38 = 31 + 7 from rfl, run_add, run31, run7]
  have run2 := firstReturn_fetched rom whole origin configuration.stage
    (by have h := tailAt_length origin; omega)
    (hcode 38 (by change 38 < 111; decide)) (hcode 39 (by change 39 < 111; decide))
    hwords hpcfit probed probed_pc probed_halt probed_result.1 (hstage.trans_lt hN)
  rw [show 40 = 38 + 2 from rfl, run_add, run38, run2]
  refine ⟨rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact probed_halt
  · exact probed_result.2.2.2.2.2.1.trans located_result.2.2.2.2.2.1
  · exact probed_result.2.2.1.trans located_result.2.1
  · exact probed_result.1
  · exact probed_result.2.2.2.1.trans located_result.2.2.2.1
  · exact probed_result.2.1
  · exact probed_result.2.2.2.2.1.trans located_result.1

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
