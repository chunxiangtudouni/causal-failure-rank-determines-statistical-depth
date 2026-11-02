module

public import Structure.PSTR_HD_HeadsZeroOriginalIteration_095
public import Structure.PSTR_HD_HeadsUniformEntry_081

/-! The actual q0 uniform dispatch skips ONLY the positive locator, then
runs the shared real stage probe/branch. All steps stay in ONE uniform code
array/QUERY ROM and preserve the actual incoming reply and heap. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem uniform_dispatch_zero {bits : Nat} (full : List (Finset (Fin 0))) (queryBody : List PackingOp)
    (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false) (hb : 8 ≤ bits) :
    ∃ steps ≤ 8,
    let after := packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps state
    after.pc = BitVec.ofNat bits (5 * (queryBody.length + 39)) ∧ after.halted = false ∧ after.heap = state.heap ∧
    after.register .value = state.register .value ∧ after.register .old = state.register .old ∧
    after.register .fresh = state.register .fresh ∧ after.register .index = state.register .index ∧
    after.register .address = BitVec.ofNat bits 46 := by
  obtain ⟨steps, hsteps, result⟩ := containing_uniform_dispatch (callInput 0 full .query) (uniformHeadsProgram queryBody)
    queryBody.length 0 (by rw [uniformDispatch_length, uniformHeadsProgram_length]; omega)
    (uniform_dispatch_code queryBody) hwords hpcfit state hp ha hb (by unfold Fits; positivity) rfl
  exact ⟨steps, hsteps, by simpa only [↓reduceIte] using result⟩

theorem zero_uniform_return {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (queryBody : List PackingOp) (hwords : WordsFit bits (packingCode (uniformHeadsProgram queryBody)))
    (hpcfit : Fits bits (5 * (uniformHeadsProgram queryBody).length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * queryBody.length)) (ha : state.halted = false)
    (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap)
    (hs : configuration.stage ≤ full.length) (hN : Fits bits full.length) :
    ∃ steps ≤ 17,
    let after := packingRun (callInput 0 full .query) (uniformHeadsProgram queryBody) steps state
    after.pc = (if configuration.stage = 0 then BitVec.ofNat bits (5 * (queryBody.length + 88)) else BitVec.ofNat bits (5 * (queryBody.length + 48))) ∧
    after.halted = false ∧ after.heap = state.heap ∧ after.register .value = state.register .value ∧
    after.register .old = BitVec.ofNat bits configuration.stage ∧ after.register .fresh = state.register .fresh ∧
    after.register .index = BitVec.ofNat bits full.length ∧ after.register .address = BitVec.ofNat bits 46 := by
  let rom := callInput 0 full .query
  let whole := uniformHeadsProgram queryBody
  obtain ⟨d, hd, dispatch⟩ := uniform_dispatch_zero full queryBody hwords hpcfit state hp ha hb
  dsimp only at dispatch
  let entered := packingRun rom whole d state
  have entered_rep : HeapRepresents 0 full 0 configuration entered.heap := by
    change HeapRepresents 0 full 0 configuration (packingRun rom whole d state).heap
    rw [dispatch.2.2.1]
    exact rep
  have returned := zero_return_prefix full configuration (queryBody.length + 8) whole (uniform_tail_bound queryBody)
    (uniform_tail_code queryBody) hwords hpcfit entered hb entered_rep dispatch.1 dispatch.2.1 hs hN
  refine ⟨d + 9, by omega, ?_⟩
  dsimp only
  rw [run_add]
  exact ⟨returned.1, returned.2.1, returned.2.2.1.trans dispatch.2.2.1,
    returned.2.2.2.1.trans dispatch.2.2.2.1, returned.2.2.2.2.1,
    returned.2.2.2.2.2.1.trans dispatch.2.2.2.2.2.1, returned.2.2.2.2.2.2.1,
    returned.2.2.2.2.2.2.2.trans dispatch.2.2.2.2.2.2.2⟩

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
