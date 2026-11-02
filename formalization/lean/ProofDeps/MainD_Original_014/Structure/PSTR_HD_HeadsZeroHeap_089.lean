module

public import Structure.PSTR_HD_HeadsUniformDispatch_080

/-! ORIGINAL q=0 heap bridges for the SHARED uniform controller. Metadata
and used/table obligations are genuinely empty; no tree/heap6 is read or
assumed. Physical stage/failed cells and query probe are derived from Rep. -/

@[expose] public section

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine PSTRWordSegments

theorem zero_packed_words (bits : Nat) (hb : 0 < bits) : packedCapacityWords 0 0 bits = 0 := by
  simp only [packedCapacityWords, Nat.zero_mul, Nat.zero_add]
  exact Nat.div_eq_of_lt (by omega)

theorem zero_rep_frame {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (old fresh : BitVec bits → BitVec bits) (rep : HeapRepresents 0 full 0 configuration old)
    (frame : ∀ physical < 6, fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical)) :
    HeapRepresents 0 full 0 configuration fresh := by
  have hlogical (address : Nat) (ha : address ≤ 1) : logicalHeap 0 0 fresh address = logicalHeap 0 0 old address := by
    have haddr : (BitVec.ofNat bits address).toNat ≤ 1 := (Nat.mod_le _ _).trans ha
    simp only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords]
    rw [frame (4 + (BitVec.ofNat bits address).toNat) (by omega)]
  rcases rep with ⟨h0, h1, h2, h3, hstage, hfailed, _hmetadata, _hused, _htable⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [frame 0 (by decide)]
    exact h0
  · rw [frame 1 (by decide)]
    exact h1
  · rw [frame 2 (by decide)]
    exact h2
  · rw [frame 3 (by decide)]
    exact h3
  · exact (hlogical 0 (by decide)).trans hstage
  · exact (hlogical 1 (by decide)).trans hfailed
  · intro position hposition
    simp [staticMetadata] at hposition
  · intro tool
    exact Fin.elim0 tool
  · intro hq
    omega

theorem zero_physical_stage_failed {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration heap) :
    (heap (BitVec.ofNat bits 4)).toNat = configuration.stage ∧
    (heap (BitVec.ofNat bits 5)).toNat = bit configuration.failed := by
  have hp : 256 ≤ 2 ^ bits := show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb
  have h1 : (BitVec.ofNat bits 1).toNat = 1 := Nat.mod_eq_of_lt (by omega)
  constructor
  · simpa only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords, BitVec.toNat_ofNat, Nat.zero_mod, Nat.add_zero] using rep.2.2.2.2.1
  · simpa only [logicalHeap, ↓reduceIte, dataHeap, physicalHeaderWords, h1] using rep.2.2.2.2.2.1

theorem zero_stage_word {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration heap) :
    heap (BitVec.ofNat bits 4) = BitVec.ofNat bits configuration.stage := by
  have h := congrArg (BitVec.ofNat bits) (zero_physical_stage_failed full configuration heap hb rep).1
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

theorem zero_packed_header {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (heap : BitVec bits → BitVec bits) (hb : 0 < bits) (rep : HeapRepresents 0 full 0 configuration heap) :
    heap (BitVec.ofNat bits 2) = BitVec.ofNat bits 0 := by
  have hNat := rep.2.2.1.trans (zero_packed_words bits hb)
  have h := congrArg (BitVec.ofNat bits) hNat
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using h

theorem zero_query_stageProbe {bits : Nat} (full : List (Finset (Fin 0))) (configuration : Configuration 0)
    (state : WordState bits) (hb : 8 ≤ bits) (rep : HeapRepresents 0 full 0 configuration state.heap) :
    let after := executeOps (callInput 0 full .query) stageProbe state
    after.register .old = BitVec.ofNat bits configuration.stage ∧ after.register .index = BitVec.ofNat bits full.length ∧
    after.register .value = state.register .value ∧ after.register .fresh = state.register .fresh ∧
    after.register .address = state.register .address ∧ after.heap = state.heap ∧ after.halted = state.halted :=
  execute_stageProbe (callInput 0 full .query) 0 configuration.stage full.length state
    (zero_packed_header full configuration state.heap (by omega) rep) (zero_stage_word full configuration state.heap hb rep) rfl

theorem zero_heads_room8192 {bits : Nat} (full : List (Finset (Fin 0))) :
    46 + full.length + 10 < physicalHeaderWords + packedCapacityWords 0 0 bits +
      8192 * (full.length + 0 + treeSize 0 full + 1) := by
  simp only [physicalHeaderWords, treeSize, ↓reduceIte, Nat.add_zero]
  omega

end PaperProofs.Structure.LaminarTree.PSTRHeadsRuntime
