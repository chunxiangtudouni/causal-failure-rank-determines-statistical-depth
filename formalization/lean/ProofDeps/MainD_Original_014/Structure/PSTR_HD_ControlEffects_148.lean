module

public import Structure.PSTR_HD_ControlPrograms_147

/-! Original positive-q correct and no-tool error semantics for the real
controls-only8/6. Reuse the mature bump/fail representation theorems; the
same actual one-store heaps give every-prefix capacity/table/high frames. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRReplyControls
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PSTRSelectedError

structure HeapEffects {bits q : Nat} (full : List (Finset (Fin q))) (capWords : Nat)
    (before after : BitVec bits → BitVec bits) : Prop where
  capacity : CapacityPrefixBounded q capWords (logicalHeap q capWords after)
  table : ∀ address < tableWords full.length q (treeSize q full), logicalHeap q capWords after address = logicalHeap q capWords before address
  high : ∀ physical, Fits bits physical → 6 + packedCapacityWords q capWords bits ≤ physical →
    after (BitVec.ofNat bits physical) = before (BitVec.ofNat bits physical)

theorem initial_effects {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap) : HeapEffects full capWords heap heap :=
  ⟨(rep.2.2.2.2.2.2.2.2 hq).2, fun _ _ => rfl, fun _ _ _ => rfl⟩

theorem effects_from_frames {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (before after : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration before)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (capacityFrame : ∀ address < capWords, logicalHeap q capWords after address = logicalHeap q capWords before address)
    (highFrame : ∀ physical, Fits bits physical → 6 + packedCapacityWords q capWords bits ≤ physical →
      after (BitVec.ofNat bits physical) = before (BitVec.ofNat bits physical)) :
    HeapEffects full capWords before after := by
  refine ⟨?_, ?_, highFrame⟩
  · intro address ha
    rw [capacityFrame address ha]
    exact ((rep.2.2.2.2.2.2.2.2 hq).2 address ha)
  · intro address ha
    exact capacityFrame address (by omega)

theorem correct_effects {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (room : Rooms full capWords bits) (rep : HeapRepresents q full capWords configuration heap) :
    HeapEffects full capWords heap (PSTRRuntimeAdvance.bumpHeap (packedCapacityWords q capWords bits) heap) := by
  have fit : Fits bits (4 + packedCapacityWords q capWords bits) := Rooms.metadata full capWords bits room hq 0 (by omega)
  apply effects_from_frames full configuration capWords heap _ hq rep room.bitmap
  · exact fun address ha => PSTRAdvanceHeap.bump_capacity heap capWords address
      (by have h := room.bits_eight; omega) hq ha room.scalar fit
  · intro physical hf hp
    exact PSTRRuntimeAdvance.heap_frame _ heap _ ((ofNat_injective_of_fit _ _ hf fit).not.mpr (by omega))

theorem fail_effects {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (room : Rooms full capWords bits) (rep : HeapRepresents q full capWords configuration heap) :
    HeapEffects full capWords heap (PSTRRuntimeFail.failHeap (packedCapacityWords q capWords bits) heap) := by
  have fit : Fits bits (5 + packedCapacityWords q capWords bits) := by
    have h := Rooms.metadata full capWords bits room hq 1 (by omega)
    convert h using 1
    omega
  apply effects_from_frames full configuration capWords heap _ hq rep room.bitmap
  · exact fun address ha => PSTRRuntimeFail.capacity_frame heap capWords address
      (by have h := room.bits_eight; omega) hq ha room.scalar fit
  · intro physical hf hp
    exact PSTRRuntimeFail.heap_frame _ heap _ ((ofNat_injective_of_fit _ _ hf fit).not.mpr (by omega))

theorem correct_prefix_effects {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (hq : 0 < q) (room : Rooms full capWords bits)
    (rep : HeapRepresents q full capWords configuration state.heap) (count : Nat) (hc : count ≤ 8) :
    HeapEffects full capWords state.heap (executeOps (callInput q full .correct) (correctProgram.take count) state).heap := by
  rw [correct_prefix_heap _ state (packedCapacityWords q capWords bits) rep.2.2.1 count hc]
  split_ifs
  · exact initial_effects full configuration capWords state.heap hq rep
  · exact correct_effects full configuration capWords state.heap hq room rep

theorem fail_prefix_effects {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (hq : 0 < q) (room : Rooms full capWords bits)
    (rep : HeapRepresents q full capWords configuration state.heap) (count : Nat) (hc : count ≤ 6) :
    HeapEffects full capWords state.heap (executeOps (callInput q full .error) (failProgram.take count) state).heap := by
  rw [fail_prefix_heap _ state (packedCapacityWords q capWords bits) rep.2.2.1 count hc]
  split_ifs
  · exact initial_effects full configuration capWords state.heap hq rep
  · exact fail_effects full configuration capWords state.heap hq room rep

theorem correct_represents {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (hq : 0 < q) (room : Rooms full capWords bits)
    (allowed : Allowed full configuration .correct) (rep : HeapRepresents q full capWords configuration state.heap) :
    HeapRepresents q full capWords (nextConfiguration q full configuration .correct)
      (executeOps (callInput q full .correct) correctProgram state).heap := by
  rw [correct_heap _ state (packedCapacityWords q capWords bits) rep.2.2.1]
  exact PSTRAdvanceHeap.heapRepresents_advance full configuration capWords state.heap room.bits_eight hq rep
    room.bitmap room.scalar (Rooms.metadata full capWords bits room hq)
    ((show configuration.stage + 1 ≤ full.length + 1 by have hs := allowed.2; omega).trans_lt room.N1)

theorem fail_represents {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (hq : 0 < q) (room : Rooms full capWords bits)
    (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = none)
    (rep : HeapRepresents q full capWords configuration state.heap) :
    HeapRepresents q full capWords (nextConfiguration q full configuration .error)
      (executeOps (callInput q full .error) failProgram state).heap := by
  rw [fail_heap _ state (packedCapacityWords q capWords bits) rep.2.2.1]
  have hs : configuration.stage < full.length + 1 := by have h := allowed.2; omega
  simp only [nextConfiguration, hs, dite_true, choose]
  exact PSTRRuntimeFail.heapRepresents_fail full configuration capWords state.heap room.bits_eight hq rep
    room.bitmap room.scalar (Rooms.metadata full capWords bits room hq)

end PaperProofs.Structure.LaminarTree.PSTRReplyControls
