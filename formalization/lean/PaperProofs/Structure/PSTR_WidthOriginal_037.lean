module

public import PaperProofs.Structure.PSTR_WidthHeap_036
public import PaperProofs.Structure.PSTR_RuntimeWidthBounds_009

/-! Original A19 indexWidth and liveWork discharge this prologue's numeric
and cost premises. This is a verified part of a call, not CallClaims or a
preprocessor/query correctness premise. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRWidthOriginal

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM

theorem raw_N_room (N q : Nat) : Fits (indexWidth 16 N q) N :=
  (show N ≤ N * q + N + q + 640 by omega).trans_lt (fits_checker_register_bound N q)

theorem raw_command_room (N q : Nat) : Fits (indexWidth 16 N q) (2 + N * q) :=
  (show 2 + N * q ≤ N * q + N + q + 640 by omega).trans_lt (fits_checker_register_bound N q)

theorem active_width_mask {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec (indexWidth 16 full.length q) → BitVec (indexWidth 16 full.length q)) :
    let bits := indexWidth 16 full.length q
    let after := packingRun (callInput q full command) PSTRWidthPrologue.program
      (8 * CapacityBits.width q + 16) (packingInitial heap)
    after.halted = false ∧ after.pc = BitVec.ofNat bits 105 ∧
      after.register .total = BitVec.ofNat bits (CapacityBits.width q) ∧
      after.register .flag = lowMask bits (CapacityBits.width q) ∧ after.heap = heap :=
  PSTRWidthPrologue.actual_width_mask full command heap (PSTRRuntimeWidthBounds.word_bits full.length q)
    (raw_N_room full.length q) (raw_command_room full.length q) (PSTRRuntimeWidthBounds.scalar_room full.length q)

theorem all_prefix_heap {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec (indexWidth 16 full.length q) → BitVec (indexWidth 16 full.length q))
    (clock : Nat) (hc : clock ≤ 8 * CapacityBits.width q + 17) :
    (packingRun (callInput q full command) PSTRWidthPrologue.program clock (packingInitial heap)).heap = heap :=
  PSTRWidthHeap.all_prefix_heap full command heap (PSTRRuntimeWidthBounds.word_bits full.length q)
    (raw_N_room full.length q) (raw_command_room full.length q) (PSTRRuntimeWidthBounds.scalar_room full.length q)
    clock hc

theorem heap_represents_prefix {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (capWords : Nat) (configuration : Configuration q)
    (heap : BitVec (indexWidth 16 full.length q) → BitVec (indexWidth 16 full.length q))
    (rep : HeapRepresents q full capWords configuration heap)
    (clock : Nat) (hc : clock ≤ 8 * CapacityBits.width q + 17) :
    HeapRepresents q full capWords configuration
      (packingRun (callInput q full command) PSTRWidthPrologue.program clock (packingInitial heap)).heap := by
  rw [all_prefix_heap full command heap clock hc]
  exact rep

theorem capacity_prefix {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (capWords : Nat) (configuration : Configuration q)
    (heap : BitVec (indexWidth 16 full.length q) → BitVec (indexWidth 16 full.length q))
    (rep : HeapRepresents q full capWords configuration heap) (hq : 0 < q)
    (clock : Nat) (hc : clock ≤ 8 * CapacityBits.width q + 17) :
    CapacityPrefixBounded q capWords (logicalHeap q capWords
      (packingRun (callInput q full command) PSTRWidthPrologue.program clock (packingInitial heap)).heap) := by
  rw [all_prefix_heap full command heap clock hc]
  exact (rep.2.2.2.2.2.2.2.2 hq).2

theorem halted {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec (indexWidth 16 full.length q) → BitVec (indexWidth 16 full.length q)) :
    (packingRun (callInput q full command) PSTRWidthPrologue.program
      (8 * CapacityBits.width q + 17) (packingInitial heap)).halted = true :=
  PSTRWidthHeap.halted full command heap (PSTRRuntimeWidthBounds.word_bits full.length q)
    (raw_N_room full.length q) (raw_command_room full.length q) (PSTRRuntimeWidthBounds.scalar_room full.length q)

theorem positive_tree_size {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q) :
    0 < treeSize q full := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have ht : 0 < (prepareNormalization q full).indexed.nodes.size :=
    Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  simpa only [treeSize, ne_of_gt hq, ite_false] using ht

theorem call_cost {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) :
    callCost q full PSTRWidthPrologue.program command (8 * CapacityBits.width q + 17) heap ≤
      419 * liveWork q (treeSize q full) := by
  have htrace := packingDynamicTrace_length_le (callInput q full command) PSTRWidthPrologue.program
    (8 * CapacityBits.width q + 17) (packingInitial heap)
  have hwidth := PSTRRuntimeWidthWord.width_le q
  have hcost : callCost q full PSTRWidthPrologue.program command (8 * CapacityBits.width q + 17) heap ≤
      96 * CapacityBits.width q + 323 := by
    unfold callCost
    rw [PSTRWidthPrologue.code_length]
    omega
  by_cases hq : q = 0
  · subst q
    rw [CapacityBits.width_zero] at hcost
    simpa only [liveWork, ite_true, Nat.mul_one, CapacityBits.width_zero] using
      hcost.trans (show 96 * 0 + 323 ≤ 419 by decide)
  · have ht := positive_tree_size full (by omega)
    have hwork : q + 1 ≤ (q + 1) * treeSize q full := Nat.le_mul_of_pos_right _ ht
    have hbound : 96 * CapacityBits.width q + 323 ≤ 419 * ((q + 1) * treeSize q full) := by omega
    simpa only [liveWork, hq, ite_false, queryWork] using hcost.trans hbound

end PaperProofs.Structure.LaminarTree.PSTRWidthOriginal
