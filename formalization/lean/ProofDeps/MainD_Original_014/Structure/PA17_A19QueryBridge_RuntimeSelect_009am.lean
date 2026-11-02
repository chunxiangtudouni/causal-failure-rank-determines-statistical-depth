module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009ak

/-! The actual26op descent initialization establishes DescReady and tool0
from arbitrary local scratch. Node range is the same-call header bound;
candidate bounds are supplied by the already proved actual parent kernel. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem descendInitHeap_frame {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (current : Nat) (heap : BitVec bits → BitVec bits) (physical : Nat) (hfit : Fits bits physical)
    (h13 : physical ≠ header + 13) (h14 : physical ≠ header + 14) (h15 : physical ≠ header + 15)
    (hn : physical ≠ nodeSlot header q size) (ht : physical ≠ toolSlot header q size) :
    descendInitHeap header q size current heap (BitVec.ofNat bits physical) = heap (BitVec.ofNat bits physical) := by
  have he13 := (ofNat_injective_of_fit _ _ hfit (layout.headerFits 13 (by decide))).not.mpr h13
  have he14 := (ofNat_injective_of_fit _ _ hfit (layout.headerFits 14 (by decide))).not.mpr h14
  have he15 := (ofNat_injective_of_fit _ _ hfit (layout.headerFits 15 (by decide))).not.mpr h15
  have hen := (ofNat_injective_of_fit _ _ hfit
    ((show nodeSlot header q size ≤ endpoint header q size by unfold nodeSlot endpoint; omega).trans_lt layout.endpointFits)).not.mpr hn
  have het := (ofNat_injective_of_fit _ _ hfit
    ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt layout.endpointFits)).not.mpr ht
  rw [descendInitHeap, Function.update_of_ne het, Function.update_of_ne hen, Function.update_of_ne he13,
    Function.update_of_ne he15, Function.update_of_ne he14]

theorem execute_desc_initial_ready {bits q origin capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))}
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ReverseHeapData full configuration capWords header base counts parents size state.heap)
    (bounded : CandidateBounded header q size state.heap)
    (hnode : (state.heap (BitVec.ofNat bits (header + 1))).toNat ≤ size)
    (hh : state.register .address = BitVec.ofNat bits header)
    (hp : state.pc = BitVec.ofNat bits (5 * origin)) (ha : state.halted = false) :
    let after := executeOps (callInput q full command) descendInit state
    DescReady full configuration (origin + 26) capWords header base counts parents size size after ∧
      after.heap (BitVec.ofNat bits (toolSlot header q size)) = BitVec.ofNat bits 0 := by
  let rom := callInput q full command
  let current := (state.heap (BitVec.ofNat bits (header + 1))).toNat
  let after := executeOps rom descendInit state
  have hnodeWord : state.heap (BitVec.ofNat bits (header + 1)) = BitVec.ofNat bits current := by
    simp only [current, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hi := descendInit_result rom header q size current state layout.endpointFits hh
    (data.represents.1.trans layout.size_eq.symm) data.candidates hnodeWord
  have hcells := descendInitHeap_cells header q size current state.heap layout.endpointFits
  dsimp only at hcells
  rw [← hi.2] at hcells
  have hkeep (physical : Nat) (hfit : Fits bits physical) (h13 : physical ≠ header + 13)
      (h14 : physical ≠ header + 14) (h15 : physical ≠ header + 15)
      (hn : physical ≠ nodeSlot header q size) (ht : physical ≠ toolSlot header q size) :
      after.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    rw [hi.2]
    exact descendInitHeap_frame layout current state.heap physical hfit h13 h14 h15 hn ht
  have hleading (physical : Nat) (hphysical : physical < header + 13) :
      after.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    apply hkeep physical ((show physical ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits)
    · omega
    · omega
    · omega
    · unfold nodeSlot childBase
      omega
    · unfold toolSlot childBase
      omega
  have hcandidate (encoded : Nat) (he : encoded ≤ size) :
      after.heap (BitVec.ofNat bits (childBase header q + encoded)) = state.heap (BitVec.ofNat bits (childBase header q + encoded)) := by
    apply hkeep (childBase header q + encoded) ((Nat.le_succ _).trans_lt (layout.targetFits encoded he))
    · unfold childBase
      omega
    · unfold childBase
      omega
    · unfold childBase
      omega
    · unfold nodeSlot
      omega
    · unfold toolSlot
      omega
  have hrep : HeapRepresents q full capWords configuration after.heap := by
    apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (header + 13) state.heap after.heap
      (by have hb := layout.bits8; omega) layout.positive data.represents layout.bitmap layout.capacityFits
      ((show header + 13 + 3 ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits)
      (by have hm := layout.metadata_le; omega) hleading
  dsimp only
  refine ⟨?_, hcells.2.2.2.2⟩
  refine ⟨le_rfl, hi.1, hcells.1, hcells.2.1, hcells.2.2.1, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcells.2.2.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (hnode.trans_lt layout.sizeFits)]
    exact hnode
  · constructor
    · rw [show childBase header q = childBase header q + 0 by omega, hcandidate 0 (by omega)]
      simpa only [Nat.add_zero] using bounded.1
    · intro encoded he
      rw [hcandidate encoded he]
      exact bounded.2 encoded he
  · rw [executeOps_pc rom descendInit state descendInit_straight, hp, descendInit_length, BitVec.ofNat_add_ofNat]
    congr 1
  · rw [executeOps_halted, ha]
  · refine ⟨hrep, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hleading _ ((layout.cache_lt 12 (by decide)).trans (by omega))]
      exact data.width
    · rw [hleading _ ((layout.cache_lt 13 (by decide)).trans (by omega))]
      exact data.mask
    · rw [hleading (header + 9) (by omega)]
      exact data.payload
    · rw [hleading (header + 10) (by omega)]
      exact data.candidates
    · rw [hleading (header + 11) (by omega)]
      exact data.countsBase
    · rw [hleading (header + 12) (by omega)]
      exact data.parentsBase
    · intro n hn
      rw [hleading _ (by have hh := layout.parentsEnd; omega)]
      exact data.parentBound n hn

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
