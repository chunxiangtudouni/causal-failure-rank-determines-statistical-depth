module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009r

/-! The runtime reverse-loop invariant closes under the actual105 fetched
iteration. The counter is decremented by the program; metadata/count/parent
cells and original packed table representation persist through its stores. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 2600000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem reverseReady_step {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ReverseEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : ReverseReady full configuration origin capWords header base counts parents size (remaining + 1) state) :
    ReverseReady full configuration origin capWords header base counts parents size remaining
      (packingRun (callInput q full command) containing 105 state) := by
  let parent := (state.heap (BitVec.ofNat bits (parents + (remaining + 1)))).toNat
  let count := (state.heap (BitVec.ofNat bits (counts + remaining))).toNat
  let cap := logicalHeap q capWords state.heap (base + remaining)
  let selected := pushedValue remaining parent cap count (state.heap (BitVec.ofNat bits (childBase header q + parent)))
  let after := packingRun (callInput q full command) containing 105 state
  have hrem : remaining < size := by have hh := ready.bound; omega
  have hparent : parent ≤ size := ready.data.parentBound remaining hrem
  have hn : Fits bits (remaining + 1) := ready.bound.trans_lt layout.sizeFits
  have hp : Fits bits parent := BitVec.isLt _
  have hc : Fits bits count := BitVec.isLt _
  have hparentWord : state.heap (BitVec.ofNat bits (parents + (remaining + 1))) = BitVec.ofNat bits parent := by
    simp only [parent, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hcountWord : state.heap (BitVec.ofNat bits (counts + remaining)) = BitVec.ofNat bits count := by
    simp only [count, BitVec.ofNat_toNat, BitVec.setWidth_eq]
  have hr := actual_reverse_push em full command configuration capWords heapWords header base (childBase header q)
    counts parents remaining parent count state layout.bits8 layout.positive layout.width ready.data.represents
    layout.capacityFits layout.heapFits layout.header_eq (by have hh := layout.headerAllocated; omega)
    ready.data.width ready.data.mask layout.oneFits hn hp hc
    ((show base + remaining ≤ base + size by omega).trans_lt layout.payloadFits)
    (by have hh := layout.payloadBound; omega) (by unfold childBase; omega) (layout.targetFits parent hparent)
    ready.address ready.pc ready.active ready.counter ready.data.payload ready.data.candidates
    ready.data.countsBase ready.data.parentsBase hcountWord hparentWord
  rcases hr with ⟨ha, hpc, had, _, _, hm⟩
  have hmem : after.heap = reverseStepHeap header (childBase header q) parent remaining selected state.heap := hm
  have hleading (physical : Nat) (hphysical : physical < header + 8) :
      after.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    rw [hmem]
    apply reverseStepHeap_frame layout parent remaining hparent selected state.heap physical
      ((show physical ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits)
    · omega
    · unfold childBase
      omega
  have hkeep (offset : Nat) (hlo : 9 ≤ offset) (hhi : offset ≤ 12) :
      after.heap (BitVec.ofNat bits (header + offset)) = state.heap (BitVec.ofNat bits (header + offset)) := by
    rw [hmem]
    apply reverseStepHeap_frame layout parent remaining hparent selected state.heap (header + offset)
      (layout.headerFits offset (by omega))
    · omega
    · unfold childBase
      omega
  have hrep : HeapRepresents q full capWords configuration after.heap := by
    apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (header + 8) state.heap after.heap
      (by have hb := layout.bits8; omega) layout.positive ready.data.represents layout.bitmap layout.capacityFits
      (by simpa only [Nat.add_assoc, Nat.reduceAdd] using layout.headerFits 11 (by decide)) layout.metadata_le hleading
  refine ⟨by have hh := ready.bound; omega, had, ?_, hpc, ha, ?_⟩
  · rw [hmem, reverseStepHeap, Function.update_self]
  · refine ⟨hrep, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hleading _ (layout.cache_lt 12 (by decide))]
      exact ready.data.width
    · rw [hleading _ (layout.cache_lt 13 (by decide))]
      exact ready.data.mask
    · rw [hkeep 9 (by decide) (by decide)]
      exact ready.data.payload
    · rw [hkeep 10 (by decide) (by decide)]
      exact ready.data.candidates
    · rw [hkeep 11 (by decide) (by decide)]
      exact ready.data.countsBase
    · rw [hkeep 12 (by decide) (by decide)]
      exact ready.data.parentsBase
    · intro node hnode
      rw [hleading _ (by have hh := layout.parentsEnd; omega)]
      exact ready.data.parentBound node hnode

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
