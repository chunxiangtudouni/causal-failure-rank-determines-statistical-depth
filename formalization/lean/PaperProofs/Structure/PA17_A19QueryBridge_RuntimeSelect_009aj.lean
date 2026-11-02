module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ai

/-! The actual descent91 round maintains its finite data invariant and the
original represented table/used/metadata. No all-prefix safety or canonical
chosen tool is an input; the leaf token comes from the real48op read. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3000000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem descendTailHeap_frame {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (remaining : Nat) (tool node : BitVec bits) (heap : BitVec bits → BitVec bits)
    (physical : Nat) (hfit : Fits bits physical)
    (hf : physical ≠ header + 13) (hn : physical ≠ nodeSlot header q size) (ht : physical ≠ toolSlot header q size) :
    descendTailHeap header q size remaining tool node heap (BitVec.ofNat bits physical) = heap (BitVec.ofNat bits physical) := by
  have hneF := (ofNat_injective_of_fit _ _ hfit (layout.headerFits 13 (by decide))).not.mpr hf
  have hneN := (ofNat_injective_of_fit _ _ hfit
    ((show nodeSlot header q size ≤ endpoint header q size by unfold nodeSlot endpoint; omega).trans_lt layout.endpointFits)).not.mpr hn
  have hneT := (ofNat_injective_of_fit _ _ hfit
    ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt layout.endpointFits)).not.mpr ht
  rw [descendTailHeap, Function.update_of_ne hneF, Function.update_of_ne hneN, Function.update_of_ne hneT]

theorem descendTailHeap_node {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (remaining : Nat) (tool node : BitVec bits) (heap : BitVec bits → BitVec bits) :
    descendTailHeap header q size remaining tool node heap (BitVec.ofNat bits (nodeSlot header q size)) = node := by
  have hn : BitVec.ofNat bits (nodeSlot header q size) ≠ BitVec.ofNat bits (header + 13) := by
    apply (ofNat_injective_of_fit _ _
      ((show nodeSlot header q size ≤ endpoint header q size by unfold nodeSlot endpoint; omega).trans_lt layout.endpointFits)
      (layout.headerFits 13 (by decide))).not.mpr
    unfold nodeSlot childBase
    omega
  rw [descendTailHeap, Function.update_of_ne hn, Function.update_self]

theorem descReady_step {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size (remaining + 1) state) :
    DescReady full configuration origin capWords header base counts parents size remaining
      (packingRun (callInput q full command) containing 91 state) := by
  let current := (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat
  let node := clampedNode layout current ready.nodeBound
  let token := BitVec.ofNat bits
    (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
      | none => 0 | some tool => tool.val + 1)
  let oldTool := state.heap (BitVec.ofNat bits (toolSlot header q size))
  let child := state.heap (BitVec.ofNat bits (childBase header q + current))
  let newTool := descendedTool current token oldTool
  let newNode := descendedNode current token child
  let after := packingRun (callInput q full command) containing 91 state
  have hr := actual_desc_round em layout command configuration state ready
  rcases hr with ⟨ha, hp, had, _, hm⟩
  have hmem : after.heap = descendTailHeap header q size remaining newTool newNode state.heap := hm
  have hkeep (physical : Nat) (hfit : Fits bits physical) (hf : physical ≠ header + 13)
      (hn : physical ≠ nodeSlot header q size) (ht : physical ≠ toolSlot header q size) :
      after.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    rw [hmem]
    exact descendTailHeap_frame layout remaining newTool newNode state.heap physical hfit hf hn ht
  have hleading (physical : Nat) (hphysical : physical < header + 13) :
      after.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    apply hkeep physical ((show physical ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits)
    · omega
    · unfold nodeSlot childBase
      omega
    · unfold toolSlot childBase
      omega
  have hrep : HeapRepresents q full capWords configuration after.heap := by
    apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (header + 13) state.heap after.heap
      (by have hb := layout.bits8; omega) layout.positive ready.data.represents layout.bitmap layout.capacityFits
      ((show header + 13 + 3 ≤ endpoint header q size by unfold endpoint childBase; omega).trans_lt layout.endpointFits)
      (by have hm := layout.metadata_le; omega) hleading
  have hcandidate (encoded : Nat) (he : encoded ≤ size) :
      after.heap (BitVec.ofNat bits (childBase header q + encoded)) = state.heap (BitVec.ofNat bits (childBase header q + encoded)) := by
    apply hkeep (childBase header q + encoded) ((Nat.le_succ _).trans_lt (layout.targetFits encoded he))
    · unfold childBase
      omega
    · unfold nodeSlot
      omega
    · unfold toolSlot
      omega
  refine ⟨by have hh := ready.bound; omega, had, ?_, ?_, ?_, ?_, ?_, hp, ha, ?_⟩
  · rw [hmem, descendTailHeap, Function.update_self]
  · rw [hkeep (header + 14) (layout.headerFits 14 (by decide)) (by omega)
      (by unfold nodeSlot childBase; omega) (by unfold toolSlot childBase; omega)]
    exact ready.nodePointer
  · rw [hkeep (header + 15) (layout.headerFits 15 (by decide)) (by omega)
      (by unfold nodeSlot childBase; omega) (by unfold toolSlot childBase; omega)]
    exact ready.toolPointer
  · rw [hmem, descendTailHeap_node layout]
    unfold newNode descendedNode
    split
    · exact ready.candidates.2 current ready.nodeBound
    · simp
  · constructor
    · rw [show childBase header q = childBase header q + 0 by omega, hcandidate 0 (by omega)]
      simpa only [Nat.add_zero] using ready.candidates.1
    · intro encoded he
      rw [hcandidate encoded he]
      exact ready.candidates.2 encoded he
  · refine ⟨hrep, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hleading _ ((layout.cache_lt 12 (by decide)).trans (by omega))]
      exact ready.data.width
    · rw [hleading _ ((layout.cache_lt 13 (by decide)).trans (by omega))]
      exact ready.data.mask
    · rw [hleading (header + 9) (by omega)]
      exact ready.data.payload
    · rw [hleading (header + 10) (by omega)]
      exact ready.data.candidates
    · rw [hleading (header + 11) (by omega)]
      exact ready.data.countsBase
    · rw [hleading (header + 12) (by omega)]
      exact ready.data.parentsBase
    · intro n hn
      rw [hleading _ (by have hh := layout.parentsEnd; omega)]
      exact ready.data.parentBound n hn

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
