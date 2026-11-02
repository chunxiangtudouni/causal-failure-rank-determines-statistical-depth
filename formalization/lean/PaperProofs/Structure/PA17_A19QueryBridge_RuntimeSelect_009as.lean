module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ar
public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeSelect_009ak

/-! Canonical candidate stability and stopped-node behavior of the real
descent. Finding a leaf really stores the token; later fuel rounds preserve
it at node0, rather than restarting or receiving an external chosen tool. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem descendTailHeap_tool {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (remaining : Nat) (tool node : BitVec bits) (heap : BitVec bits → BitVec bits) :
    descendTailHeap header q size remaining tool node heap (BitVec.ofNat bits (toolSlot header q size)) = tool := by
  have hf : BitVec.ofNat bits (toolSlot header q size) ≠ BitVec.ofNat bits (header + 13) := by
    apply (ofNat_injective_of_fit _ _
      ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt layout.endpointFits)
      (layout.headerFits 13 (by decide))).not.mpr
    unfold toolSlot childBase
    omega
  have hn : BitVec.ofNat bits (toolSlot header q size) ≠ BitVec.ofNat bits (nodeSlot header q size) := by
    apply (ofNat_injective_of_fit _ _
      ((show toolSlot header q size ≤ endpoint header q size by unfold toolSlot endpoint; omega).trans_lt layout.endpointFits)
      ((show nodeSlot header q size ≤ endpoint header q size by unfold nodeSlot endpoint; omega).trans_lt layout.endpointFits)).not.mpr
    unfold toolSlot nodeSlot
    omega
  rw [descendTailHeap, Function.update_of_ne hf, Function.update_of_ne hn, Function.update_self]

theorem physicalCandidates_tail {bits q capWords heapWords header base counts parents size : Nat}
    {full : List (Finset (Fin q))} (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (remaining : Nat) (tool node : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hc : PhysicalCandidatesFor full usedCounts capacity header heap) :
    PhysicalCandidatesFor full usedCounts capacity header (descendTailHeap header q size remaining tool node heap) := by
  have hs : size = (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt layout.positive, ite_false] using layout.size_eq
  have hkeep (encoded : Nat) (he : encoded ≤ size) :
      descendTailHeap header q size remaining tool node heap (BitVec.ofNat bits (childBase header q + encoded)) =
        heap (BitVec.ofNat bits (childBase header q + encoded)) := by
    apply descendTailHeap_frame layout remaining tool node heap _ ((Nat.le_succ _).trans_lt (layout.targetFits encoded he))
    · unfold childBase
      omega
    · unfold nodeSlot
      omega
    · unfold toolSlot
      omega
  constructor
  · simpa only [Nat.add_zero] using (hkeep 0 (by omega)).trans hc.1
  · intro parent
    rw [hkeep (parent.val + 1) (by have hp := parent.isLt; omega)]
    exact hc.2 parent

theorem actual_desc_round_candidates {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size (remaining + 1) state)
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hc : PhysicalCandidatesFor full usedCounts capacity header state.heap) :
    PhysicalCandidatesFor full usedCounts capacity header
      (packingRun (callInput q full command) containing 91 state).heap := by
  have hr := actual_desc_round em layout command configuration state ready
  dsimp only at hr
  rw [hr.2.2.2.2]
  exact physicalCandidates_tail layout usedCounts capacity remaining _ _ state.heap hc

theorem actual_desc_stopped_step {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size (remaining + 1) state)
    (hz : state.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits 0) :
    let after := packingRun (callInput q full command) containing 91 state
    after.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits 0 ∧
      after.heap (BitVec.ofNat bits (toolSlot header q size)) = state.heap (BitVec.ofNat bits (toolSlot header q size)) := by
  have hr := actual_desc_round em layout command configuration state ready
  dsimp only at hr
  have hn : (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat = 0 := by rw [hz]; rfl
  dsimp only
  rw [hr.2.2.2.2, descendTailHeap_node layout, descendTailHeap_tool layout]
  simp only [hn, descendedNode, descendedTool, maskedLeaf, ite_true, BitVec.toNat_ofNat, Nat.zero_mod,
    Nat.add_zero, ready.candidates.1, and_self]

theorem actual_desc_stopped {bits q origin capWords heapWords header base counts parents size fuel : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size fuel state)
    (hz : state.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits 0) :
    (packingRun (callInput q full command) containing (91 * fuel) state).heap (BitVec.ofNat bits (toolSlot header q size)) =
      state.heap (BitVec.ofNat bits (toolSlot header q size)) := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    have hs := actual_desc_stopped_step em layout command configuration state ready hz
    have hd := descReady_step em layout command configuration state ready
    rw [show 91 * (fuel + 1) = 91 + 91 * fuel by omega, run_add]
    exact (ih _ hd hs.1).trans hs.2

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
