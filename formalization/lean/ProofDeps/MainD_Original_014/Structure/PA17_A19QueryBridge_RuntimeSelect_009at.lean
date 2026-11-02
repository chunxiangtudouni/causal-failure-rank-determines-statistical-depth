module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009as

/-! Exact original canonical descent from the true candidate array. The
leaf token is fetched by the actual metadata reader inside every91-op
round; the proof follows the original first-child tie and failure behavior. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3400000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims IndexedDescent

theorem actual_desc_node_step {bits q origin capWords heapWords header base counts parents size remaining : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size (remaining + 1) state)
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hc : PhysicalCandidatesFor full usedCounts capacity header state.heap)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hn : state.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits (node.val + 1)) :
    let after := packingRun (callInput q full command) containing 91 state
    after.heap (BitVec.ofNat bits (nodeSlot header q size)) =
        (match (leafTools (prepareNormalization q full).indexed).get node with
          | none => BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed
              (firstSlackChild (prepareNormalization q full).indexed usedCounts capacity node))
          | some _ => BitVec.ofNat bits 0) ∧
      after.heap (BitVec.ofNat bits (toolSlot header q size)) =
        (match (leafTools (prepareNormalization q full).indexed).get node with
          | none => state.heap (BitVec.ofNat bits (toolSlot header q size))
          | some tool => BitVec.ofNat bits (tool.val + 1)) := by
  have hs : size = (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt layout.positive, ite_false] using layout.size_eq
  have hfit : Fits bits (node.val + 1) :=
    (show node.val + 1 ≤ size by have hh := node.isLt; omega).trans_lt layout.sizeFits
  have hcurrent : (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat = node.val + 1 := by
    rw [hn, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  have hnode : clampedNode layout (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat ready.nodeBound = node := by
    apply Fin.ext
    change (state.heap (BitVec.ofNat bits (nodeSlot header q size))).toNat - 1 = node.val
    rw [hcurrent]
    omega
  have hr := actual_desc_round em layout command configuration state ready
  dsimp only at hr
  rw [hnode] at hr
  dsimp only
  rw [hr.2.2.2.2, descendTailHeap_node layout, descendTailHeap_tool layout]
  cases hl : (leafTools (prepareNormalization q full).indexed).get node with
  | none =>
    simp only [hcurrent, descendedNode, descendedTool, maskedLeaf, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ite_false, BitVec.toNat_ofNat, Nat.zero_mod, ite_true, hc.2 node, and_self]
  | some tool =>
    have ht : Fits bits (tool.val + 1) :=
      (show tool.val + 1 ≤ endpoint header q size by have hh := tool.isLt; unfold endpoint childBase; omega).trans_lt layout.endpointFits
    have htool : tool.val + 1 ≠ 0 := by omega
    simp only [hcurrent, descendedNode, descendedTool, maskedLeaf, Nat.add_eq_zero_iff,
      Nat.one_ne_zero, and_false, ite_false, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ht, htool, and_self]

theorem actual_desc_tool_node {bits q origin capWords heapWords header base counts parents size fuel : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : DescEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (ready : DescReady full configuration origin capWords header base counts parents size fuel state)
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hc : PhysicalCandidatesFor full usedCounts capacity header state.heap)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hn : state.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits (node.val + 1))
    (ht : state.heap (BitVec.ofNat bits (toolSlot header q size)) = BitVec.ofNat bits 0) :
    (packingRun (callInput q full command) containing (91 * fuel) state).heap (BitVec.ofNat bits (toolSlot header q size)) =
      BitVec.ofNat bits (PA17LeafLabels005.encodeTool
        (descend (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed) usedCounts capacity fuel node)) := by
  induction fuel generalizing state node with
  | zero => exact ht
  | succ fuel ih =>
    let after := packingRun (callInput q full command) containing 91 state
    have hd := descReady_step em layout command configuration state ready
    have hca := actual_desc_round_candidates em layout command configuration state ready usedCounts capacity hc
    have hstep := actual_desc_node_step em layout command configuration state ready usedCounts capacity hc node hn
    rw [show 91 * (fuel + 1) = 91 + 91 * fuel by omega, run_add]
    cases hl : (leafTools (prepareNormalization q full).indexed).get node with
    | some tool =>
      have hz : after.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits 0 := by simpa only [hl] using hstep.1
      have hv : after.heap (BitVec.ofNat bits (toolSlot header q size)) = BitVec.ofNat bits (tool.val + 1) := by simpa only [hl] using hstep.2
      rw [actual_desc_stopped em layout command configuration after hd hz, hv, descend, hl]
      rfl
    | none =>
      have hna : after.heap (BitVec.ofNat bits (nodeSlot header q size)) =
          BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed
            (firstSlackChild (prepareNormalization q full).indexed usedCounts capacity node)) := by simpa only [hl] using hstep.1
      have hta : after.heap (BitVec.ofNat bits (toolSlot header q size)) = BitVec.ofNat bits 0 := by
        have hv : after.heap (BitVec.ofNat bits (toolSlot header q size)) = state.heap (BitVec.ofNat bits (toolSlot header q size)) := by
          simpa only [hl] using hstep.2
        exact hv.trans ht
      rw [descend, hl]
      cases hchild : firstSlackChild (prepareNormalization q full).indexed usedCounts capacity node with
      | none =>
        have hz : after.heap (BitVec.ofNat bits (nodeSlot header q size)) = BitVec.ofNat bits 0 := by simpa only [hchild, encodedNode] using hna
        exact (actual_desc_stopped em layout command configuration after hd hz).trans hta
      | some child =>
        exact ih after hd hca child (by simpa only [hchild, encodedNode] using hna) hta

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
