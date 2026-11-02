module

public import Structure.PA17_A19QueryBridge_RuntimeSelect_009aq
public import Structure.PA17_A19QueryBridge_RuntimeCanonical_021a

/-! Canonical meaning of the actual runtime-built candidate array. Source
facts describe only the current run's materialized parents/counts and the
original packed table payload. No candidate, flag or selected-tool oracle. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 3200000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine PSTRWordSegments
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

structure SelectionSources {bits q : Nat} (full : List (Finset (Fin q)))
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (capWords base counts parents : Nat) (heap : BitVec bits → BitVec bits) : Prop where
  parentValues : ∀ node : (prepareNormalization q full).indexed.NodeId,
    (heap (BitVec.ofNat bits (parents + (node.val + 1)))).toNat =
      encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get node)
  countValues : ∀ node : (prepareNormalization q full).indexed.NodeId,
    (heap (BitVec.ofNat bits (counts + node.val))).toNat = usedCounts.get node
  capacityValues : ∀ node : (prepareNormalization q full).indexed.NodeId,
    logicalHeap q capWords heap (base + node.val) = capacity.get node

def PhysicalCandidatesFor {bits q : Nat} (full : List (Finset (Fin q)))
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (header : Nat) (heap : BitVec bits → BitVec bits) : Prop :=
  heap (BitVec.ofNat bits (childBase header q)) = BitVec.ofNat bits 0 ∧
    ∀ node : (prepareNormalization q full).indexed.NodeId,
      heap (BitVec.ofNat bits (childBase header q + (node.val + 1))) =
        BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed
          (IndexedDescent.firstSlackChild (prepareNormalization q full).indexed usedCounts capacity node))

theorem actual_parent_candidates_canonical {bits q origin capWords heapWords header base counts parents size row budget : Nat}
    {full : List (Finset (Fin q))} {containing : List PackingOp}
    (em : ParentEmbedded bits origin containing)
    (layout : ReverseLayout bits q full capWords heapWords header base counts parents size)
    (command : Command) (configuration : Configuration q) (state : WordState bits)
    (data : ParentInputs full configuration origin capWords header base counts parents size row budget state)
    (usedCounts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (sources : SelectionSources full usedCounts capacity capWords base counts parents state.heap) :
    PhysicalCandidatesFor full usedCounts capacity header
      (packingRun (callInput q full command) containing (parentSteps size) state).heap := by
  have hs : size = (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt layout.positive, ite_false] using layout.size_eq
  constructor
  · exact (actual_parent_candidateBounded em layout command configuration state data).1
  · intro parent
    rw [actual_parent_candidate_find em layout command configuration state data (parent.val + 1) (by omega) (by have hp := parent.isLt; omega)]
    have ht (n : Nat) (hn : n < (prepareNormalization q full).indexed.nodes.size) :
        parentHit q capWords base counts parents (parent.val + 1) state.heap n =
          decide ((prepareNormalization q full).indexed.parents.get ⟨n, hn⟩ = some parent ∧
            usedCounts.get ⟨n, hn⟩ < capacity.get ⟨n, hn⟩) := by
      let node : (prepareNormalization q full).indexed.NodeId := ⟨n, hn⟩
      have hp := sources.parentValues node
      have hc := sources.countValues node
      have hv := sources.capacityValues node
      dsimp only [node] at hp hc hv
      simp only [parentHit, hp, hc, hv, UniformNormalizationRAM.encodedNode_eq_some]
    have he := PA17A19RuntimeCanonical021.prepared_find_firstSlackChild full usedCounts capacity parent
      (parentHit q capWords base counts parents (parent.val + 1) state.heap) ht
    congr 1
    simpa only [childSuffix, Nat.sub_zero, ← List.range_eq_range', hs] using he

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeSelect009
