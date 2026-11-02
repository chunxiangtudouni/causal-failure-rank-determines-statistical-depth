module

public import Structure.PSTR_HD_StaticLayout_019

/-! Word-for-word refinement of the ORIGINAL HeapRepresents to its actual
cached metadata addresses. No copied tree or extra input field is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRStaticHeap

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PSTRStaticLayout

variable {bits q : Nat}

def metadataAddress (q capWords bits position : Nat) : Nat :=
  physicalHeaderWords + packedCapacityWords q capWords bits + 2 + position

/-- Adding the fixed header commutes with the original Word truncation.
Consequently this exact-address identity requires no extra Fits premise. -/
theorem dataHeap_word (heap : BitVec bits → BitVec bits) (address : Nat) :
    dataHeap heap (BitVec.ofNat bits address) =
      heap (BitVec.ofNat bits (physicalHeaderWords + address)) := by
  unfold dataHeap
  apply congrArg heap
  rw [← BitVec.ofNat_add_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq, BitVec.ofNat_add_ofNat]

theorem logical_suffix (heap : BitVec bits → BitVec bits) (capWords offset : Nat)
    (hq : 0 < q) :
    logicalHeap q capWords heap (capWords + offset) =
      (heap (BitVec.ofNat bits (physicalHeaderWords + packedCapacityWords q capWords bits + offset))).toNat := by
  have hn : ¬ capWords + offset < capWords := by omega
  simp only [logicalHeap, ne_of_gt hq, ite_false, unpackHeap, hn, Nat.add_sub_cancel_left]
  rw [dataHeap_word]
  congr 3
  omega

theorem headers (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits)
    (rep : HeapRepresents q full capWords configuration heap) :
    heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (treeSize q full) ∧
    heap (BitVec.ofNat bits 1) = BitVec.ofNat bits capWords ∧
    heap (BitVec.ofNat bits 2) = BitVec.ofNat bits (packedCapacityWords q capWords bits) ∧
    heap (BitVec.ofNat bits 3) = BitVec.ofNat bits bits := by
  exact ⟨by simpa using congrArg (BitVec.ofNat bits) rep.1,
    by simpa using congrArg (BitVec.ofNat bits) rep.2.1,
    by simpa using congrArg (BitVec.ofNat bits) rep.2.2.1,
    by simpa using congrArg (BitVec.ofNat bits) rep.2.2.2.1⟩

theorem stage_failed (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap) :
    heap (BitVec.ofNat bits (physicalHeaderWords + packedCapacityWords q capWords bits)) = BitVec.ofNat bits configuration.stage ∧
    heap (BitVec.ofNat bits (physicalHeaderWords + packedCapacityWords q capWords bits + 1)) = BitVec.ofNat bits (bit configuration.failed) := by
  have hs := rep.2.2.2.2.1
  have hf := rep.2.2.2.2.2.1
  have hs' : logicalHeap q capWords heap (capWords + 0) = configuration.stage := by simpa using hs
  rw [logical_suffix heap capWords 0 hq, Nat.add_zero] at hs'
  rw [logical_suffix heap capWords 1 hq] at hf
  exact ⟨by simpa using congrArg (BitVec.ofNat bits) hs',
    by simpa using congrArg (BitVec.ofNat bits) hf⟩

theorem metadata_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (position : Nat) (hp : position < (staticMetadata q full).length) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits position)) =
      BitVec.ofNat bits (staticMetadata q full)[position] := by
  have hm := rep.2.2.2.2.2.2.1 position hp
  have hm' : logicalHeap q capWords heap (capWords + (2 + position)) = (staticMetadata q full)[position] := by
    simpa only [Nat.add_assoc] using hm
  rw [logical_suffix heap capWords (2 + position) hq] at hm'
  simpa only [metadataAddress, Nat.add_assoc, BitVec.ofNat_toNat, BitVec.setWidth_eq] using congrArg (BitVec.ofNat bits) hm'

theorem metadata_toNat (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (position : Nat) (hp : position < (staticMetadata q full).length) :
    (heap (BitVec.ofNat bits (metadataAddress q capWords bits position))).toNat =
      (staticMetadata q full)[position] := by
  have hm := rep.2.2.2.2.2.2.1 position hp
  have hm' : logicalHeap q capWords heap (capWords + (2 + position)) = (staticMetadata q full)[position] := by
    simpa only [Nat.add_assoc] using hm
  rw [logical_suffix heap capWords (2 + position) hq] at hm'
  simpa only [metadataAddress, Nat.add_assoc] using hm'

theorem chunk_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (segment position : Nat) (hs : segment < 9)
    (hp : position < (chunks q full hq)[segment].length) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full segment + position))) =
      BitVec.ofNat bits (chunks q full hq)[segment][position] := by
  have hb := chunk_in_bounds q full hq segment position hs hp
  have he := metadata_chunk_getD q full hq segment position hs hp
  rw [List.getD_eq_getElem _ _ hb] at he
  rw [metadata_word full configuration capWords heap hq rep _ hb, he]

theorem chunk_toNat (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (segment position : Nat) (hs : segment < 9)
    (hp : position < (chunks q full hq)[segment].length) :
    (heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full segment + position)))).toNat =
      (chunks q full hq)[segment][position] := by
  have hb := chunk_in_bounds q full hq segment position hs hp
  have he := metadata_chunk_getD q full hq segment position hs hp
  rw [List.getD_eq_getElem _ _ hb] at he
  rw [metadata_toNat full configuration capWords heap hq rep _ hb, he]

theorem child_count_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits 0)) = BitVec.ofNat bits (edgeCount q full) := by
  simpa [chunks, offset] using chunk_word full configuration capWords heap hq rep 0 0 (by decide) (by simp [chunks])

theorem parent_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (node : (prepareNormalization q full).indexed.NodeId) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 1 + node.val))) =
      BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get node)) := by
  simpa [chunks, mapped_finRange_get] using chunk_word full configuration capWords heap hq rep 1 node.val (by decide) (by simp [chunks])

theorem degree_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (node : (prepareNormalization q full).indexed.NodeId) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 2 + node.val))) =
      BitVec.ofNat bits ((prepareNormalization q full).indexed.children.get node).size := by
  simpa [chunks, mapped_finRange_get] using chunk_word full configuration capWords heap hq rep 2 node.val (by decide) (by simp [chunks])

theorem child_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap) (position : Fin (edgeCount q full)) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 3 + position.val))) =
      BitVec.ofNat bits (childWords q full)[position.val] := by
  simpa [chunks] using chunk_word full configuration capWords heap hq rep 3 position.val (by decide) position.isLt

theorem card_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (node : (prepareNormalization q full).indexed.NodeId) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 4 + node.val))) =
      BitVec.ofNat bits ((prepareNormalization q full).indexed.metadata.cardinalities.get node) := by
  simpa [chunks, mapped_finRange_get] using chunk_word full configuration capWords heap hq rep 4 node.val (by decide) (by simp [chunks])

theorem internal_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (node : (prepareNormalization q full).indexed.NodeId) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 5 + node.val))) =
      BitVec.ofNat bits (bit ((prepareNormalization q full).indexed.metadata.isInternal.get node)) := by
  simpa [chunks, mapped_finRange_get] using chunk_word full configuration capWords heap hq rep 5 node.val (by decide) (by simp [chunks])

theorem leaf_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap)
    (node : (prepareNormalization q full).indexed.NodeId) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 6 + node.val))) =
      BitVec.ofNat bits (match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get node with
        | none => 0 | some tool => tool.val + 1) := by
  have he := chunk_word full configuration capWords heap hq rep 6 node.val (by decide) (by simp [chunks])
  change heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 6 + node.val))) =
    BitVec.ofNat bits (((List.finRange (prepareNormalization q full).indexed.nodes.size).map
      (fun other => match (IndexedDescent.leafTools (prepareNormalization q full).indexed).get other with
        | none => 0 | some tool => tool.val + 1))[node.val]) at he
  rw [mapped_finRange_get] at he
  exact he

theorem stage_node_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap) (stage : Fin full.length) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 7 + stage.val))) =
      BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed
        ((IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage)) := by
  simpa [chunks, mapped_finRange_get] using chunk_word full configuration capWords heap hq rep 7 stage.val (by decide) (by simp [chunks])

theorem tool_node_word (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration heap) (tool : Fin q) :
    heap (BitVec.ofNat bits (metadataAddress q capWords bits (offset q full 8 + tool.val))) =
      BitVec.ofNat bits ((IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool).val.succ := by
  simpa [chunks, mapped_finRange_get] using chunk_word full configuration capWords heap hq rep 8 tool.val (by decide) (by simp [chunks])

end PaperProofs.Structure.LaminarTree.PSTRStaticHeap

