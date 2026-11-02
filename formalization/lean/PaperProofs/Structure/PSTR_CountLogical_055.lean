module

public import PaperProofs.Structure.PSTR_QueryLayout_041
public import PaperProofs.Structure.PSTR_HD_CountWorkspace_025
public import PaperProofs.Structure.PA17_HeapAncestors_001

/-! Exit-view conversion for the actual outer traversal's arrays. The
array equalities below are internal postconditions to prove from the SAME
run, never data newly supplied to original callers. ORIGINAL logicalHeap
and ORIGINAL A17 ParentHeapFor are retained, including the true sentinel. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountLogical

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PSTRQueryLayout

theorem workspace_eq {q : Nat} (full : List (Finset (Fin q))) (capWords bits : Nat) (hq : 0 < q) :
    physicalWorkspace full capWords bits = PSTRCountWorkspace.base q full capWords bits := by
  rw [PSTRCountWorkspace.base_metadata_end q full hq]
  rfl

theorem usedCount_le {q : Nat} (cache : IndexedNodeCache (Fin q)) (used : Finset (Fin q))
    (node : cache.NodeId) : (IndexedDescent.usedCounts cache used).get node ≤ q := by
  rw [IndexedDescent.usedCounts_get]
  have hs : used ∩ cache.decode node ⊆ (Finset.univ : Finset (Fin q)) := Finset.subset_univ _
  simpa only [Finset.card_univ, Fintype.card_fin] using Finset.card_le_card hs

theorem encodedNode_le {Tool : Type*} (cache : IndexedNodeCache Tool) (node : Option cache.NodeId) :
    encodedNode cache node ≤ cache.nodes.size := by
  cases node with
  | none => exact Nat.zero_le _
  | some node => exact Nat.succ_le_of_lt node.isLt

theorem counts_view {bits q : Nat} (full : List (Finset (Fin q))) (capWords : Nat)
    (used : Finset (Fin q)) (heap : BitVec bits → BitVec bits) (hq : 0 < q) (hqfit : Fits bits q)
    (counts : ∀ node : (prepareNormalization q full).indexed.NodeId,
      heap (BitVec.ofNat bits (countsBase (PSTRCountWorkspace.base q full capWords bits) + node.val)) =
        BitVec.ofNat bits ((IndexedDescent.usedCounts (prepareNormalization q full).indexed used).get node)) :
    ∀ node : (prepareNormalization q full).indexed.NodeId,
      logicalHeap q capWords heap (countsBase (logicalWorkspace full capWords) + node.val) =
        (IndexedDescent.usedCounts (prepareNormalization q full).indexed used).get node := by
  intro node
  have haddr : countsBase (logicalWorkspace full capWords) + node.val =
      logicalWorkspace full capWords + (16 + node.val) := by unfold countsBase; omega
  rw [haddr, logical_suffix_word full capWords heap hq, workspace_eq full capWords bits hq]
  have hp : PSTRCountWorkspace.base q full capWords bits + (16 + node.val) =
      countsBase (PSTRCountWorkspace.base q full capWords bits) + node.val := by unfold countsBase; omega
  rw [hp, counts node, BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt ((usedCount_le (prepareNormalization q full).indexed used node).trans_lt hqfit)

theorem parents_view {bits q : Nat} (full : List (Finset (Fin q))) (capWords : Nat)
    (heap : BitVec bits → BitVec bits) (hq : 0 < q)
    (hsize : Fits bits (prepareNormalization q full).indexed.nodes.size)
    (sentinel : heap (BitVec.ofNat bits (parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size)) = BitVec.ofNat bits 0)
    (parents : ∀ node : (prepareNormalization q full).indexed.NodeId,
      heap (BitVec.ofNat bits (parentsBase (PSTRCountWorkspace.base q full capWords bits)
        (prepareNormalization q full).indexed.nodes.size + node.val + 1)) =
          BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed
            ((prepareNormalization q full).indexed.parents.get node))) :
    PA17HeapAncestors001.ParentHeapFor (prepareNormalization q full).indexed
      (parentsBase (logicalWorkspace full capWords) (prepareNormalization q full).indexed.nodes.size)
      (logicalHeap q capWords heap) := by
  constructor
  · have ha : parentsBase (logicalWorkspace full capWords) (prepareNormalization q full).indexed.nodes.size =
        logicalWorkspace full capWords + (16 + (prepareNormalization q full).indexed.nodes.size) := by
      unfold parentsBase countsBase
      omega
    rw [ha, logical_suffix_word full capWords heap hq, workspace_eq full capWords bits hq]
    have hp : PSTRCountWorkspace.base q full capWords bits + (16 + (prepareNormalization q full).indexed.nodes.size) =
        parentsBase (PSTRCountWorkspace.base q full capWords bits) (prepareNormalization q full).indexed.nodes.size := by
      unfold parentsBase countsBase
      omega
    rw [hp, sentinel]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod]
  · intro node
    have ha : parentsBase (logicalWorkspace full capWords) (prepareNormalization q full).indexed.nodes.size +
        (node.val + 1) = logicalWorkspace full capWords + (16 + (prepareNormalization q full).indexed.nodes.size + node.val + 1) := by
      unfold parentsBase countsBase
      omega
    rw [ha, logical_suffix_word full capWords heap hq, workspace_eq full capWords bits hq]
    have hp : PSTRCountWorkspace.base q full capWords bits + (16 + (prepareNormalization q full).indexed.nodes.size + node.val + 1) =
        parentsBase (PSTRCountWorkspace.base q full capWords bits) (prepareNormalization q full).indexed.nodes.size + node.val + 1 := by
      unfold parentsBase countsBase
      omega
    rw [hp, parents node, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((encodedNode_le (prepareNormalization q full).indexed _).trans_lt hsize)

end PaperProofs.Structure.LaminarTree.PSTRCountLogical
