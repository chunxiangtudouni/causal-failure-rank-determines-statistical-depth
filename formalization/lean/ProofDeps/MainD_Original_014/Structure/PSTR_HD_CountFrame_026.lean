module

public import Structure.PSTR_HD_CountWorkspace_025
public import Structure.PSTR_RepairHeap_024

/-! Reuse the original packed-prefix frame theorem for actual count scratch
stores. Metadata/capacities/table stay in the same physical heap. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountWorkspace

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRStaticHeap

theorem store_prefix_frame {bits : Nat} (heap : BitVec bits → BitVec bits)
    (cutoff address : Nat) (value : BitVec bits) (hcut : cutoff ≤ address) (ha : Fits bits address) :
    ∀ physical < cutoff,
      (Function.update heap (BitVec.ofNat bits address) value) (BitVec.ofNat bits physical) =
        heap (BitVec.ofNat bits physical) := by
  intro physical hp
  have hf : Fits bits physical := (hp.trans_le hcut).trans ha
  have hn : BitVec.ofNat bits physical ≠ BitVec.ofNat bits address :=
    (ofNat_injective_of_fit physical address hf ha).not.mpr (by omega)
  rw [Function.update_of_ne hn]

theorem store_other {bits : Nat} (heap : BitVec bits → BitVec bits)
    (address physical : Nat) (value : BitVec bits) (ha : Fits bits address)
    (hp : Fits bits physical) (hne : physical ≠ address) :
    (Function.update heap (BitVec.ofNat bits address) value) (BitVec.ofNat bits physical) =
      heap (BitVec.ofNat bits physical) := by
  rw [Function.update_of_ne ((ofNat_injective_of_fit physical address hp ha).not.mpr hne)]

theorem scratch_store_represents {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords address : Nat)
    (heap : BitVec bits → BitVec bits) (value : BitVec bits)
    (hb : 0 < bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 3))
    (ha : Fits bits address) (hafter : base q full capWords bits ≤ address) :
    HeapRepresents q full capWords configuration
      (Function.update heap (BitVec.ofNat bits address) value) := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords
    (base q full capWords bits) heap _ hb hq rep bitmap hr hw ?_
    (store_prefix_frame heap _ address value hafter ha)
  rw [base_metadata_end q full hq capWords bits]
  unfold metadataAddress physicalHeaderWords
  omega

theorem scratch_logical_frame {bits q : Nat} (full : List (Finset (Fin q)))
    (capWords address logical : Nat) (heap : BitVec bits → BitVec bits) (value : BitVec bits)
    (hb : 0 < bits) (hq : 0 < q)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hw : Fits bits (base q full capWords bits + 3))
    (ha : Fits bits address) (hafter : base q full capWords bits ≤ address)
    (hl : logical < capWords + (2 + (staticMetadata q full).length)) :
    logicalHeap q capWords (Function.update heap (BitVec.ofNat bits address) value) logical =
      logicalHeap q capWords heap logical := by
  apply PSTRRepairHeap.logical_frame heap _ capWords (2 + (staticMetadata q full).length)
    (base q full capWords bits) logical hb hq hr hw ?_
    (store_prefix_frame heap _ address value hafter ha) hl
  rw [base_metadata_end q full hq capWords bits]
  unfold metadataAddress physicalHeaderWords
  omega

theorem count_store_workspace_frame {bits : Nat} (heap : BitVec bits → BitVec bits)
    (workspace countsBase node slot : Nat) (value : BitVec bits)
    (hbase : workspace + 16 ≤ countsBase) (hs : slot < 8) (hfit : Fits bits (countsBase + node)) :
    (Function.update heap (BitVec.ofNat bits (countsBase + node)) value)
      (BitVec.ofNat bits (workspace + slot)) = heap (BitVec.ofNat bits (workspace + slot)) := by
  exact store_prefix_frame heap countsBase _ value (by omega) hfit _ (by omega)

theorem workspace_store_counts_frame {bits : Nat} (heap : BitVec bits → BitVec bits)
    (workspace countsBase node slot : Nat) (value : BitVec bits)
    (hbase : workspace + 16 ≤ countsBase) (hs : slot < 8) (hfit : Fits bits (countsBase + node)) :
    (Function.update heap (BitVec.ofNat bits (workspace + slot)) value)
      (BitVec.ofNat bits (countsBase + node)) = heap (BitVec.ofNat bits (countsBase + node)) := by
  exact store_other heap _ _ value ((show workspace + slot ≤ countsBase + node by omega).trans_lt hfit)
    hfit (by omega)

end PaperProofs.Structure.LaminarTree.PSTRCountWorkspace
