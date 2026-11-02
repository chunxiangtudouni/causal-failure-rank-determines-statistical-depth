module

public import PaperProofs.Structure.PSTR_ParentCopy_043
public import PaperProofs.Structure.PSTR_CountAdvance_049

/-! Original persistent-heap preservation for the real outer-loop writes.
These are properties of the executed blocks, including every proper prefix;
they do not initialize scratch or add fields to HeapRepresents. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTROuterMemory

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout

theorem represents_of_workspace_frame {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (old fresh : BitVec bits → BitVec bits)
    (hb : 0 < bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration old)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRCountWorkspace.base q full capWords bits + 3))
    (hframe : ∀ physical < PSTRCountWorkspace.base q full capWords bits,
      fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical)) :
    HeapRepresents q full capWords configuration fresh := by
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords
    (PSTRCountWorkspace.base q full capWords bits) old fresh hb hq rep bitmap hr hroom ?_ hframe
  rw [PSTRCountWorkspace.base_metadata_end q full hq]
  unfold PSTRStaticHeap.metadataAddress physicalHeaderWords
  omega

theorem sentinel_prefix_rep {bits q : Nat} (full : List (Finset (Fin q))) (rom : PhysicalROM)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 0 < bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (parentsBase (PSTRCountWorkspace.base q full capWords bits) (treeSize q full)))
    (hbase : state.register .old = BitVec.ofNat bits (countsBase (PSTRCountWorkspace.base q full capWords bits)))
    (count : Nat) (hc : count ≤ 5) :
    HeapRepresents q full capWords configuration
      (executeOps rom (PSTRParentSentinel.program.take count) state).heap := by
  have ht := (PSTRStaticHeap.headers full configuration capWords state.heap rep).1
  apply represents_of_workspace_frame full configuration capWords state.heap _ hb hq rep bitmap hr
    ((show PSTRCountWorkspace.base q full capWords bits + 3 ≤
      parentsBase (PSTRCountWorkspace.base q full capWords bits) (treeSize q full) by
        unfold parentsBase countsBase; omega).trans_lt hroom)
  intro physical hp
  exact PSTRParentSentinel.prefix_frame rom (PSTRCountWorkspace.base q full capWords bits)
    (treeSize q full) state hbase ht hroom physical (by unfold parentsBase countsBase; omega) count hc

theorem parent_prefix_rep {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (node : (prepareNormalization q full).indexed.NodeId) (hb : 8 ≤ bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q)) (hN : Fits bits full.length)
    (hi : state.register .index = BitVec.ofNat bits node.val)
    (hroom : Fits bits (parentsBase (PSTRCountWorkspace.base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + (prepareNormalization q full).indexed.nodes.size))
    (count : Nat) (hc : count ≤ 50) :
    HeapRepresents q full capWords configuration
      (executeOps (callInput q full command) (PSTRParentCopy.program.take count) state).heap := by
  apply represents_of_workspace_frame full configuration capWords state.heap _ (by omega) hq rep bitmap hr
    ((show PSTRCountWorkspace.base q full capWords bits + 3 ≤
      parentsBase (PSTRCountWorkspace.base q full capWords bits)
        (prepareNormalization q full).indexed.nodes.size + (prepareNormalization q full).indexed.nodes.size by
          unfold parentsBase countsBase; omega).trans_lt hroom)
  intro physical hp
  exact PSTRParentCopy.prefix_frame full command configuration capWords state node hb hq rep hN hi hroom
    physical (by unfold parentsBase countsBase; omega) count hc

theorem locator_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) (hc : count ≤ 19) :
    (executeOps rom (PSTRCountWorkspace.program.take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem advance_prefix_frame {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (hroom : Fits bits (PSTRCountWorkspace.base q full capWords bits + 15))
    (physical : Nat) (hfit : Fits bits physical)
    (hout : physical < PSTRCountWorkspace.base q full capWords bits + 14 ∨
      PSTRCountWorkspace.base q full capWords bits + 16 ≤ physical)
    (count : Nat) (hc : count ≤ 32) :
    (executeOps (callInput q full command) (PSTRCountAdvance.program.take count) state).heap
      (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  rw [PSTRCountAdvance.program]
  by_cases hfirst : count ≤ 19
  · rw [List.take_append_of_le_length (show count ≤ PSTRCountWorkspace.program.length from hfirst),
      locator_prefix_heap _ state count hfirst]
  · rw [List.take_append,
      List.take_of_length_le (show PSTRCountWorkspace.program.length ≤ count from by
        rw [PSTRCountWorkspace.program_length]; omega), executeOps_append, PSTRCountWorkspace.program_length]
    have locating := PSTRCountWorkspace.execute_base full command configuration capWords state hb hq rep
    exact (PSTRCountAdvance.advance_prefix_frame _ (PSTRCountWorkspace.base q full capWords bits)
      (executeOps (callInput q full command) PSTRCountWorkspace.program state) locating.1 hroom
      physical hfit hout (count - 19) (by omega)).trans (congrFun locating.2.2.2.2.2.1 _)

theorem advance_prefix_rep {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (state : WordState bits)
    (hb : 8 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRCountWorkspace.base q full capWords bits + 15))
    (count : Nat) (hc : count ≤ 32) :
    HeapRepresents q full capWords configuration
      (executeOps (callInput q full command) (PSTRCountAdvance.program.take count) state).heap := by
  apply represents_of_workspace_frame full configuration capWords state.heap _ (by omega) hq rep bitmap hr
    ((show PSTRCountWorkspace.base q full capWords bits + 3 ≤
      PSTRCountWorkspace.base q full capWords bits + 15 by omega).trans_lt hroom)
  intro physical hp
  exact advance_prefix_frame full command configuration capWords state hb hq rep hroom physical
    (hp.trans ((Nat.le_add_right _ 15).trans_lt hroom)) (Or.inl (by omega)) count hc

end PaperProofs.Structure.LaminarTree.PSTROuterMemory
