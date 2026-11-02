module

public import PaperProofs.Structure.PA17_A19QueryBridge_RuntimeTests_010d
public import PaperProofs.Structure.PSTR_RepairHeap_024

/-! Original-model semantic target and preservation of the original physical
representation under the actual bounded header scratch stores. These are
internal composition lemmas, not a fixed-run or caller eligibility premise. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims PA17TagBridge001

def rawGood (heap : Nat → Nat) (entryBase countsBase size : Nat) : Bool :=
  decide (heap entryBase ≠ 0) && acceptPrefix heap entryBase countsBase size

def rawBad (heap : Nat → Nat) (entryBase countsBase parentBase size encoded : Nat) : Bool :=
  (rawGood heap entryBase countsBase size && decide (encoded ≠ 0)) &&
    chainPrefix heap entryBase countsBase parentBase size encoded

theorem rawGood_correct {q : Nat} (cache : IndexedNodeCache (Fin q))
    (heap : Nat → Nat) (entryBase countsBase : Nat) (counts : IndexedCapacity cache)
    (entry : IndexedEntry.FixedEntry cache)
    (hcounts : ∀ node : cache.NodeId, heap (countsBase + node.val) = counts.get node)
    (hentry : TagFirstRep cache heap entryBase entry) :
    rawGood heap entryBase countsBase cache.nodes.size = IndexedQuery.accepts cache counts entry :=
  acceptPrefix_correct cache heap entryBase countsBase counts entry hcounts hentry

theorem rawBad_correct {q : Nat} (cache : IndexedNodeCache (Fin q))
    (heap : Nat → Nat) (entryBase countsBase parentBase : Nat) (counts : IndexedCapacity cache)
    (entry : IndexedEntry.FixedEntry cache) (current : Option cache.NodeId)
    (hcounts : ∀ node : cache.NodeId, heap (countsBase + node.val) = counts.get node)
    (hentry : TagFirstRep cache heap entryBase entry)
    (hparents : PA17HeapAncestors001.ParentHeapFor cache parentBase heap) :
    rawBad heap entryBase countsBase parentBase cache.nodes.size (encodedNode cache current) =
      IndexedQuery.extensionTest cache counts current entry := by
  rw [rawBad, rawGood_correct cache heap entryBase countsBase counts entry hcounts hentry]
  cases entry with
  | void => simp only [IndexedQuery.accepts, Bool.false_and, IndexedQuery.extensionTest]
  | vector capacity =>
    rw [chainPrefix_correct cache heap entryBase countsBase parentBase cache.nodes.size
      counts capacity current hcounts hentry.2 hparents]
    cases current with
    | none => simp only [encodedNode, ne_eq, not_true_eq_false, decide_false, Bool.and_false,
        Bool.false_and, IndexedQuery.extensionTest]
    | some node =>
      simp only [encodedNode, ne_eq, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
        not_false_eq_true, decide_true, Bool.and_true]
      rfl

theorem storeSlot_prefix_represents {bits q : Nat} (rom : PhysicalROM)
    (full : List (Finset (Fin q))) (configuration : Configuration q) (capWords offset : Nat)
    (source : Register) (state : WordState bits) (hb : 0 < bits) (hq : 0 < q)
    (rep : HeapRepresents q full capWords configuration state.heap)
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hr : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits)
      (treeSize q full) + 16))
    (hh : state.register .address = BitVec.ofNat bits
      (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)))
    (ho : 8 ≤ offset) (hu : offset < 16) (count : Nat) (hc : count ≤ 3) :
    HeapRepresents q full capWords configuration
      (executeOps rom ((storeSlot offset source).take count) state).heap := by
  let header := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) (treeSize q full)
  refine PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (header + 8)
    state.heap _ hb hq rep bitmap hr
    ((show header + 8 + 3 ≤ header + 16 by omega).trans_lt hroom) ?_ ?_
  · unfold header PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      PSTRQueryLayout.physicalWorkspace PSTRStaticHeap.metadataAddress
    omega
  · intro physical hp
    exact storeSlot_prefix_leading_frame rom offset header source state hh hroom ho hu physical hp count hc

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
