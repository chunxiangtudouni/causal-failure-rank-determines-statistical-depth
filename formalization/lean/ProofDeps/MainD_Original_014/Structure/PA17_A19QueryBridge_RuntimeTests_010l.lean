module

public import Structure.PA17_A19QueryBridge_RuntimeTests_010e

/-! A single ghost heap for same-run tests: ORIGINAL logicalHeap q C. The
Word program uses physical W/H, while all Nat semantic counts/parents/header
use the corresponding logical W/H. Physical addresses are never classified
by address<C; packed physical suffix addresses may themselves be below C. -/

@[expose] public section
set_option maxRecDepth 18000
set_option maxHeartbeats 1800000

namespace PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

theorem logical_counts_word {bits q : Nat} (full : List (Finset (Fin q))) (capWords node : Nat)
    (heap : BitVec bits → BitVec bits) (hq : 0 < q) :
    logicalHeap q capWords heap (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords) + node) =
      (heap (BitVec.ofNat bits (PSTRQueryLayout.countsBase
        (PSTRQueryLayout.physicalWorkspace full capWords bits) + node))).toNat := by
  simpa only [PSTRQueryLayout.countsBase, Nat.add_assoc] using
    PSTRQueryLayout.logical_suffix_word full capWords heap hq (16 + node)

theorem logical_parent_word {bits q : Nat} (full : List (Finset (Fin q))) (capWords size encoded : Nat)
    (heap : BitVec bits → BitVec bits) (hq : 0 < q) :
    logicalHeap q capWords heap
        (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) size + encoded) =
      (heap (BitVec.ofNat bits (PSTRQueryLayout.parentsBase
        (PSTRQueryLayout.physicalWorkspace full capWords bits) size + encoded))).toNat := by
  simpa only [PSTRQueryLayout.parentsBase, PSTRQueryLayout.countsBase, Nat.add_assoc] using
    PSTRQueryLayout.logical_suffix_word full capWords heap hq (16 + size + encoded)

theorem logical_header_word {bits q : Nat} (full : List (Finset (Fin q))) (capWords size offset : Nat)
    (heap : BitVec bits → BitVec bits) (hq : 0 < q) :
    logicalHeap q capWords heap
        (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size + offset) =
      (heap (BitVec.ofNat bits (PSTRQueryLayout.header
        (PSTRQueryLayout.physicalWorkspace full capWords bits) size + offset))).toNat := by
  simpa only [PSTRQueryLayout.header, PSTRQueryLayout.parentsBase, PSTRQueryLayout.countsBase,
    Nat.add_assoc] using PSTRQueryLayout.logical_suffix_word full capWords heap hq (16 + size + size + 1 + offset)

theorem logical_leading_frame {bits q : Nat} (full : List (Finset (Fin q))) (capWords size : Nat)
    (old fresh : BitVec bits → BitVec bits) (hb : 0 < bits) (hq : 0 < q)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) size + 16))
    (hframe : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) size + 8,
      fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical))
    (logical : Nat)
    (hl : logical < PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size + 8) :
    logicalHeap q capWords fresh logical = logicalHeap q capWords old logical := by
  let physicalHeader := PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) size
  let indexWords := 2 + (staticMetadata q full).length + 16 + size + size + 1 + 8
  refine PSTRRepairHeap.logical_frame old fresh capWords indexWords (physicalHeader + 8)
    logical hb hq hs ((show physicalHeader + 8 + 3 ≤ physicalHeader + 16 by omega).trans_lt hroom) ?_ hframe ?_
  · unfold physicalHeader indexWords PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      PSTRQueryLayout.physicalWorkspace PSTRStaticHeap.metadataAddress physicalHeaderWords
    omega
  · unfold indexWords PSTRQueryLayout.header PSTRQueryLayout.parentsBase PSTRQueryLayout.countsBase
      PSTRQueryLayout.logicalWorkspace at *
    omega

theorem logical_inputs_transfer {bits q : Nat} (full : List (Finset (Fin q)))
    (cache : IndexedNodeCache (Fin q)) (capWords size rowBase : Nat)
    (counts : IndexedCapacity cache) (row : IndexedTable.Row cache (q + 1)) (node : Option cache.NodeId)
    (old fresh : BitVec bits → BitVec bits) (hb : 0 < bits) (hq : 0 < q)
    (hs : Fits bits (4 + capWords * CapacityBits.width q))
    (hroom : Fits bits (PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) size + 16))
    (hframe : ∀ physical < PSTRQueryLayout.header (PSTRQueryLayout.physicalWorkspace full capWords bits) size + 8,
      fresh (BitVec.ofNat bits physical) = old (BitVec.ofNat bits physical))
    (hi : PA17QueryTests009.Inputs cache
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size)
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) size)
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size + 1)
      rowBase counts row node (logicalHeap q capWords old))
    (hread : PA17QueryTests009.ReadBounds cache.nodes.size q
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size)
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) size)
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size + 1)
      rowBase (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size + 8)) :
    PA17QueryTests009.Inputs cache
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size)
      (PSTRQueryLayout.countsBase (PSTRQueryLayout.logicalWorkspace full capWords))
      (PSTRQueryLayout.parentsBase (PSTRQueryLayout.logicalWorkspace full capWords) size)
      (PSTRQueryLayout.header (PSTRQueryLayout.logicalWorkspace full capWords) size + 1)
      rowBase counts row node (logicalHeap q capWords fresh) := by
  exact hi.transfer hread (logical_leading_frame full capWords size old fresh hb hq hs hroom hframe)

end PaperProofs.Structure.LaminarTree.PA17A19RuntimeTests010
