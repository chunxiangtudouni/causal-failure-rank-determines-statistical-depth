module

public import PaperProofs.Structure.PSTR_LeafCountEntry_062
public import PaperProofs.Structure.PSTR_HD_CountSlots_050

/-! Actual outer test/leaf/restore followed by the frozen actual node loop.
All node-kernel data duties follow from the original Ready invariant and
preceding real instructions in this SAME containing run. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRNodeCounted

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace

structure Counted {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (origin capWords : Nat) (node : (prepareNormalization q full).indexed.NodeId)
    (initial result : WordState bits) : Prop where
  active : result.halted = false
  pc : result.pc = BitVec.ofNat bits (5 * (origin + 393))
  rep : HeapRepresents q full capWords configuration result.heap
  value : result.register .value = BitVec.ofNat bits
    ((IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used).get node)
  address : result.register .address = BitVec.ofNat bits (countsBase (base q full capWords bits) + node.val)
  index : result.register .index = BitVec.ofNat bits node.val
  array : ∀ child < (prepareNormalization q full).indexed.nodes.size,
    result.heap (BitVec.ofNat bits (countsBase (base q full capWords bits) + child)) =
      if child = node.val then BitVec.ofNat bits
        ((IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used).get node)
      else initial.heap (BitVec.ofNat bits (countsBase (base q full capWords bits) + child))
  frame : ∀ physical, Fits bits physical →
    (physical < base q full capWords bits ∨ base q full capWords bits + 8 ≤ physical) →
    physical ≠ countsBase (base q full capWords bits) + node.val →
    result.heap (BitVec.ofNat bits physical) = initial.heap (BitVec.ofNat bits physical)
  degree : result.heap (BitVec.ofNat bits (base q full capWords bits + 4)) =
    BitVec.ofNat bits ((prepareNormalization q full).indexed.children.get node).size

theorem actual_counted {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (origin : Nat)
    (node : (prepareNormalization q full).indexed.NodeId)
    (state : WordState (indexWidth 32 full.length q)) (whole : List PackingOp)
    (hc : PSTROuterCountCode.Contains whole origin)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (ready : PSTRCountReady.Ready full configuration origin
      (capacityWords 8192 full.length q (treeSize q full)) node.val state) :
    ∃ steps ≤ 302 + 114 * ((prepareNormalization q full).indexed.children.get node).size,
      Counted full configuration origin (capacityWords 8192 full.length q (treeSize q full)) node state
        (packingRun (callInput q full command) whole steps state) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let B := countsBase workspace
  let offset := PSTRCountChildRows.flatOffset full node.val
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let leaf := (IndexedUsedCounts.leafBitmap (prepareNormalization q full).indexed configuration.used).get node
  let rom := callInput q full command
  obtain ⟨entrySteps, hentrySteps, entryResult⟩ := PSTRLeafCountEntry.actual_entry full command configuration origin node
    state whole hc hwords hpcfit hq ready
  let entering := packingRun rom whole entrySteps state
  rcases entryResult with ⟨eactive, epc, eheap, eold, eindex, eoffset, eleaf⟩
  have heap_eq : entering.heap = state.heap := eheap
  have erep : HeapRepresents q full capWords configuration entering.heap := by rw [eheap]; exact ready.rep
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have dimensions := PSTROriginalCountRoom.dimension_rooms full
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have hw : Fits bits (workspace + 7) := (show workspace + 7 ≤ workspace + 15 by omega).trans_lt rooms.1
  have hfit : Fits bits (B + (prepareNormalization q full).indexed.nodes.size) :=
    (Nat.le_add_right _ (prepareNormalization q full).indexed.nodes.size).trans_lt rooms.2
  have hbase : workspace + 16 ≤ B := Nat.le_refl _
  have previous : ∀ child : (prepareNormalization q full).indexed.NodeId, child.val < node.val →
      entering.heap (BitVec.ofNat bits (B + child.val)) =
        BitVec.ofNat bits ((IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used).get child) := by
    intro child hchild
    rw [eheap]
    exact ready.counts child hchild
  have row : ∀ position (hp : position < degree),
      (PSTRStaticLayout.childWords q full).getD (offset + position) 0 =
        (((prepareNormalization q full).indexed.children.get node)[position]).val :=
    PSTRCountChildRows.row_alignment full node
  have hoff : offset + degree ≤ PSTRStaticLayout.edgeCount q full := PSTRCountChildRows.row_bound full node
  have kernel := PSTROuterCountCode.kernel_at whole origin hc
  have n := PSTRCountKernel.active_node_usedCount full command configuration capWords B offset (origin + 123)
    configuration.used node entering whole kernel.bound kernel.code hwords hpcfit (by omega) hq hl raw.1 dimensions.2.2.2.2
    (PSTROriginalCountRoom.bitmap_room full 8192 hq)
    (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) hw hbase hfit
    eold eoffset eindex eleaf hoff row previous erep epc eactive
  have nd := PSTRCountKernel.active_node_degree full command configuration capWords B offset (origin + 123) leaf node
    entering whole kernel.bound kernel.code hwords hpcfit (by omega) hq raw.1
    (PSTROriginalCountRoom.bitmap_room full 8192 hq)
    (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) hw hbase hfit
    eold eoffset eindex eleaf hoff erep epc eactive
  rcases n with ⟨nactive, npc, nvalue, naddress, nindex, nrep, narray, nframe⟩
  refine ⟨entrySteps + PSTRCountKernel.activeSteps degree, ?_, ?_⟩
  · unfold PSTRCountKernel.activeSteps
    omega
  · rw [PSTRWordSegments.run_add]
    constructor
    · exact nactive
    · simpa only [Nat.add_assoc] using npc
    · exact nrep
    · exact nvalue
    · exact naddress
    · exact nindex
    · intro child hchild
      have har := narray child hchild
      rw [heap_eq] at har
      exact har
    · intro physical hphysical hout hne
      exact (nframe physical hphysical hout hne).trans (congrFun eheap _)
    · exact nd

end PaperProofs.Structure.LaminarTree.PSTRNodeCounted
