module

public import PaperProofs.Structure.PSTR_LeafEntrySafe_091
public import PaperProofs.Structure.PSTR_NodeCounted_063
public import PaperProofs.Structure.PSTR_HD_CountSlots_050

/-! Actual outer test/leaf/restore followed by the frozen actual node loop.
EVERY actual prefix preserves original HeapRep and ALL Fits physical words at/above E.
All node-kernel data duties follow from the original Ready invariant and
preceding real instructions in this SAME containing run. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountedSafe

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace

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
      (PSTRNodeCounted.Counted full configuration origin (capacityWords 8192 full.length q (treeSize q full)) node state
        (packingRun (callInput q full command) whole steps state)) ∧
      (∀ clock ≤ steps,
        let result := packingRun (callInput q full command) whole clock state
        HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
        ∀ physical, Fits (indexWidth 32 full.length q) physical →
          (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
          result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) =
            state.heap (BitVec.ofNat (indexWidth 32 full.length q) physical)) ∧
      (∀ clock < steps, PSTRCountKernel.AtSafe (callInput q full command) whole
        (endpoint (base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
          (prepareNormalization q full).indexed.nodes.size q)
        (packingRun (callInput q full command) whole clock state)) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let B := countsBase workspace
  let offset := PSTRCountChildRows.flatOffset full node.val
  let degree := ((prepareNormalization q full).indexed.children.get node).size
  let leaf := (IndexedUsedCounts.leafBitmap (prepareNormalization q full).indexed configuration.used).get node
  let rom := callInput q full command
  let heapWords := endpoint workspace (prepareNormalization q full).indexed.nodes.size q
  have hroomE : workspace + 15 < heapWords := by
    change workspace + 15 < endpoint workspace (prepareNormalization q full).indexed.nodes.size q
    rw [endpoint_eq]
    omega
  obtain ⟨entrySteps, hentrySteps, entryResult, entryPrefixes, entryFetch⟩ := PSTRLeafEntrySafe.actual_entry full command configuration origin node
    state whole heapWords hc hwords hpcfit hq hroomE ready
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
  refine ⟨entrySteps + PSTRCountKernel.activeSteps degree, ?_, ?_, ?_, ?_⟩
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

  · intro clock hclock
    dsimp only
    have high_protected (physical : Nat)
        (hh : physical < workspace ∨ endpoint workspace (prepareNormalization q full).indexed.nodes.size q ≤ physical) :
        (physical < workspace ∨ workspace + 8 ≤ physical) ∧ physical ≠ B + node.val := by
      rcases hh with low | high
      · refine ⟨Or.inl low, ?_⟩
        change physical ≠ workspace + 16 + node.val
        omega
      · rw [endpoint_eq] at high
        constructor
        · exact Or.inr (by omega)
        · have hn := node.isLt
          change physical ≠ workspace + 16 + node.val
          omega
    by_cases hentry : clock ≤ entrySteps
    · have he := entryPrefixes clock hentry
      constructor
      · rw [he]
        exact ready.rep
      · intro physical _ _
        rw [he]
    · have hremaining : clock - entrySteps ≤ PSTRCountKernel.activeSteps degree := by omega
      by_cases hproper : clock - entrySteps < PSTRCountKernel.activeSteps degree
      · have safe := PSTRCountKernel.active_node_prefix full command configuration capWords B offset (origin + 123)
          (endpoint workspace (prepareNormalization q full).indexed.nodes.size q) node entering whole
          kernel.bound kernel.code hwords hpcfit (by omega) hq raw.1
          (PSTROriginalCountRoom.bitmap_room full 8192 hq)
          (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) hw hbase hfit
          (by change workspace + 7 < endpoint workspace (prepareNormalization q full).indexed.nodes.size q; rw [endpoint_eq]; omega)
          (by change workspace + 16 + (prepareNormalization q full).indexed.nodes.size ≤ _; rw [endpoint_eq]; omega)
          eold eoffset eindex hoff erep epc eactive (clock - entrySteps) hproper
        rw [show clock = entrySteps + (clock - entrySteps) by omega, PSTRWordSegments.run_add]
        refine ⟨safe.2.2, ?_⟩
        intro physical hp hh
        exact (safe.2.1 physical hp (high_protected physical hh)).trans (congrFun eheap _)
      · have he : clock = entrySteps + PSTRCountKernel.activeSteps degree := by omega
        rw [he, PSTRWordSegments.run_add]
        refine ⟨nrep, ?_⟩
        intro physical hp hh
        have shield := high_protected physical hh
        exact (nframe physical hp shield.1 shield.2).trans (congrFun eheap _)

  · intro clock hclock
    by_cases hentryClock : clock < entrySteps
    · exact entryFetch clock hentryClock
    · have hproper : clock - entrySteps < PSTRCountKernel.activeSteps degree := by omega
      have safe := PSTRCountKernel.active_node_prefix full command configuration capWords B offset (origin + 123)
        heapWords node entering whole kernel.bound kernel.code hwords hpcfit (by omega) hq raw.1
        (PSTROriginalCountRoom.bitmap_room full 8192 hq)
        (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) hw hbase hfit
        (by change workspace + 7 < heapWords; omega)
        (by
          change workspace + 16 + (prepareNormalization q full).indexed.nodes.size ≤ endpoint workspace (prepareNormalization q full).indexed.nodes.size q
          rw [endpoint_eq]
          omega)
        eold eoffset eindex hoff erep epc eactive (clock - entrySteps) hproper
      rw [show clock = entrySteps + (clock - entrySteps) by omega, PSTRWordSegments.run_add]
      exact safe.1

end PaperProofs.Structure.LaminarTree.PSTRCountedSafe
