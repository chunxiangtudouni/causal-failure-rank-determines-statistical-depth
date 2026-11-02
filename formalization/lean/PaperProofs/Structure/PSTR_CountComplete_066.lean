module

public import PaperProofs.Structure.PSTR_CountIteration_065

/-! Complete actual positive-q outer traversal in the SAME containing
program, beginning at the original raw call. All count/parent words are
materialized by the real loop; no caller is supplied a prepared array. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountComplete

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace PSTRCountReady

theorem ready_zero_in {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp)
    (cb : PSTRBootstrapSlices.Contains whole) (co : PSTROuterCountCode.Contains whole 61)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration heap) :
    Ready full configuration 61 (capacityWords 8192 full.length q (treeSize q full)) 0
      (packingRun (callInput q full command) whole
        (8 * CapacityBits.width q + 61) (packingInitial heap)) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := callInput q full command
  let boot := packingRun rom whole (8 * CapacityBits.width q + 56) (packingInitial heap)
  let finished := executeOps rom PSTRParentSentinel.program boot
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have h := PSTRBootstrapIn.actual_bootstrap whole cb hwords hpcfit full command configuration capWords heap
    (by omega) hq rep raw.1 raw.2.1 raw.2.2 rooms.1
  have original_rep := PSTRBootstrapIn.heap_represents whole cb hwords hpcfit full command configuration capWords heap
    (by omega) hq rep raw.1 raw.2.1 raw.2.2 rooms.1
    (PSTROriginalCountRoom.bitmap_room full 8192 hq)
    (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide))
  have bp : HeapRepresents q full capWords configuration boot.heap := original_rep
  have hbase : boot.register .old = BitVec.ofNat bits (countsBase workspace) := h.2.2.1
  have ht : boot.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using (PSTRStaticHeap.headers full configuration capWords boot.heap bp).1
  have hroom : Fits bits (parentsBase workspace size) := (Nat.le_add_right _ size).trans_lt rooms.2
  have hs := PSTROuterCountCode.sentinel_at whole 61 co
  have run : packingRun rom whole (8 * CapacityBits.width q + 61) (packingInitial heap) = finished := by
    rw [show 8 * CapacityBits.width q + 61 = (8 * CapacityBits.width q + 56) + 5 by omega,
      PSTRWordSegments.run_add,
      PSTRParentSentinel.containing_run rom whole 61 hs.bound hs.code
        hwords hpcfit boot h.2.1 h.1]
  rw [run]
  constructor
  · have hp : Fits bits (parentsBase workspace (treeSize q full)) := by
      simpa only [treeSize, ne_of_gt hq, ite_false] using hroom
    have rp := PSTROuterMemory.sentinel_prefix_rep full rom configuration capWords boot (by omega) hq bp
      (PSTROriginalCountRoom.bitmap_room full 8192 hq)
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) hp hbase 5 le_rfl
    rw [List.take_of_length_le (show PSTRParentSentinel.program.length ≤ 5 by rw [PSTRParentSentinel.program_length])] at rp
    exact rp
  · rw [executeOps_halted, h.1]
  · rw [executeOps_pc rom PSTRParentSentinel.program boot PSTRParentSentinel.program_straight,
      h.2.1, PSTRParentSentinel.program_length, BitVec.ofNat_add_ofNat]
  · exact Nat.zero_le _
  · exact (PSTRParentSentinel.execute_registers rom workspace size boot hbase ht).2.2.2.2
  · intro offset hoffset
    have hf := PSTRParentSentinel.prefix_frame rom workspace size boot hbase ht hroom
      (workspace + 12 + offset) (by unfold parentsBase countsBase; omega) 5 le_rfl
    rw [List.take_of_length_le (show PSTRParentSentinel.program.length ≤ 5 by rw [PSTRParentSentinel.program_length])] at hf
    rw [hf]
    simpa only [PSTRCountChildRows.offset_zero, ite_self] using h.2.2.2.2.2.2.1 offset hoffset
  · intro child hchild
    omega
  · exact PSTRParentSentinel.sentinel rom workspace size boot hbase ht
  · intro child hchild
    omega


structure Complete {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (origin capWords : Nat) (result : WordState bits) : Prop where
  active : result.halted = false
  pc : result.pc = BitVec.ofNat bits (5 * (origin + 478))
  rep : HeapRepresents q full capWords configuration result.heap
  index : result.register .index = BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size
  slots : ∀ offset < 4, result.heap (BitVec.ofNat bits (base q full capWords bits + 12 + offset)) =
    if offset = 0 then BitVec.ofNat bits (CapacityBits.width q)
    else if offset = 1 then lowMask bits (CapacityBits.width q)
    else if offset = 2 then BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size
    else BitVec.ofNat bits (PSTRStaticLayout.edgeCount q full)
  counts : ∀ child : (prepareNormalization q full).indexed.NodeId,
    result.heap (BitVec.ofNat bits (countsBase (base q full capWords bits) + child.val)) =
      BitVec.ofNat bits ((IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used).get child)
  sentinel : result.heap (BitVec.ofNat bits (parentsBase (base q full capWords bits)
    (prepareNormalization q full).indexed.nodes.size)) = BitVec.ofNat bits 0
  parents : ∀ child : (prepareNormalization q full).indexed.NodeId,
    result.heap (BitVec.ofNat bits (parentsBase (base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + child.val + 1)) =
        BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed
          ((prepareNormalization q full).indexed.parents.get child))

theorem finish_from_ready {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (origin : Nat) (whole : List PackingOp)
    (hc : PSTROuterCountCode.Contains whole origin)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length)) (hq : 0 < q)
    (state : WordState (indexWidth 32 full.length q))
    (ready : Ready full configuration origin (capacityWords 8192 full.length q (treeSize q full))
      (prepareNormalization q full).indexed.nodes.size state) :
    Complete full configuration origin (capacityWords 8192 full.length q (treeSize q full))
      (packingRun (callInput q full command) whole 5 state) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let rom := callInput q full command
  have dimensions := PSTROriginalCountRoom.dimension_rooms full
  have ht : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using
      (PSTRStaticHeap.headers full configuration capWords state.heap ready.rep).1
  have hsize : Fits bits (prepareNormalization q full).indexed.nodes.size :=
    (Nat.le_succ _).trans_lt dimensions.2.2.1
  have ts := PSTROuterCountCode.test_at whole origin hc
  rw [PSTRCountControl.fetched_test rom whole (origin + 5) (origin + 478) ts.bound ts.code hwords hpcfit
    state ready.pc ready.active]
  have heap_eq := (PSTRCountControl.test_payload rom (origin + 478) state).1
  constructor
  · rw [executeOps_halted, ready.active]
  · exact PSTRCountControl.test_pc_at_end rom (origin + 5) (origin + 478)
      (prepareNormalization q full).indexed.nodes.size state ready.pc ht ready.index hsize
  · rw [heap_eq]
    exact ready.rep
  · exact (PSTRCountControl.test_payload rom (origin + 478) state).2.1.trans ready.index
  · intro offset hoffset
    rw [heap_eq]
    simpa only [PSTRCountChildRows.offset_end] using ready.slots offset hoffset
  · intro child
    rw [heap_eq]
    exact ready.counts child child.isLt
  · rw [heap_eq]
    exact ready.sentinel
  · intro child
    rw [heap_eq]
    exact ready.parents child child.isLt

theorem actual_complete {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp)
    (cb : PSTRBootstrapSlices.Contains whole) (co : PSTROuterCountCode.Contains whole 61)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration heap) :
    ∃ steps ≤ 8 * CapacityBits.width q + 66 + 501 * (prepareNormalization q full).indexed.nodes.size,
      Complete full configuration 61 (capacityWords 8192 full.length q (treeSize q full))
        (packingRun (callInput q full command) whole steps (packingInitial heap)) := by
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := callInput q full command
  let boot := packingRun rom whole (8 * CapacityBits.width q + 61) (packingInitial heap)
  have start := ready_zero_in full command configuration whole cb co hwords hpcfit hq hl heap rep
  obtain ⟨loopSteps, hloopSteps, last⟩ := PSTRCountIteration.actual_iterations full command configuration 61 whole co
    hwords hpcfit hq hl size 0 boot (by omega) start
  have bound : loopSteps ≤ 387 * size + 114 * PSTRStaticLayout.edgeCount q full := by
    simpa only [size, PSTRCountChildRows.offset_zero, PSTRCountChildRows.offset_end,
      Nat.mul_zero, Nat.add_zero, Nat.zero_add] using hloopSteps
  have he := PSTRStaticLayout.edgeCount_eq q full hq hl
  have he_le : PSTRStaticLayout.edgeCount q full ≤ size := by rw [he]; exact Nat.sub_le _ _
  have ending := finish_from_ready full command configuration 61 whole co hwords hpcfit hq
    (packingRun rom whole loopSteps boot) (by simpa only [Nat.zero_add] using last)
  refine ⟨(8 * CapacityBits.width q + 61) + (loopSteps + 5), by omega, ?_⟩
  rw [PSTRWordSegments.run_add, PSTRWordSegments.run_add]
  exact ending

theorem logical_views {q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (origin : Nat) (hq : 0 < q) (result : WordState (indexWidth 32 full.length q))
    (complete : Complete full configuration origin (capacityWords 8192 full.length q (treeSize q full)) result) :
    let capWords := capacityWords 8192 full.length q (treeSize q full)
    (∀ child : (prepareNormalization q full).indexed.NodeId,
      logicalHeap q capWords result.heap (countsBase (logicalWorkspace full capWords) + child.val) =
        (IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used).get child) ∧
    PA17HeapAncestors001.ParentHeapFor (prepareNormalization q full).indexed
      (parentsBase (logicalWorkspace full capWords) (prepareNormalization q full).indexed.nodes.size)
      (logicalHeap q capWords result.heap) := by
  have dimensions := PSTROriginalCountRoom.dimension_rooms full
  exact ⟨PSTRCountLogical.counts_view full _ configuration.used result.heap hq dimensions.2.2.2.2 complete.counts,
    PSTRCountLogical.parents_view full _ result.heap hq ((Nat.le_succ _).trans_lt dimensions.2.2.1)
      complete.sentinel complete.parents⟩

end PaperProofs.Structure.LaminarTree.PSTRCountComplete
