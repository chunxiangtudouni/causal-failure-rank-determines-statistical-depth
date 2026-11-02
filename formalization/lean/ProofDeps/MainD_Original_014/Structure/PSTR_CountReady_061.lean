module

public import Structure.PSTR_CountProgram_059

/-! The original raw call actually reaches the outer-loop invariant at
node0. Prefix counts/parents are empty proof obligations at0; their words
are not initialized by an assumption. The sentinel and all four control
slots are genuinely written by preceding instructions in this SAME run. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountReady

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace

structure Ready {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (origin capWords node : Nat) (state : WordState bits) : Prop where
  rep : HeapRepresents q full capWords configuration state.heap
  active : state.halted = false
  pc : state.pc = BitVec.ofNat bits (5 * (origin + 5))
  node_le : node ≤ (prepareNormalization q full).indexed.nodes.size
  index : state.register .index = BitVec.ofNat bits node
  slots : ∀ offset < 4, state.heap (BitVec.ofNat bits (base q full capWords bits + 12 + offset)) =
    if offset = 0 then BitVec.ofNat bits (CapacityBits.width q)
    else if offset = 1 then lowMask bits (CapacityBits.width q)
    else if offset = 2 then BitVec.ofNat bits node
    else BitVec.ofNat bits (PSTRCountChildRows.flatOffset full node)
  counts : ∀ child : (prepareNormalization q full).indexed.NodeId, child.val < node →
    state.heap (BitVec.ofNat bits (countsBase (base q full capWords bits) + child.val)) =
      BitVec.ofNat bits ((IndexedDescent.usedCounts (prepareNormalization q full).indexed configuration.used).get child)
  sentinel : state.heap (BitVec.ofNat bits (parentsBase (base q full capWords bits)
    (prepareNormalization q full).indexed.nodes.size)) = BitVec.ofNat bits 0
  parents : ∀ child : (prepareNormalization q full).indexed.NodeId, child.val < node →
    state.heap (BitVec.ofNat bits (parentsBase (base q full capWords bits)
      (prepareNormalization q full).indexed.nodes.size + child.val + 1)) =
        BitVec.ofNat bits (encodedNode (prepareNormalization q full).indexed
          ((prepareNormalization q full).indexed.parents.get child))

theorem actual_ready_zero {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration heap) :
    Ready full configuration 61 (capacityWords 8192 full.length q (treeSize q full)) 0
      (packingRun (callInput q full command) PSTRCountProgram.program
        (8 * CapacityBits.width q + 61) (packingInitial heap)) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := callInput q full command
  let boot := packingRun rom PSTRCountProgram.program (8 * CapacityBits.width q + 56) (packingInitial heap)
  let finished := executeOps rom PSTRParentSentinel.program boot
  have h := PSTRCountProgram.original_active_bootstrap full command configuration hq hl heap rep
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have bp : HeapRepresents q full capWords configuration boot.heap := h.2.2.2.2.2.2.2
  have hbase : boot.register .old = BitVec.ofNat bits (countsBase workspace) := h.2.2.1
  have ht : boot.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using (PSTRStaticHeap.headers full configuration capWords boot.heap bp).1
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have hroom : Fits bits (parentsBase workspace size) := (Nat.le_add_right _ size).trans_lt rooms.2
  have hs := PSTROuterCountCode.sentinel_at PSTRCountProgram.program 61 PSTRCountProgram.outer_contains
  have run : packingRun rom PSTRCountProgram.program (8 * CapacityBits.width q + 61) (packingInitial heap) = finished := by
    rw [show 8 * CapacityBits.width q + 61 = (8 * CapacityBits.width q + 56) + 5 by omega,
      PSTRWordSegments.run_add,
      PSTRParentSentinel.containing_run rom PSTRCountProgram.program 61 hs.bound hs.code
        (PSTRCountProgram.code_fit (by omega)) (PSTRCountProgram.pc_fit (by omega)) boot h.2.1 h.1]
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

end PaperProofs.Structure.LaminarTree.PSTRCountReady
