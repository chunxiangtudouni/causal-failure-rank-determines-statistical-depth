module

public import Structure.PSTR_UniformPositiveBootstrap_107
public import Structure.PSTR_CountComplete_066

/-! Real new-bootstrap63 plus true sentinel yields original Ready at0,
from arbitrary seven entry registers, in the SAME containing program. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRUniformCountReady

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace PSTRCountReady

theorem actual_ready_zero {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp) (zeroTarget : Nat)
    (cb : PSTRUniformBootstrapCode.Contains whole zeroTarget) (co : PSTROuterCountCode.Contains whole 63)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap) :
    Ready full configuration 63 (capacityWords 8192 full.length q (treeSize q full)) 0
      (packingRun (callInput q full command) whole
        (8 * CapacityBits.width q + 63) state) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := callInput q full command
  let boot := packingRun rom whole (8 * CapacityBits.width q + 58) state
  let finished := executeOps rom PSTRParentSentinel.program boot
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have h := PSTRUniformPositiveBootstrap.actual_bootstrap full command configuration whole zeroTarget cb hwords hpcfit
    state hp ha hq hl rep
  have original_rep := PSTRUniformPositiveBootstrap.heap_represents full command configuration whole zeroTarget cb hwords hpcfit
    state hp ha hq hl rep
  have bp : HeapRepresents q full capWords configuration boot.heap := original_rep
  have hbase : boot.register .old = BitVec.ofNat bits (countsBase workspace) := h.2.2.1
  have ht : boot.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using (PSTRStaticHeap.headers full configuration capWords boot.heap bp).1
  have hroom : Fits bits (parentsBase workspace size) := (Nat.le_add_right _ size).trans_lt rooms.2
  have hs := PSTROuterCountCode.sentinel_at whole 63 co
  have run : packingRun rom whole (8 * CapacityBits.width q + 63) state = finished := by
    rw [show 8 * CapacityBits.width q + 63 = (8 * CapacityBits.width q + 58) + 5 by omega,
      PSTRWordSegments.run_add,
      PSTRParentSentinel.containing_run rom whole 63 hs.bound hs.code
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

end PaperProofs.Structure.LaminarTree.PSTRUniformCountReady
