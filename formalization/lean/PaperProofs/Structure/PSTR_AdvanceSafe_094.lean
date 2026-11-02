module

public import PaperProofs.Structure.PSTR_OuterStoreAccess_092
public import PaperProofs.Structure.PSTR_AdvanceOutside_081

/-! Actual parent50/advance32/back3 fetched access safety at every proper
clock, with all pointers derived from ORIGINAL Counted and heap headers.
The same real segment boundaries as the frozen frame proof are used. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRAdvanceSafe

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRCountKernel PSTRQueryLayout PSTRCountWorkspace

theorem actual_safe {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (origin : Nat)
    (node : (prepareNormalization q full).indexed.NodeId)
    (initial current : WordState (indexWidth 32 full.length q)) (whole : List PackingOp)
    (hc : PSTROuterCountCode.Contains whole origin)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (counted : PSTRNodeCounted.Counted full configuration origin
      (capacityWords 8192 full.length q (treeSize q full)) node initial current)
    (clock : Nat) (hclock : clock < 85) :
    AtSafe (callInput q full command) whole
      (endpoint (base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
        (prepareNormalization q full).indexed.nodes.size q)
      (packingRun (callInput q full command) whole clock current) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let size := (prepareNormalization q full).indexed.nodes.size
  let heapWords := endpoint workspace size q
  let rom := callInput q full command
  let parented := executeOps rom PSTRParentCopy.program current
  let advanced := executeOps rom PSTRCountAdvance.program parented
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have hroom : workspace + 15 < heapWords := by
    change workspace + 15 < endpoint workspace size q
    rw [endpoint_eq]
    omega
  have hparents : parentsBase workspace size + size < heapWords := by
    change workspace + 16 + size + size < endpoint workspace size q
    rw [endpoint_eq]
    omega
  have parent_rep : HeapRepresents q full capWords configuration parented.heap := by
    have hr := PSTROuterMemory.parent_prefix_rep full command configuration capWords current node (by omega) hq counted.rep
      (PSTROriginalCountRoom.bitmap_room full 8192 hq)
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) raw.1 counted.index rooms.2 50 le_rfl
    simpa only [List.take_of_length_le (show PSTRParentCopy.program.length ≤ 50 by rw [PSTRParentCopy.program_length])] using hr
  have parent_pc : parented.pc = BitVec.ofNat bits (5 * (origin + 443)) := by
    rw [executeOps_pc rom _ current PSTRParentCopy.program_straight, counted.pc,
      PSTRParentCopy.program_length, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (by omega)
  have parent_active : parented.halted = false := by rw [executeOps_halted, counted.active]
  have advance_pc : advanced.pc = BitVec.ofNat bits (5 * (origin + 475)) := by
    rw [executeOps_pc rom _ parented PSTRCountAdvance.program_straight, parent_pc,
      PSTRCountAdvance.program_length, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (by omega)
  have advance_active : advanced.halted = false := by rw [executeOps_halted, parent_active]
  have ps := PSTROuterCountCode.parent_at whole origin hc
  have ads := PSTROuterCountCode.advance_at whole origin hc
  have bs := PSTROuterCountCode.back_at whole origin hc
  have parent_run := PSTRParentCopy.containing_run rom whole (origin + 393) ps.bound ps.code hwords hpcfit
    current counted.pc counted.active
  have advance_run := PSTRCountAdvance.containing_run rom whole (origin + 443) ads.bound ads.code hwords hpcfit
    parented parent_pc parent_active
  by_cases hparent : clock < 50
  · exact PSTROuterStoreAccess.parent_safe full command configuration capWords heapWords current node whole (origin + 393)
      ps hwords hpcfit (by omega) hq counted.rep raw.1 counted.index
      (by change workspace < heapWords; omega) hparents counted.pc counted.active clock hparent
  · by_cases hadvance : clock < 82
    · rw [show clock = 50 + (clock - 50) by omega, PSTRWordSegments.run_add, parent_run]
      exact PSTROuterStoreAccess.advance_safe full command configuration capWords heapWords parented whole (origin + 443)
        ads hwords hpcfit (by omega) hq parent_rep rooms.1 hroom parent_pc parent_active (clock - 50) (by omega)
    · rw [show clock = 50 + (32 + (clock - 82)) by omega, PSTRWordSegments.run_add, parent_run,
        PSTRWordSegments.run_add, advance_run]
      exact PSTRBranchAccess.back_safe rom whole (origin + 475) (origin + 5) heapWords bs hwords hpcfit
        advanced advance_pc advance_active (clock - 82) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRAdvanceSafe
