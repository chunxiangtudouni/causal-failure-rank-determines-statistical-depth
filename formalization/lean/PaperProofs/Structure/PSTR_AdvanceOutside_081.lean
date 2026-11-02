module

public import PaperProofs.Structure.PSTR_CountAdvanceStep_064
public import PaperProofs.Structure.PSTR_OuterStoreFrame_069
public import PaperProofs.Structure.PSTR_WidthPrefix_035

/-! Every actual clock of parent50 + advance32 + back3 preserves the
original persistent heap representation and every fitting physical word
at/above the exclusive heads endpoint E. No access certificate is inferred. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRAdvanceOutside

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace

theorem back_prefix_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start target : Nat)
    (hbound : start + (PSTRCountControl.backBlock target).length ≤ whole.length)
    (hcode : ∀ i (hi : i < (PSTRCountControl.backBlock target).length),
      whole[start + i]'(by omega) = (PSTRCountControl.backBlock target)[i])
    (hw : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (state : WordState bits) (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 3) :
    packingRun rom whole count state = executeOps rom ((PSTRCountControl.backBlock target).take count) state := by
  apply PSTRWordSegments.segment_prefix rom whole (PSTRCountControl.backLead target)
    (.jumpIfZero .flag .address) start
    (by rw [PSTRCountControl.backBlock_length, PSTRCountControl.backLead_length] at *; omega)
    ?_ ?_ (PSTRCountControl.backLead_straight target) hw hpcfit state hp ha count hc
  · intro i hi
    exact (hcode i (by rw [PSTRCountControl.backBlock_length]; rw [PSTRCountControl.backLead_length] at hi; omega)).trans
      (List.getElem_append_left hi)
  · exact (hcode (PSTRCountControl.backLead target).length
      (by rw [PSTRCountControl.backBlock_length, PSTRCountControl.backLead_length]; decide)).trans
      (List.getElem_append_right' (PSTRCountControl.backLead target)
        (l₂ := [.jumpIfZero .flag .address]) (i := 0) (by decide))

theorem actual_prefix {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (origin : Nat)
    (node : (prepareNormalization q full).indexed.NodeId)
    (initial current : WordState (indexWidth 32 full.length q)) (whole : List PackingOp)
    (hc : PSTROuterCountCode.Contains whole origin)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (counted : PSTRNodeCounted.Counted full configuration origin
      (capacityWords 8192 full.length q (treeSize q full)) node initial current)
    (clock : Nat) (hclock : clock ≤ 85) :
    let result := packingRun (callInput q full command) whole clock current
    HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
      ∀ physical, Fits (indexWidth 32 full.length q) physical →
        (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
        result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) =
          current.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let rom := callInput q full command
  let parented := executeOps rom PSTRParentCopy.program current
  let advanced := executeOps rom PSTRCountAdvance.program parented
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have parent_rep : HeapRepresents q full capWords configuration parented.heap := by
    have hr := PSTROuterMemory.parent_prefix_rep full command configuration capWords current node (by omega) hq counted.rep
      (PSTROriginalCountRoom.bitmap_room full 8192 hq)
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) raw.1 counted.index rooms.2 50 le_rfl
    simpa only [List.take_of_length_le (show PSTRParentCopy.program.length ≤ 50 by rw [PSTRParentCopy.program_length])] using hr
  have parent_high (physical : Nat) (hp : Fits bits physical)
      (hh : physical < workspace ∨ endpoint workspace (prepareNormalization q full).indexed.nodes.size q ≤ physical)
      (count : Nat) (hn : count ≤ 50) :
      (executeOps rom (PSTRParentCopy.program.take count) current).heap (BitVec.ofNat bits physical) =
        current.heap (BitVec.ofNat bits physical) := by
    rcases hh with low | high
    · apply PSTRParentCopy.prefix_frame full command configuration capWords current node (by omega) hq
        counted.rep raw.1 counted.index rooms.2 physical ?_ count hn
      change physical < workspace + 16 + (prepareNormalization q full).indexed.nodes.size + node.val + 1
      omega
    · apply PSTROuterStoreFrame.parent_prefix_high full command configuration capWords current node (by omega) hq
        counted.rep raw.1 counted.index rooms.2 physical hp ?_ count hn
      rw [endpoint_eq] at high
      change workspace + 16 + (prepareNormalization q full).indexed.nodes.size +
        (prepareNormalization q full).indexed.nodes.size < physical
      omega
  have advance_high (physical : Nat) (hp : Fits bits physical)
      (hh : physical < workspace ∨ endpoint workspace (prepareNormalization q full).indexed.nodes.size q ≤ physical)
      (count : Nat) (hn : count ≤ 32) :
      (executeOps rom (PSTRCountAdvance.program.take count) parented).heap (BitVec.ofNat bits physical) =
        parented.heap (BitVec.ofNat bits physical) := by
    apply PSTROuterMemory.advance_prefix_frame full command configuration capWords parented (by omega) hq
      parent_rep rooms.1 physical hp ?_ count hn
    rcases hh with low | high
    · exact Or.inl (by change physical < workspace + 14; omega)
    · right
      rw [endpoint_eq] at high
      change workspace + 16 ≤ physical
      omega
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
  dsimp only
  by_cases hparent : clock ≤ 50
  · rw [PSTRWidthPrefix.straight_prefix rom whole PSTRParentCopy.program (origin + 393)
      ps.bound ps.code PSTRParentCopy.program_straight hwords hpcfit current counted.pc counted.active clock hparent]
    exact ⟨PSTROuterMemory.parent_prefix_rep full command configuration capWords current node (by omega) hq counted.rep
      (PSTROriginalCountRoom.bitmap_room full 8192 hq)
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) raw.1 counted.index rooms.2 clock hparent,
      fun physical hp hh => parent_high physical hp hh clock hparent⟩
  · by_cases hadvance : clock ≤ 82
    · rw [show clock = 50 + (clock - 50) by omega, PSTRWordSegments.run_add, parent_run,
        PSTRWidthPrefix.straight_prefix rom whole PSTRCountAdvance.program (origin + 443)
          ads.bound ads.code PSTRCountAdvance.program_straight hwords hpcfit parented parent_pc parent_active
          (clock - 50) (by rw [PSTRCountAdvance.program_length]; omega)]
      refine ⟨PSTROuterMemory.advance_prefix_rep full command configuration capWords parented (by omega) hq parent_rep
        (PSTROriginalCountRoom.bitmap_room full 8192 hq)
        (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) rooms.1 (clock - 50) (by omega), ?_⟩
      intro physical hp hh
      have hpframe := parent_high physical hp hh 50 le_rfl
      rw [List.take_of_length_le (show PSTRParentCopy.program.length ≤ 50 by rw [PSTRParentCopy.program_length])] at hpframe
      exact (advance_high physical hp hh (clock - 50) (by omega)).trans hpframe
    · rw [show clock = 50 + (32 + (clock - 82)) by omega, PSTRWordSegments.run_add, parent_run,
        PSTRWordSegments.run_add, advance_run,
        back_prefix_run rom whole (origin + 475) (origin + 5) bs.bound bs.code hwords hpcfit
          advanced advance_pc advance_active (clock - 82) (by omega),
        PSTRCountControl.back_prefix_heap rom (origin + 5) advanced (clock - 82) (by omega)]
      constructor
      · have hr := PSTROuterMemory.advance_prefix_rep full command configuration capWords parented (by omega) hq parent_rep
          (PSTROriginalCountRoom.bitmap_room full 8192 hq)
          (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) rooms.1 32 le_rfl
        simpa only [List.take_of_length_le (show PSTRCountAdvance.program.length ≤ 32 by rw [PSTRCountAdvance.program_length])] using hr
      · intro physical hp hh
        have apframe := advance_high physical hp hh 32 le_rfl
        have ppframe := parent_high physical hp hh 50 le_rfl
        rw [List.take_of_length_le (show PSTRCountAdvance.program.length ≤ 32 by rw [PSTRCountAdvance.program_length])] at apframe
        rw [List.take_of_length_le (show PSTRParentCopy.program.length ≤ 50 by rw [PSTRParentCopy.program_length])] at ppframe
        exact apframe.trans ppframe

end PaperProofs.Structure.LaminarTree.PSTRAdvanceOutside
