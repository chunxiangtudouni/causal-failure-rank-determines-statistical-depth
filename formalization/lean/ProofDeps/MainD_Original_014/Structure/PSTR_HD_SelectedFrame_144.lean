module

public import Structure.PSTR_HD_SelectedCapacity_143

/-! Exact original table and high-heap frames at EVERY102-op prefix. The
only low writes are real packed-used and stage cells; reply spills occupy
W8..W11. ALL Fits words at or above W12 are physically protected. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRSelectedError
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PSTRReplySpill

theorem entry_geometry {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q) (hq : 0 < q)
    (room : Rooms full capWords bits) (data : EntryData full configuration capWords state tool) :
    let entered := entryState (callInput q full .error) state
    let start := (entered.register .address).toNat * CapacityBits.width q
    (entered.register .address).toNat < capWords ∧ Fits bits start ∧
      start / bits < packedCapacityWords q capWords bits ∧ Fits bits (4 + start / bits) := by
  dsimp only
  have hwp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have haddr : ((entryState (callInput q full .error) state).register .address).toNat < capWords := by
    rw [data.address]
    have ht := tool.isLt
    have hm := room.bitmap
    omega
  have hstart := Nat.mul_lt_mul_of_pos_right haddr hwp
  exact ⟨haddr, hstart.trans ((Nat.le_add_left _ 4).trans_lt room.scalar),
    (Nat.div_lt_iff_lt_mul (by have hb := room.bits_eight; omega)).mpr
      (hstart.trans_le (packedCapacityWords_mul_bits q capWords (by have hb := room.bits_eight; omega))),
    PSTRMarkUsedBits.physical_fit_of_offset _ _ hstart room.scalar⟩

theorem repair_prefix_heap {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q) (hq : 0 < q)
    (room : Rooms full capWords bits) (data : EntryData full configuration capWords state tool)
    (count : Nat) (hc : count ≤ 21) :
    let entered := entryState (callInput q full .error) state
    let marked := PSTRRuntimeMarkUsed.markHeap
      ((tableWords full.length q (treeSize q full) + tool.val) * CapacityBits.width q) entered.heap
    (executeOps (callInput q full .error) (PSTRRuntimeRepair.program.take count) entered).heap =
      if count < 13 then entered.heap else if count < 21 then marked
      else PSTRRuntimeAdvance.bumpHeap (packedCapacityWords q capWords bits) marked := by
  let entered := entryState (callInput q full .error) state
  have geometry := entry_geometry full configuration capWords state tool hq room data
  have hp : (PSTRRuntimeMarkUsed.markHeap
      ((entered.register .address).toNat * CapacityBits.width q) entered.heap (BitVec.ofNat bits 2)).toNat =
        packedCapacityWords q capWords bits := by
    rw [PSTRRuntimeMarkUsed.markHeap_header _ entered.heap room.bits_eight geometry.2.2.2 2 (by decide)]
    exact data.represented.2.2.1
  simpa only [entered, data.address] using PSTRRepairCapacity.execute_prefix_heap (callInput q full .error) entered
    (by have hb := room.bits_eight; omega) room.width data.width data.represented.2.2.2.1 geometry.2.1
    (packedCapacityWords q capWords bits) hp count hc

theorem spill_prefix_table {bits q : Nat} (full : List (Finset (Fin q))) (capWords : Nat)
    (state : WordState bits) (hq : 0 < q) (room : Rooms full capWords bits)
    (flag : state.register .flag = BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 8))
    (count : Nat) (hc : count ≤ 8) (address : Nat)
    (ha : address < tableWords full.length q (treeSize q full)) :
    logicalHeap q capWords (executeOps (callInput q full .error) (spillProgram.take count) state).heap address =
      logicalHeap q capWords state.heap address := by
  have hb := room.bitmap
  apply PSTRRepairHeap.logical_frame state.heap _ capWords (2 + (staticMetadata q full).length)
    (PSTRCountWorkspace.base q full capWords bits + 8) address (by have h := room.bits_eight; omega) hq room.scalar
    ((show PSTRCountWorkspace.base q full capWords bits + 8 + 3 ≤ PSTRCountWorkspace.base q full capWords bits + 12 by omega).trans_lt room.workspace)
    (Rooms.spill_base full capWords bits hq) _ (by omega)
  intro physical hp
  exact PSTRReplyCapacity.spill_prefix_frame (callInput q full .error) state _ flag
    ((show PSTRCountWorkspace.base q full capWords bits + 8 + 3 ≤ PSTRCountWorkspace.base q full capWords bits + 12 by omega).trans_lt room.workspace)
    physical hp count hc

theorem prefix_table_high {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q) (hq : 0 < q)
    (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = some tool)
    (room : Rooms full capWords bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (reply : ReplyCorrect q (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used)
      (replyState q capWords state))
    (savedWidth : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q)) :
    ∀ count ≤ 102,
      (∀ address < tableWords full.length q (treeSize q full),
        logicalHeap q capWords (executeOps (callInput q full .error) (program.take count) state).heap address =
          logicalHeap q capWords state.heap address) ∧
      (∀ physical, Fits bits physical → PSTRCountWorkspace.base q full capWords bits + 12 ≤ physical →
        (executeOps (callInput q full .error) (program.take count) state).heap (BitVec.ofNat bits physical) =
          state.heap (BitVec.ofNat bits physical)) := by
  let rom := callInput q full .error
  let workspace := PSTRCountWorkspace.base q full capWords bits
  let property := fun (heap : BitVec bits → BitVec bits) =>
    (∀ address < tableWords full.length q (treeSize q full), logicalHeap q capWords heap address = logicalHeap q capWords state.heap address) ∧
    (∀ physical, Fits bits physical → workspace + 12 ≤ physical → heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical))
  have prep := prepare_values full .error configuration capWords state room.bits_eight hq rep
  have data := execute_entry_data full configuration capWords state tool hq allowed choose room rep reply savedWidth
  have sp (count : Nat) (hc : count ≤ 8) :
      property (executeOps rom (spillProgram.take count) (executeOps rom prepareProgram state)).heap := by
    constructor
    · intro address ha
      rw [spill_prefix_table full capWords _ hq room prep.1 count hc address ha, prep.2.2]
    · intro physical hf hp
      rw [spill_prefix_frame_outside rom _ (workspace + 8) physical prep.1
        ((show workspace + 8 + 3 ≤ workspace + 12 by omega).trans_lt room.workspace) hf (Or.inr (by omega)) count hc,
        prep.2.2]
  have spFull : property (savedState rom state).heap := by
    simpa only [show 8 = spillProgram.length from rfl, List.take_length, savedState] using sp 8 le_rfl
  have ent : property (entryState rom state).heap := by rw [entry_heap]; exact spFull
  have geometry := entry_geometry full configuration capWords state tool hq room data
  have hws := workspace_exact full capWords bits hq
  have hstage := Rooms.metadata full capWords bits room hq 0 (by omega)
  simp only [Nat.add_zero] at hstage
  have hm (count : Nat) (hc : count ≤ 21) :
      property (executeOps rom (PSTRRuntimeRepair.program.take count) (entryState rom state)).heap := by
    rw [repair_prefix_heap full configuration capWords state tool hq room data count hc]
    have marked : property (PSTRRuntimeMarkUsed.markHeap
        ((tableWords full.length q (treeSize q full) + tool.val) * CapacityBits.width q) (entryState rom state).heap) := by
      constructor
      · intro address ha
        have hcap := room.bitmap
        have htool := tool.isLt
        rw [PSTRMarkUsedBits.mark_other_capacity _ capWords _ address
          (by have h := room.bits_eight; omega) hq (by omega) (by omega) (by omega) room.scalar]
        exact ent.1 address ha
      · intro physical hf hp
        rw [PSTRRuntimeMarkUsed.markHeap_frame]
        · exact ent.2 physical hf hp
        · have hg := geometry.2.2.1
          rw [data.address] at hg
          have hfmark : Fits bits (4 + (tableWords full.length q (treeSize q full) + tool.val) * CapacityBits.width q / bits) := by
            simpa only [data.address] using geometry.2.2.2
          exact (ofNat_injective_of_fit _ _ hf hfmark).not.mpr (by omega)
    split_ifs
    · exact ent
    · exact marked
    · constructor
      · intro address ha
        rw [PSTRAdvanceHeap.bump_capacity _ capWords address
          (by have h := room.bits_eight; omega) hq (by have hc := room.bitmap; omega) room.scalar hstage]
        exact marked.1 address ha
      · intro physical hf hp
        rw [PSTRRuntimeAdvance.heap_frame]
        · exact marked.2 physical hf hp
        · exact (ofNat_injective_of_fit _ _ hf hstage).not.mpr (by omega)
  apply prefix_property rom state property
  · intro count hc
    rw [prepare_prefix_heap rom state count hc]
    exact ⟨fun _ _ => rfl, fun _ _ _ => rfl⟩
  · exact sp
  · intro count hc
    rw [PSTRRepairEntry.all_prefix_heap]
    · exact spFull
    · exact hc
  · exact hm
  · intro count _hc
    rw [PSTRReplyCapacity.restore_prefix_heap]
    simpa only [show 21 = PSTRRuntimeRepair.program.length from rfl, List.take_length, repairState] using hm 21 le_rfl

end PaperProofs.Structure.LaminarTree.PSTRSelectedError
