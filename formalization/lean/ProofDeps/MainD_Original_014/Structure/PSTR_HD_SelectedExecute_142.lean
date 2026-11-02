module

public import Structure.PSTR_HD_SelectedEntry_141

/-! Actual102-op selected-error semantics. Repair21 is the existing real
marker and stage store, and restore10 consumes the cursor actually produced
by entry42. OLD reply values are recovered from actual heap slots. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRSelectedError
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open PSTRReplySpill

def repairState {bits : Nat} (rom : PhysicalROM) (state : WordState bits) : WordState bits :=
  executeOps rom PSTRRuntimeRepair.program (entryState rom state)

theorem execute_program_eq {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    executeOps rom program state = executeOps rom restoreProgram (repairState rom state) := by
  simp only [program, repairState, entryState, savedState, executeOps_append]

theorem next_configuration_some {q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (tool : Fin q) (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = some tool) :
    nextConfiguration q full configuration .error =
      {configuration with stage := configuration.stage + 1, used := insert tool configuration.used} := by
  have hs : configuration.stage < full.length + 1 := by have h := allowed.2; omega
  simp only [nextConfiguration, hs, dite_true, choose]
  have hf := allowed.1
  cases configuration
  simp_all only

theorem repair_heap {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q) (hq : 0 < q)
    (room : Rooms full capWords bits) (data : EntryData full configuration capWords state tool) :
    (repairState (callInput q full .error) state).heap =
      PSTRRuntimeAdvance.bumpHeap (packedCapacityWords q capWords bits)
        (PSTRRuntimeMarkUsed.markHeap
          ((tableWords full.length q (treeSize q full) + tool.val) * CapacityBits.width q)
          (entryState (callInput q full .error) state).heap) := by
  let entered := entryState (callInput q full .error) state
  have hwp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have haddr : (entered.register .address).toNat < capWords := by
    rw [data.address]
    have ht := tool.isLt
    have hb := room.bitmap
    omega
  have hstartlt : (entered.register .address).toNat * CapacityBits.width q < capWords * CapacityBits.width q :=
    Nat.mul_lt_mul_of_pos_right haddr hwp
  have hstart : Fits bits ((entered.register .address).toNat * CapacityBits.width q) :=
    hstartlt.trans ((Nat.le_add_left (capWords * CapacityBits.width q) 4).trans_lt room.scalar)
  have hptr := PSTRMarkUsedBits.physical_fit_of_offset _ _ hstartlt room.scalar
  have hheader : (PSTRRuntimeMarkUsed.markHeap
      ((entered.register .address).toNat * CapacityBits.width q) entered.heap (BitVec.ofNat bits 2)).toNat =
        packedCapacityWords q capWords bits := by
    rw [PSTRRuntimeMarkUsed.markHeap_header _ entered.heap room.bits_eight hptr 2 (by decide)]
    exact data.represented.2.2.1
  have h := PSTRRepairCapacity.execute_prefix_heap (callInput q full .error) entered
    (by have hb := room.bits_eight; omega) room.width data.width data.represented.2.2.2.1 hstart
    (packedCapacityWords q capWords bits) hheader 21 le_rfl
  have ht : PSTRRuntimeRepair.program.take 21 = PSTRRuntimeRepair.program :=
    List.take_of_length_le (by rw [PSTRRuntimeRepair.program_length])
  simpa only [ht, entered, repairState, show ¬21 < 13 by decide, show ¬21 < 21 by decide,
    ite_false, data.address] using h

theorem repair_slots {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q) (hq : 0 < q)
    (room : Rooms full capWords bits) (data : EntryData full configuration capWords state tool)
    (offset : Nat) (ho : offset < 4) :
    (repairState (callInput q full .error) state).heap
      (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 8 + offset)) = savedWord state offset := by
  let workspace := PSTRCountWorkspace.base q full capWords bits
  let start := (tableWords full.length q (treeSize q full) + tool.val) * CapacityBits.width q
  have hwp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have haddr : tableWords full.length q (treeSize q full) + tool.val < capWords := by
    have ht := tool.isLt
    have hb := room.bitmap
    omega
  have hword : start / bits < packedCapacityWords q capWords bits :=
    (Nat.div_lt_iff_lt_mul (by have hb := room.bits_eight; omega)).mpr
      ((Nat.mul_lt_mul_of_pos_right haddr hwp).trans_le
        (packedCapacityWords_mul_bits q capWords (by have hb := room.bits_eight; omega)))
  have hws := workspace_exact full capWords bits hq
  have hslot : Fits bits (workspace + 8 + offset) :=
    (show workspace + 8 + offset ≤ workspace + 12 by omega).trans_lt room.workspace
  have hmark : Fits bits (4 + start / bits) :=
    (show 4 + start / bits ≤ workspace + 12 by omega).trans_lt room.workspace
  have hstage := Rooms.metadata full capWords bits room hq 0 (by omega)
  simp only [Nat.add_zero] at hstage
  have hnmark : BitVec.ofNat bits (workspace + 8 + offset) ≠ BitVec.ofNat bits (4 + start / bits) :=
    (ofNat_injective_of_fit _ _ hslot hmark).not.mpr (by omega)
  have hnstage : BitVec.ofNat bits (workspace + 8 + offset) ≠ BitVec.ofNat bits (4 + packedCapacityWords q capWords bits) :=
    (ofNat_injective_of_fit _ _ hslot hstage).not.mpr (by omega)
  rw [repair_heap full configuration capWords state tool hq room data,
    PSTRRuntimeAdvance.heap_frame _ _ _ hnstage, PSTRRuntimeMarkUsed.markHeap_frame _ _ _ hnmark]
  exact data.slots offset ho

theorem execute_selected {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q) (hq : 0 < q)
    (laminar : LaminarSchedule full) (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = some tool)
    (room : Rooms full capWords bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (reply : ReplyCorrect q (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used)
      (replyState q capWords state))
    (savedWidth : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q)) :
    let after := executeOps (callInput q full .error) program state
    HeapRepresents q full capWords (nextConfiguration q full configuration .error) after.heap ∧
      ReplyRegisters state after ∧
      ReplyCorrect q (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used)
        (replyState q capWords after) := by
  let rom := callInput q full .error
  let workspace := PSTRCountWorkspace.base q full capWords bits
  have data := execute_entry_data full configuration capWords state tool hq allowed choose room rep reply savedWidth
  have unused : tool ∉ configuration.used :=
    ((PSTRCallback.callback_stage q full laminar ⟨configuration.stage, allowed.2⟩ configuration.used).2.2.2 tool choose).2.1
  have hnext : Fits bits (configuration.stage + 1) :=
    (show configuration.stage + 1 ≤ full.length + 1 by have hs := allowed.2; omega).trans_lt room.N1
  have repaired : HeapRepresents q full capWords
      {configuration with stage := configuration.stage + 1, used := insert tool configuration.used}
      (repairState rom state).heap :=
    PSTRRuntimeRepair.execute_represents rom full configuration capWords (entryState rom state) tool
      room.bits_eight hq room.width data.represented unused room.bitmap room.scalar
      (Rooms.metadata full capWords bits room hq) hnext data.address data.width
  have cursor : (repairState rom state).register .flag = BitVec.ofNat bits (workspace + 8 + 3) := by
    rw [repairState, repair_cursor]
    exact data.cursor
  have restored := restore_reply rom state (repairState rom state) (workspace + 8) room.bits_eight
    ((show workspace + 8 + 3 ≤ workspace + 12 by omega).trans_lt room.workspace) cursor
    (repair_slots full configuration capWords state tool hq room data)
  dsimp only
  rw [execute_program_eq]
  refine ⟨?_, restored, PSTRRepairHeap.replyCorrect_of_registers capWords state _ restored _ reply⟩
  rw [restore_heap, next_configuration_some full configuration tool allowed choose]
  exact repaired

end PaperProofs.Structure.LaminarTree.PSTRSelectedError
