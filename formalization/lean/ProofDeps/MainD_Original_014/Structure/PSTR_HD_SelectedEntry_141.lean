module

public import Structure.PSTR_HD_SelectedProgram_140

/-! Actual OLD reply spill plus genuine42-op repair entry. The saved tool
is obtained from ORIGINAL ReplyCorrect/some, and W12 is an internal physical
query postcondition. No address, width, cursor or reply is a ROM oracle. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRSelectedError
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open PSTRReplySpill

structure Rooms {q : Nat} (full : List (Finset (Fin q))) (capWords bits : Nat) : Prop where
  bits_eight : 8 ≤ bits
  width : CapacityBits.width q ≤ bits
  scalar : Fits bits (4 + capWords * CapacityBits.width q)
  workspace : Fits bits (PSTRCountWorkspace.base q full capWords bits + 12)
  N1 : Fits bits (full.length + 1)
  q2 : Fits bits (q + 2)
  tree1 : Fits bits (treeSize q full + 1)
  product : Fits bits ((full.length + 1) * (q + 2))
  bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords

def savedState {bits : Nat} (rom : PhysicalROM) (state : WordState bits) : WordState bits :=
  executeOps rom spillProgram (executeOps rom prepareProgram state)

def entryState {bits : Nat} (rom : PhysicalROM) (state : WordState bits) : WordState bits :=
  executeOps rom PSTRRepairEntry.program (savedState rom state)

theorem workspace_exact {q : Nat} (full : List (Finset (Fin q))) (capWords bits : Nat) (hq : 0 < q) :
    PSTRCountWorkspace.base q full capWords bits = 4 + packedCapacityWords q capWords bits + 2 + (staticMetadata q full).length := by
  rw [PSTRCountWorkspace.base_metadata_end q full hq capWords bits]
  rfl

theorem Rooms.metadata {q : Nat} (full : List (Finset (Fin q))) (capWords bits : Nat)
    (room : Rooms full capWords bits) (hq : 0 < q) (offset : Nat) (ho : offset < 2 + (staticMetadata q full).length) :
    Fits bits (4 + packedCapacityWords q capWords bits + offset) := by
  have hw := room.workspace
  rw [workspace_exact full capWords bits hq] at hw
  exact (show 4 + packedCapacityWords q capWords bits + offset ≤
    4 + packedCapacityWords q capWords bits + 2 + (staticMetadata q full).length + 12 by omega).trans_lt hw

theorem Rooms.spill_base {q : Nat} (full : List (Finset (Fin q))) (capWords bits : Nat) (hq : 0 < q) :
    4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤
      PSTRCountWorkspace.base q full capWords bits + 8 := by
  rw [workspace_exact full capWords bits hq]
  omega

structure EntryData {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q) : Prop where
  represented : HeapRepresents q full capWords configuration (entryState (callInput q full .error) state).heap
  address : ((entryState (callInput q full .error) state).register .address).toNat =
    tableWords full.length q (treeSize q full) + tool.val
  width : (entryState (callInput q full .error) state).register .total = BitVec.ofNat bits (CapacityBits.width q)
  cursor : (entryState (callInput q full .error) state).register .flag =
    BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 8 + 3)
  slots : ∀ offset < 4, (entryState (callInput q full .error) state).heap
    (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 8 + offset)) = savedWord state offset
  heap : (entryState (callInput q full .error) state).heap =
    spillHeap (PSTRCountWorkspace.base q full capWords bits + 8) (executeOps (callInput q full .error) prepareProgram state)

theorem execute_entry_data {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q) (hq : 0 < q)
    (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = some tool)
    (room : Rooms full capWords bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (reply : ReplyCorrect q (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used)
      (replyState q capWords state))
    (savedWidth : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q)) : EntryData full configuration capWords state tool := by
  let rom := callInput q full .error
  let workspace := PSTRCountWorkspace.base q full capWords bits
  let prepared := executeOps rom prepareProgram state
  let spilled := savedState rom state
  have prep := prepare_values full .error configuration capWords state room.bits_eight hq rep
  have hslotRoom : Fits bits (workspace + 8 + 3) := (show workspace + 8 + 3 ≤ workspace + 12 by omega).trans_lt room.workspace
  have spHeap : spilled.heap = spillHeap (workspace + 8) prepared := spill_execute_heap rom prepared _ prep.1
  have spRep : HeapRepresents q full capWords configuration spilled.heap := by
    rw [spHeap]
    have prepRep : HeapRepresents q full capWords configuration prepared.heap := by rw [prep.2.2]; exact rep
    exact PSTRRepairHeap.spill_represents full configuration capWords (workspace + 8) prepared
      (by have h := room.bits_eight; omega) hq prepRep room.bitmap room.scalar hslotRoom
      (Rooms.spill_base full capWords bits hq)
  have spSlots (offset : Nat) (ho : offset < 4) :
      spilled.heap (BitVec.ofNat bits (workspace + 8 + offset)) = savedWord state offset := by
    rw [spHeap, spill_slot _ prepared hslotRoom offset ho]
    exact savedWord_of_reply state prepared prep.2.1 offset
  have index := (PSTRHeadsRuntime.original_reply_word_fields capWords _ state reply).2.2.2
  simp only [choose] at index
  have spTool : spilled.heap (BitVec.ofNat bits (workspace + 11)) = BitVec.ofNat bits (tool.val + 1) := by
    have hs := spSlots 3 (by decide)
    simpa only [show workspace + 8 + 3 = workspace + 11 by omega, savedWord] using hs.trans index
  have spWidth : spilled.heap (BitVec.ofNat bits (workspace + 12)) = BitVec.ofNat bits (CapacityBits.width q) := by
    rw [show spilled = executeOps rom spillProgram prepared from rfl,
      spill_width_slot rom prepared workspace prep.1 room.workspace, prep.2.2]
    exact savedWidth
  have entered := PSTRRepairEntry.execute_entry full .error configuration capWords spilled tool
    room.bits_eight hq spRep room.workspace spTool spWidth room.N1 room.q2 room.tree1 room.product
  have hwp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
    intro he
    exact (ne_of_gt hq) ((CapacityBits.width_eq_zero_iff q).mp he))
  have hlogical : tableWords full.length q (treeSize q full) + tool.val < capWords := by
    have ht := tool.isLt
    have hb := room.bitmap
    omega
  have hfit : Fits bits (tableWords full.length q (treeSize q full) + tool.val) :=
    (hlogical.trans_le (Nat.le_mul_of_pos_right capWords hwp)).trans
      ((Nat.le_add_left (capWords * CapacityBits.width q) 4).trans_lt room.scalar)
  refine ⟨?_, ?_, entered.2.1, ?_, ?_, entered.2.2.2.trans spHeap⟩
  · change HeapRepresents q full capWords configuration (executeOps rom PSTRRepairEntry.program spilled).heap
    rw [entered.2.2.2]
    exact spRep
  · change ((executeOps rom PSTRRepairEntry.program spilled).register .address).toNat = _
    rw [entered.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hfit]
  · change (executeOps rom PSTRRepairEntry.program spilled).register .flag = BitVec.ofNat bits (workspace + 8 + 3)
    rw [show workspace + 8 + 3 = workspace + 11 by omega]
    exact entered.2.2.1
  · intro offset ho
    change (executeOps rom PSTRRepairEntry.program spilled).heap _ = _
    rw [entered.2.2.2]
    exact spSlots offset ho

end PaperProofs.Structure.LaminarTree.PSTRSelectedError
