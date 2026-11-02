module

public import Structure.PSTR_HD_SelectedExecute_142
public import Structure.PSTR_HD_CountPrefixCompose_040

/-! Every actual prefix of the102-op selected update preserves original
capacity. Composition is over the fixed instructions and their real states;
there is no prefix invariant assumption in the original-facing theorem. -/

@[expose] public section
set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace PaperProofs.Structure.LaminarTree.PSTRSelectedError
open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM PSTRReplySpill

theorem heap_property_append {bits : Nat} (rom : PhysicalROM) (left right : List PackingOp)
    (state : WordState bits) (property : (BitVec bits → BitVec bits) → Prop)
    (hl : ∀ count ≤ left.length, property (executeOps rom (left.take count) state).heap)
    (hr : ∀ count ≤ right.length, property (executeOps rom (right.take count) (executeOps rom left state)).heap) :
    ∀ count ≤ (left ++ right).length, property (executeOps rom ((left ++ right).take count) state).heap := by
  intro count hc
  by_cases hleft : count ≤ left.length
  · rw [List.take_append_of_le_length hleft]
    exact hl count hleft
  · rw [PSTRCountKernel.take_append_after rom left right state count (by omega)]
    exact hr _ (by rw [List.length_append] at hc; omega)

theorem prefix_property {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (property : (BitVec bits → BitVec bits) → Prop)
    (hp : ∀ count ≤ 21, property (executeOps rom (prepareProgram.take count) state).heap)
    (hs : ∀ count ≤ 8, property (executeOps rom (spillProgram.take count) (executeOps rom prepareProgram state)).heap)
    (he : ∀ count ≤ 42, property (executeOps rom (PSTRRepairEntry.program.take count) (savedState rom state)).heap)
    (hm : ∀ count ≤ 21, property (executeOps rom (PSTRRuntimeRepair.program.take count) (entryState rom state)).heap)
    (hr : ∀ count ≤ 10, property (executeOps rom (restoreProgram.take count) (repairState rom state)).heap) :
    ∀ count ≤ 102, property (executeOps rom (program.take count) state).heap := by
  have first := heap_property_append rom prepareProgram spillProgram state property
    (by simpa only [prepare_length] using hp) (by simpa only [spill_length] using hs)
  have second := heap_property_append rom (prepareProgram ++ spillProgram) PSTRRepairEntry.program state property first
    (by simpa only [PSTRRepairEntry.program_length, executeOps_append, savedState] using he)
  have third := heap_property_append rom ((prepareProgram ++ spillProgram) ++ PSTRRepairEntry.program)
    PSTRRuntimeRepair.program state property second
    (by simpa only [PSTRRuntimeRepair.program_length, executeOps_append, entryState, savedState] using hm)
  have fourth := heap_property_append rom (((prepareProgram ++ spillProgram) ++ PSTRRepairEntry.program) ++ PSTRRuntimeRepair.program)
    restoreProgram state property third
    (by simpa only [restore_length, executeOps_append, repairState, entryState, savedState] using hr)
  exact fourth

theorem entry_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (entryState rom state).heap = (savedState rom state).heap := by
  simpa only [show 42 = PSTRRepairEntry.program.length from rfl, List.take_length, entryState] using
    PSTRRepairEntry.all_prefix_heap rom (savedState rom state) 42 le_rfl

theorem prefix_capacity {bits q : Nat} (full : List (Finset (Fin q))) (configuration : Configuration q)
    (capWords : Nat) (state : WordState bits) (tool : Fin q) (hq : 0 < q)
    (laminar : LaminarSchedule full) (allowed : Allowed full configuration .error)
    (choose : (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used).tool = some tool)
    (room : Rooms full capWords bits) (rep : HeapRepresents q full capWords configuration state.heap)
    (reply : ReplyCorrect q (callback q full ⟨configuration.stage, by have hs := allowed.2; omega⟩ configuration.used)
      (replyState q capWords state))
    (savedWidth : state.heap (BitVec.ofNat bits (PSTRCountWorkspace.base q full capWords bits + 12)) =
      BitVec.ofNat bits (CapacityBits.width q)) :
    ∀ count ≤ 102, CapacityPrefixBounded q capWords
      (logicalHeap q capWords (executeOps (callInput q full .error) (program.take count) state).heap) := by
  let rom := callInput q full .error
  let workspace := PSTRCountWorkspace.base q full capWords bits
  let property := fun (heap : BitVec bits → BitVec bits) => CapacityPrefixBounded q capWords (logicalHeap q capWords heap)
  have prep := prepare_values full .error configuration capWords state room.bits_eight hq rep
  have prepRep : HeapRepresents q full capWords configuration (executeOps rom prepareProgram state).heap := by
    rw [prep.2.2]
    exact rep
  have data := execute_entry_data full configuration capWords state tool hq allowed choose room rep reply savedWidth
  have spRep : HeapRepresents q full capWords configuration (savedState rom state).heap := by
    rw [← entry_heap rom state]
    exact data.represented
  have unused : tool ∉ configuration.used :=
    ((PSTRCallback.callback_stage q full laminar ⟨configuration.stage, allowed.2⟩ configuration.used).2.2.2 tool choose).2.1
  have hrepair (count : Nat) (hc : count ≤ 21) :
      property (executeOps rom (PSTRRuntimeRepair.program.take count) (entryState rom state)).heap :=
    PSTRReplyCapacity.repair_execute_capacity rom full configuration capWords (entryState rom state) tool
      room.bits_eight hq room.width data.represented unused room.bitmap room.scalar
      (Rooms.metadata full capWords bits room hq 0 (by omega)) data.address data.width count hc
  apply prefix_property rom state property
  · intro count hc
    rw [prepare_prefix_heap rom state count hc]
    exact (rep.2.2.2.2.2.2.2.2 hq).2
  · intro count hc
    have sp := PSTRReplyCapacity.spill_prefix_represents rom full configuration capWords (workspace + 8)
      (executeOps rom prepareProgram state) (by have h := room.bits_eight; omega) hq prepRep room.bitmap room.scalar
      ((show workspace + 8 + 3 ≤ workspace + 12 by omega).trans_lt room.workspace)
      (Rooms.spill_base full capWords bits hq) prep.1 count hc
    exact (sp.2.2.2.2.2.2.2.2 hq).2
  · intro count hc
    rw [PSTRRepairEntry.all_prefix_heap rom (savedState rom state) count hc]
    exact (spRep.2.2.2.2.2.2.2.2 hq).2
  · exact hrepair
  · intro count _hc
    rw [PSTRReplyCapacity.restore_prefix_heap]
    simpa only [show 21 = PSTRRuntimeRepair.program.length from rfl, List.take_length, repairState] using
      hrepair 21 le_rfl

end PaperProofs.Structure.LaminarTree.PSTRSelectedError
