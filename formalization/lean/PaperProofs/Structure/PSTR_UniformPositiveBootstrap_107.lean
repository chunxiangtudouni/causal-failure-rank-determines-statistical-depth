module

public import PaperProofs.Structure.PSTR_UniformWidthEntry_106

/-! NEW positive path of bootstrap63, including the actual two guard
instructions. Arbitrary entry registers, true runtime width/mask/base and
four real stores. Nothing shifts an old61/539 statement by assertion. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRUniformPositiveBootstrap

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRUniformBootstrapCode

theorem actual_bootstrap {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp) (zeroTarget : Nat)
    (cb : Contains whole zeroTarget)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (hq : 0 < q) (hl : LaminarSchedule full)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords 8192 full.length q (treeSize q full)
    let workspace := PSTRCountWorkspace.base q full capWords bits
    let after := packingRun (callInput q full command) whole (8 * CapacityBits.width q + 58) state
    after.halted = false ∧ after.pc = BitVec.ofNat bits 315 ∧
      after.register .old = BitVec.ofNat bits (workspace + 16) ∧
      after.register .index = BitVec.ofNat bits 0 ∧ after.register .fresh = BitVec.ofNat bits 0 ∧
      after.register .value = BitVec.ofNat bits 0 ∧
      (∀ offset < 4, after.heap (BitVec.ofNat bits (workspace + 12 + offset)) =
        if offset = 0 then BitVec.ofNat bits (CapacityBits.width q)
        else if offset = 1 then lowMask bits (CapacityBits.width q) else BitVec.ofNat bits 0) ∧
      (∀ physical < workspace + 12, after.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical)) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let rom := callInput q full command
  let workspace := PSTRCountWorkspace.base q full capWords bits
  let wide := packingRun rom whole (8 * CapacityBits.width q + 18) state
  let parked := executeOps rom PSTRCountInit.park wide
  let located := executeOps rom PSTRCountWorkspace.program parked
  let finished := executeOps rom PSTRCountInit.program located
  have width := PSTRUniformWidthEntry.actual_entry full command whole zeroTarget cb hwords hpcfit state hp ha
  have wide_pc : wide.pc = BitVec.ofNat bits 115 := by
    simpa only [ne_of_gt hq, ite_false] using width.2.1
  have parking := PSTRCountInit.park_registers rom wide
  have parked_pc : parked.pc = BitVec.ofNat bits 130 := by
    rw [executeOps_pc rom PSTRCountInit.park wide PSTRCountInit.park_straight, wide_pc,
      PSTRCountInit.park_length, BitVec.ofNat_add_ofNat]
  have parked_active : parked.halted = false := by rw [executeOps_halted, width.1]
  have parked_heap : parked.heap = state.heap := parking.2.2.2.2.trans width.2.2.2.2
  have parked_rep : HeapRepresents q full capWords configuration parked.heap := by rw [parked_heap]; exact rep
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords parked (by omega) hq parked_rep
  obtain ⟨located_address, _located_value, _located_index, located_old, located_fresh, located_heap, located_halted⟩ := locating
  have located_pc : located.pc = BitVec.ofNat bits 225 := by
    rw [executeOps_pc rom PSTRCountWorkspace.program parked PSTRCountWorkspace.program_straight,
      parked_pc, PSTRCountWorkspace.program_length, BitVec.ofNat_add_ofNat]
  have located_active : located.halted = false := located_halted.trans parked_active
  have regs := PSTRCountInit.execute_registers rom workspace located located_address
  have finished_pc : finished.pc = BitVec.ofNat bits 315 := by
    rw [executeOps_pc rom PSTRCountInit.program located PSTRCountInit.program_straight,
      located_pc, PSTRCountInit.program_length, BitVec.ofNat_add_ofNat]
  have finished_active : finished.halted = false := by rw [executeOps_halted, located_active]
  have parkSlice := park_contains whole zeroTarget cb
  have workspaceSlice := workspace_contains whole zeroTarget cb
  have initSlice := init_contains whole zeroTarget cb
  have run : packingRun rom whole (8 * CapacityBits.width q + 58) state = finished := by
    rw [show 8 * CapacityBits.width q + 58 = (8 * CapacityBits.width q + 18) + (3 + (19 + 18)) by omega,
      PSTRWordSegments.run_add, PSTRWordSegments.run_add,
      PSTRCountInit.containing_park rom whole 23 parkSlice.bound parkSlice.code hwords hpcfit wide wide_pc width.1,
      PSTRWordSegments.run_add,
      PSTRCountWorkspace.containing_base rom whole 26 workspaceSlice.bound workspaceSlice.code hwords hpcfit
        parked parked_pc parked_active,
      PSTRCountInit.containing_init rom whole 45 initSlice.bound initSlice.code hwords hpcfit
        located located_pc located_active]
  have hworkspace := (PSTROriginalCountRoom.workspace_rooms full 8192 8192
    (by decide) (by decide) (by decide) hq hl).1
  dsimp only
  rw [run]
  refine ⟨finished_active, finished_pc, regs.1, regs.2.1, regs.2.2.1, regs.2.2.2, ?_, ?_⟩
  · intro offset hoffset
    rw [PSTRCountInit.execute_slots rom workspace located located_address hworkspace offset hoffset,
      located_old, located_fresh, parking.1, parking.2.1, width.2.2.1, width.2.2.2.1]
  · intro physical hphysical
    exact (PSTRCountInit.execute_frame rom workspace located located_address hworkspace physical hphysical).trans
      (congrFun (located_heap.trans parked_heap) _)

theorem heap_represents {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp) (zeroTarget : Nat)
    (cb : Contains whole zeroTarget)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (hq : 0 < q) (hl : LaminarSchedule full)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap) :
    HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration
      (packingRun (callInput q full command) whole (8 * CapacityBits.width q + 58) state).heap := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := PSTRCountWorkspace.base q full capWords bits
  have result := actual_bootstrap full command configuration whole zeroTarget cb hwords hpcfit state hp ha hq hl rep
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ workspace + 12 := by
    have he := PSTRCountWorkspace.base_metadata_end q full hq capWords bits
    dsimp only [workspace]
    rw [he]
    unfold PSTRStaticHeap.metadataAddress physicalHeaderWords
    omega
  have hworkspace := (PSTROriginalCountRoom.workspace_rooms full 8192 8192
    (by decide) (by decide) (by decide) hq hl).1
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (workspace + 12) state.heap _
    (by omega) hq rep (PSTROriginalCountRoom.bitmap_room full 8192 hq)
    (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide))
    (by simpa only [Nat.add_assoc] using hworkspace) hbase
  exact result.2.2.2.2.2.2.2

end PaperProofs.Structure.LaminarTree.PSTRUniformPositiveBootstrap
