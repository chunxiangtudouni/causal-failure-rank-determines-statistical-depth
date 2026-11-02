module

public import PaperProofs.Structure.PSTR_BootstrapSlices_057

/-! The actual raw bootstrap INSIDE the caller's full containing program.
All source reads, width loop, parking, W locator and writes use that ONE
program and its true PC. No halted helper or packingInitial reset is used
between bootstrap and the caller's later count/tail code. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBootstrapIn

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRCountBootstrapCode

theorem actual_bootstrap {bits q : Nat} (whole : List PackingOp) (hc : PSTRBootstrapSlices.Contains whole)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 9 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration heap)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hwidthroom : Fits bits (2 * (q + 1)))
    (hworkspace : Fits bits (PSTRCountWorkspace.base q full capWords bits + 15)) :
    let workspace := PSTRCountWorkspace.base q full capWords bits
    let after := packingRun (callInput q full command) whole (8 * CapacityBits.width q + 56) (packingInitial heap)
    after.halted = false ∧ after.pc = BitVec.ofNat bits 305 ∧
      after.register .old = BitVec.ofNat bits (workspace + 16) ∧
      after.register .index = BitVec.ofNat bits 0 ∧
      after.register .fresh = BitVec.ofNat bits 0 ∧
      after.register .value = BitVec.ofNat bits 0 ∧
      (∀ offset < 4, after.heap (BitVec.ofNat bits (workspace + 12 + offset)) =
        if offset = 0 then BitVec.ofNat bits (CapacityBits.width q)
        else if offset = 1 then lowMask bits (CapacityBits.width q) else BitVec.ofNat bits 0) ∧
      (∀ address < workspace + 12, after.heap (BitVec.ofNat bits address) = heap (BitVec.ofNat bits address)) := by
  let rom := callInput q full command
  let workspace := PSTRCountWorkspace.base q full capWords bits
  let wide := packingRun rom whole (8 * CapacityBits.width q + 16) (packingInitial heap)
  let parked := executeOps rom PSTRCountInit.park wide
  let located := executeOps rom PSTRCountWorkspace.program parked
  let finished := executeOps rom PSTRCountInit.program located
  have width := PSTRBootstrapSlices.width_run whole hc hwords hpcfit full command heap (by omega) hN hpos hwidthroom
  have parking := PSTRCountInit.park_registers rom wide
  have parked_pc : parked.pc = BitVec.ofNat bits 120 := by
    rw [executeOps_pc rom PSTRCountInit.park wide PSTRCountInit.park_straight, width.2.1,
      PSTRCountInit.park_length, BitVec.ofNat_add_ofNat]
  have parked_active : parked.halted = false := by rw [executeOps_halted, width.1]
  have parked_heap : parked.heap = heap := parking.2.2.2.2.trans width.2.2.2.2
  have parked_rep : HeapRepresents q full capWords configuration parked.heap := by rw [parked_heap]; exact rep
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords parked (by omega) hq parked_rep
  obtain ⟨located_address, _located_value, _located_index, located_old, located_fresh, located_heap, located_halted⟩ := locating
  have located_pc : located.pc = BitVec.ofNat bits 215 := by
    rw [executeOps_pc rom PSTRCountWorkspace.program parked PSTRCountWorkspace.program_straight,
      parked_pc, PSTRCountWorkspace.program_length, BitVec.ofNat_add_ofNat]
  have located_active : located.halted = false := located_halted.trans parked_active
  have regs := PSTRCountInit.execute_registers rom workspace located located_address
  have finished_pc : finished.pc = BitVec.ofNat bits 305 := by
    rw [executeOps_pc rom PSTRCountInit.program located PSTRCountInit.program_straight,
      located_pc, PSTRCountInit.program_length, BitVec.ofNat_add_ofNat]
  have finished_active : finished.halted = false := by rw [executeOps_halted, located_active]
  have run : packingRun rom whole (8 * CapacityBits.width q + 56) (packingInitial heap) = finished := by
    rw [show 8 * CapacityBits.width q + 56 = (8 * CapacityBits.width q + 16) + (3 + (19 + 18)) by omega,
      PSTRWordSegments.run_add, PSTRWordSegments.run_add,
      PSTRBootstrapSlices.park_run rom whole hc hwords hpcfit wide width.2.1 width.1,
      PSTRWordSegments.run_add, PSTRBootstrapSlices.workspace_run rom whole hc hwords hpcfit parked parked_pc parked_active,
      PSTRBootstrapSlices.init_run rom whole hc hwords hpcfit located located_pc located_active]
  dsimp only
  rw [run]
  refine ⟨finished_active, finished_pc, regs.1, regs.2.1, regs.2.2.1, regs.2.2.2, ?_, ?_⟩
  · intro offset hoffset
    rw [PSTRCountInit.execute_slots rom workspace located located_address hworkspace offset hoffset,
      located_old, located_fresh, parking.1, parking.2.1, width.2.2.1, width.2.2.2.1]
  · intro address haddress
    exact (PSTRCountInit.execute_frame rom workspace located located_address hworkspace address haddress).trans
      (congrFun (located_heap.trans parked_heap) _)

theorem heap_represents {bits q : Nat} (whole : List PackingOp) (hc : PSTRBootstrapSlices.Contains whole)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 9 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration heap)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hwidthroom : Fits bits (2 * (q + 1)))
    (hworkspace : Fits bits (PSTRCountWorkspace.base q full capWords bits + 15))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hcapacity : Fits bits (4 + capWords * CapacityBits.width q)) :
    HeapRepresents q full capWords configuration
      (packingRun (callInput q full command) whole (8 * CapacityBits.width q + 56) (packingInitial heap)).heap := by
  have result := actual_bootstrap whole hc hwords hpcfit full command configuration capWords heap hb hq rep hN hpos hwidthroom hworkspace
  let workspace := PSTRCountWorkspace.base q full capWords bits
  have hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ workspace + 12 := by
    have he := PSTRCountWorkspace.base_metadata_end q full hq capWords bits
    dsimp only [workspace]
    rw [he]
    unfold PSTRStaticHeap.metadataAddress physicalHeaderWords
    omega
  apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (workspace + 12) heap _
    (by omega) hq rep bitmap hcapacity (by simpa only [Nat.add_assoc] using hworkspace) hbase
  exact result.2.2.2.2.2.2.2

end PaperProofs.Structure.LaminarTree.PSTRBootstrapIn
