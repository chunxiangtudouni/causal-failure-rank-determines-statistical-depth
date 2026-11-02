module

public import Structure.PSTR_UniformStoreAccess_115
public import Structure.PSTR_UniformEntrySafe_110
public import Structure.PSTR_UniformCountReady_108

/-! ALL actual proper clocks of NEW bootstrap63+parent sentinel: arbitrary
seven registers, original raw input/representation and original numeric
rooms. Real two-op guard remains charged, not an erased shifted execution. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformBootstrapSafe

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRCountKernel PSTRQueryLayout PSTRCountWorkspace PSTRUniformBootstrapCode

theorem actual_safe {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp) (zeroTarget : Nat)
    (cb : Contains whole zeroTarget) (co : PSTROuterCountCode.Contains whole 63)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (clock : Nat) (hclock : clock < 8 * CapacityBits.width q + 63) :
    AtSafe (callInput q full command) whole
      (endpoint (base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
        (prepareNormalization q full).indexed.nodes.size q)
      (packingRun (callInput q full command) whole clock state) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let size := (prepareNormalization q full).indexed.nodes.size
  let heapWords := endpoint workspace size q
  let rom := callInput q full command
  let wide := packingRun rom whole (8 * CapacityBits.width q + 18) state
  let parked := executeOps rom PSTRCountInit.park wide
  let located := executeOps rom PSTRCountWorkspace.program parked
  let boot := packingRun rom whole (8 * CapacityBits.width q + 58) state
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have hroom : workspace + 15 < heapWords := by
    change workspace + 15 < endpoint workspace size q
    rw [endpoint_eq]
    omega
  have parentRoom : parentsBase workspace size < heapWords := by
    change workspace + 16 + size < endpoint workspace size q
    rw [endpoint_eq]
    omega
  have width := PSTRUniformWidthEntry.actual_entry full command whole zeroTarget cb hwords hpcfit state hp ha
  have wide_pc : wide.pc = BitVec.ofNat bits 115 := by
    simpa only [ne_of_gt hq, ite_false] using width.2.1
  have parking := PSTRCountInit.park_registers rom wide
  have parked_pc : parked.pc = BitVec.ofNat bits 130 := by
    rw [executeOps_pc rom _ wide PSTRCountInit.park_straight, wide_pc,
      PSTRCountInit.park_length, BitVec.ofNat_add_ofNat]
  have parked_active : parked.halted = false := by rw [executeOps_halted, width.1]
  have parked_heap : parked.heap = state.heap := parking.2.2.2.2.trans width.2.2.2.2
  have parked_rep : HeapRepresents q full capWords configuration parked.heap := by rw [parked_heap]; exact rep
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords parked (by omega) hq parked_rep
  have located_pc : located.pc = BitVec.ofNat bits 225 := by
    rw [executeOps_pc rom _ parked PSTRCountWorkspace.program_straight, parked_pc,
      PSTRCountWorkspace.program_length, BitVec.ofNat_add_ofNat]
  have located_active : located.halted = false := locating.2.2.2.2.2.2.trans parked_active
  have bootData := PSTRUniformPositiveBootstrap.actual_bootstrap full command configuration whole zeroTarget cb hwords hpcfit
    state hp ha hq hl rep
  have bootRep := PSTRUniformPositiveBootstrap.heap_represents full command configuration whole zeroTarget cb hwords hpcfit
    state hp ha hq hl rep
  have boot_base : boot.register .old = BitVec.ofNat bits (countsBase workspace) := bootData.2.2.1
  have boot_tree : boot.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using (PSTRStaticHeap.headers full configuration capWords boot.heap bootRep).1
  have ps := park_contains whole zeroTarget cb
  have ws := workspace_contains whole zeroTarget cb
  have parkRun := PSTRCountInit.containing_park rom whole 23 ps.bound ps.code hwords hpcfit wide wide_pc width.1
  have workspaceRun := PSTRCountWorkspace.containing_base rom whole 26 ws.bound ws.code hwords hpcfit
    parked parked_pc parked_active
  by_cases hwide : clock < 8 * CapacityBits.width q + 18
  · exact PSTRUniformEntrySafe.entry_safe full command whole zeroTarget heapWords cb hwords hpcfit state hp ha clock hwide
  · by_cases hpark : clock < 8 * CapacityBits.width q + 21
    · rw [show clock = (8 * CapacityBits.width q + 18) + (clock - (8 * CapacityBits.width q + 18)) by omega,
        PSTRWordSegments.run_add]
      exact PSTRUniformStoreAccess.park_safe rom whole zeroTarget cb hwords hpcfit heapWords wide wide_pc width.1
        (clock - (8 * CapacityBits.width q + 18)) (by omega)
    · by_cases hlocate : clock < 8 * CapacityBits.width q + 40
      · rw [show clock = (8 * CapacityBits.width q + 18) + (3 + (clock - (8 * CapacityBits.width q + 21))) by omega,
          PSTRWordSegments.run_add, PSTRWordSegments.run_add, parkRun]
        exact PSTRUniformStoreAccess.workspace_safe full command configuration capWords heapWords parked whole zeroTarget cb hwords hpcfit
          (by omega) parked_rep (by change workspace < heapWords; omega) parked_pc parked_active
          (clock - (8 * CapacityBits.width q + 21)) (by omega)
      · by_cases hinit : clock < 8 * CapacityBits.width q + 58
        · rw [show clock = (8 * CapacityBits.width q + 18) + (3 + (19 + (clock - (8 * CapacityBits.width q + 40)))) by omega,
            PSTRWordSegments.run_add, PSTRWordSegments.run_add, parkRun, PSTRWordSegments.run_add, workspaceRun]
          exact PSTRUniformStoreAccess.init_safe full command capWords heapWords located whole zeroTarget cb hwords hpcfit
            locating.1 hroom located_pc located_active (clock - (8 * CapacityBits.width q + 40)) (by omega)
        · rw [show clock = (8 * CapacityBits.width q + 58) + (clock - (8 * CapacityBits.width q + 58)) by omega,
            PSTRWordSegments.run_add]
          exact PSTRBootstrapStoreAccess.sentinel_safe rom whole 63 workspace size heapWords
            (PSTROuterCountCode.sentinel_at whole 63 co) hwords hpcfit boot boot_base boot_tree parentRoom bootData.2.1 bootData.1
            (clock - (8 * CapacityBits.width q + 58)) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRUniformBootstrapSafe
