module

public import Structure.PSTR_UniformEntrySafe_110
public import Structure.PSTR_BootstrapOutside_084

/-! ALL actual prefixes of NEW guarded bootstrap63 preserve original
representation and both low persistent/high physical areas, arbitrary regs. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PSTRUniformBootstrapOutside
open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace
open PSTRBootstrapPrefix

theorem actual_prefix {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp) (zeroTarget : Nat)
    (cb : PSTRUniformBootstrapCode.Contains whole zeroTarget)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (clock : Nat) (hclock : clock ≤ 8 * CapacityBits.width q + 58) :
    let bits := indexWidth 32 full.length q
    let capWords := capacityWords 8192 full.length q (treeSize q full)
    let result := packingRun (callInput q full command) whole clock state
    HeapRepresents q full capWords configuration result.heap ∧
      ∀ physical, Fits bits physical →
        (physical < base q full capWords bits ∨ base q full capWords bits + 16 ≤ physical) →
        result.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have hworkspace := (PSTROriginalCountRoom.workspace_rooms full 8192 8192
    (by decide) (by decide) (by decide) hq hl).1
  have bitmap := PSTROriginalCountRoom.bitmap_room full 8192 hq
  have hcapacity := PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)
  let rom := callInput q full command
  let workspace := base q full capWords bits
  let wide := packingRun rom whole (8 * CapacityBits.width q + 18) state
  let parked := executeOps rom PSTRCountInit.park wide
  let located := executeOps rom PSTRCountWorkspace.program parked
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
  obtain ⟨located_address, _value, _index, _old, _fresh, located_heap, located_halted⟩ := locating
  have located_pc : located.pc = BitVec.ofNat bits 225 := by
    rw [executeOps_pc rom _ parked PSTRCountWorkspace.program_straight, parked_pc,
      PSTRCountWorkspace.program_length, BitVec.ofNat_add_ofNat]
  have located_active : located.halted = false := located_halted.trans parked_active
  have located_original : located.heap = state.heap := located_heap.trans parked_heap
  have located_rep : HeapRepresents q full capWords configuration located.heap := by rw [located_original]; exact rep
  have ps := PSTRUniformBootstrapCode.park_contains whole zeroTarget cb
  have ws := PSTRUniformBootstrapCode.workspace_contains whole zeroTarget cb
  have ins := PSTRUniformBootstrapCode.init_contains whole zeroTarget cb
  have parent_park := PSTRCountInit.containing_park rom whole 23 ps.bound ps.code hwords hpcfit wide wide_pc width.1
  have parent_workspace := PSTRCountWorkspace.containing_base rom whole 26 ws.bound ws.code hwords hpcfit parked parked_pc parked_active
  have conclude_heap (current : WordState bits) (hh : current.heap = state.heap) :
      HeapRepresents q full capWords configuration current.heap ∧
        ∀ physical, Fits bits physical → (physical < workspace ∨ workspace + 16 ≤ physical) →
          current.heap (BitVec.ofNat bits physical) = state.heap (BitVec.ofNat bits physical) := by
    rw [hh]
    exact ⟨rep, fun _ _ _ => rfl⟩
  dsimp only
  by_cases hwide : clock ≤ 8 * CapacityBits.width q + 18
  · exact conclude_heap _ (PSTRUniformEntrySafe.entry_prefix_heap full command whole zeroTarget cb hwords hpcfit state hp ha clock hwide)
  · by_cases hpark : clock ≤ 8 * CapacityBits.width q + 21
    · rw [show clock = (8 * CapacityBits.width q + 18) + (clock - (8 * CapacityBits.width q + 18)) by omega,
        PSTRWordSegments.run_add,
        PSTRWidthPrefix.straight_prefix rom whole PSTRCountInit.park 23 ps.bound ps.code PSTRCountInit.park_straight
          hwords hpcfit wide wide_pc width.1 (clock - (8 * CapacityBits.width q + 18))
          (by rw [PSTRCountInit.park_length]; omega)]
      exact conclude_heap _ ((readonly_prefix_heap rom _ wide park_no_store _).trans width.2.2.2.2)
    · by_cases hlocate : clock ≤ 8 * CapacityBits.width q + 40
      · rw [show clock = (8 * CapacityBits.width q + 18) + (3 + (clock - (8 * CapacityBits.width q + 21))) by omega,
          PSTRWordSegments.run_add, PSTRWordSegments.run_add, parent_park,
          PSTRWidthPrefix.straight_prefix rom whole PSTRCountWorkspace.program 26 ws.bound ws.code PSTRCountWorkspace.program_straight
            hwords hpcfit parked parked_pc parked_active (clock - (8 * CapacityBits.width q + 21))
            (by rw [PSTRCountWorkspace.program_length]; omega)]
        exact conclude_heap _ ((readonly_prefix_heap rom _ parked workspace_no_store _).trans parked_heap)
      · let count := clock - (8 * CapacityBits.width q + 40)
        rw [show clock = (8 * CapacityBits.width q + 18) + (3 + (19 + count)) by dsimp only [count]; omega,
          PSTRWordSegments.run_add, PSTRWordSegments.run_add, parent_park,
          PSTRWordSegments.run_add, parent_workspace,
          PSTRWidthPrefix.straight_prefix rom whole PSTRCountInit.program 45 ins.bound ins.code PSTRCountInit.program_straight
            hwords hpcfit located located_pc located_active count
            (by rw [PSTRCountInit.program_length]; dsimp only [count]; omega)]
        constructor
        · have hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ workspace + 12 := by
            dsimp only [workspace]
            rw [base_metadata_end q full hq]
            unfold PSTRStaticHeap.metadataAddress physicalHeaderWords
            omega
          apply PSTRRepairHeap.heapRepresents_of_prefix_frame full configuration capWords (workspace + 12) located.heap _
            (by omega) hq located_rep bitmap hcapacity (by simpa only [Nat.add_assoc] using hworkspace) hbase
          intro physical hp
          exact PSTRCountInit.prefix_frame rom workspace located located_address hworkspace physical hp count
        · intro physical hp hh
          change physical < workspace ∨ workspace + 16 ≤ physical at hh
          rcases hh with low | high
          · exact (PSTRCountInit.prefix_frame rom workspace located located_address hworkspace physical
              (by omega) count).trans (congrFun located_original _)
          · exact (PSTROuterStoreFrame.init_prefix_high rom workspace located located_address hworkspace physical hp
              (by omega) count).trans (congrFun located_original _)

end PaperProofs.Structure.LaminarTree.PSTRUniformBootstrapOutside
