module

public import PaperProofs.Structure.PSTR_BootstrapPrefix_077

/-! All actual bootstrap prefixes frame BOTH the original low persistent
physical area and the high suffix, including opaque void-row payload bits. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBootstrapOutside

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTROuterCountCode PSTRCountWorkspace PSTRBootstrapPrefix

theorem actual_prefix {bits q : Nat} (whole : List PackingOp) (hc : PSTRBootstrapSlices.Contains whole)
    (hwords : WordsFit bits (packingCode whole)) (hpcfit : Fits bits (5 * whole.length))
    (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (capWords : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 9 ≤ bits) (hq : 0 < q) (rep : HeapRepresents q full capWords configuration heap)
    (hN : Fits bits full.length) (hpos : Fits bits (2 + full.length * q))
    (hwidthroom : Fits bits (2 * (q + 1)))
    (hworkspace : Fits bits (base q full capWords bits + 15))
    (bitmap : tableWords full.length q (treeSize q full) + q ≤ capWords)
    (hcapacity : Fits bits (4 + capWords * CapacityBits.width q))
    (clock : Nat) (hclock : clock ≤ 8 * CapacityBits.width q + 56) :
    let result := packingRun (callInput q full command) whole clock (packingInitial heap)
    HeapRepresents q full capWords configuration result.heap ∧
      ∀ physical, Fits bits physical → (physical < base q full capWords bits ∨ base q full capWords bits + 16 ≤ physical) →
        result.heap (BitVec.ofNat bits physical) = heap (BitVec.ofNat bits physical) := by
  let rom := callInput q full command
  let workspace := base q full capWords bits
  let wide := packingRun rom whole (8 * CapacityBits.width q + 16) (packingInitial heap)
  let parked := executeOps rom PSTRCountInit.park wide
  let located := executeOps rom PSTRCountWorkspace.program parked
  have width := PSTRBootstrapSlices.width_run whole hc hwords hpcfit full command heap (by omega) hN hpos hwidthroom
  have parking := PSTRCountInit.park_registers rom wide
  have parked_pc : parked.pc = BitVec.ofNat bits 120 := by
    rw [executeOps_pc rom _ wide PSTRCountInit.park_straight, width.2.1,
      PSTRCountInit.park_length, BitVec.ofNat_add_ofNat]
  have parked_active : parked.halted = false := by rw [executeOps_halted, width.1]
  have parked_heap : parked.heap = heap := parking.2.2.2.2.trans width.2.2.2.2
  have parked_rep : HeapRepresents q full capWords configuration parked.heap := by rw [parked_heap]; exact rep
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords parked (by omega) hq parked_rep
  obtain ⟨located_address, _value, _index, _old, _fresh, located_heap, located_halted⟩ := locating
  have located_pc : located.pc = BitVec.ofNat bits 215 := by
    rw [executeOps_pc rom _ parked PSTRCountWorkspace.program_straight, parked_pc,
      PSTRCountWorkspace.program_length, BitVec.ofNat_add_ofNat]
  have located_active : located.halted = false := located_halted.trans parked_active
  have located_original : located.heap = heap := located_heap.trans parked_heap
  have located_rep : HeapRepresents q full capWords configuration located.heap := by rw [located_original]; exact rep
  have ps := park_at whole hc
  have ws := workspace_at whole hc
  have ins := init_at whole hc
  have parent_park := PSTRBootstrapSlices.park_run rom whole hc hwords hpcfit wide width.2.1 width.1
  have parent_workspace := PSTRBootstrapSlices.workspace_run rom whole hc hwords hpcfit parked parked_pc parked_active
  have conclude_heap (current : WordState bits) (hh : current.heap = heap) :
      HeapRepresents q full capWords configuration current.heap ∧
        ∀ physical, Fits bits physical → (physical < workspace ∨ workspace + 16 ≤ physical) →
          current.heap (BitVec.ofNat bits physical) = heap (BitVec.ofNat bits physical) := by
    rw [hh]
    exact ⟨rep, fun _ _ _ => rfl⟩
  dsimp only
  by_cases hwide : clock ≤ 8 * CapacityBits.width q + 16
  · exact conclude_heap _ (width_prefix_heap whole hc hwords hpcfit full command heap (by omega) hN hpos hwidthroom clock hwide)
  · by_cases hpark : clock ≤ 8 * CapacityBits.width q + 19
    · rw [show clock = (8 * CapacityBits.width q + 16) + (clock - (8 * CapacityBits.width q + 16)) by omega,
        PSTRWordSegments.run_add,
        PSTRWidthPrefix.straight_prefix rom whole PSTRCountInit.park 21 ps.bound ps.code PSTRCountInit.park_straight
          hwords hpcfit wide width.2.1 width.1 (clock - (8 * CapacityBits.width q + 16))
          (by rw [PSTRCountInit.park_length]; omega)]
      exact conclude_heap _ ((readonly_prefix_heap rom _ wide park_no_store _).trans width.2.2.2.2)
    · by_cases hlocate : clock ≤ 8 * CapacityBits.width q + 38
      · rw [show clock = (8 * CapacityBits.width q + 16) + (3 + (clock - (8 * CapacityBits.width q + 19))) by omega,
          PSTRWordSegments.run_add, PSTRWordSegments.run_add, parent_park,
          PSTRWidthPrefix.straight_prefix rom whole PSTRCountWorkspace.program 24 ws.bound ws.code PSTRCountWorkspace.program_straight
            hwords hpcfit parked parked_pc parked_active (clock - (8 * CapacityBits.width q + 19))
            (by rw [PSTRCountWorkspace.program_length]; omega)]
        exact conclude_heap _ ((readonly_prefix_heap rom _ parked workspace_no_store _).trans parked_heap)
      · let count := clock - (8 * CapacityBits.width q + 38)
        rw [show clock = (8 * CapacityBits.width q + 16) + (3 + (19 + count)) by dsimp only [count]; omega,
          PSTRWordSegments.run_add, PSTRWordSegments.run_add, parent_park,
          PSTRWordSegments.run_add, parent_workspace,
          PSTRWidthPrefix.straight_prefix rom whole PSTRCountInit.program 43 ins.bound ins.code PSTRCountInit.program_straight
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
          rcases hh with low | high
          · exact (PSTRCountInit.prefix_frame rom workspace located located_address hworkspace physical
              (by omega) count).trans (congrFun located_original _)
          · exact (PSTROuterStoreFrame.init_prefix_high rom workspace located located_address hworkspace physical hp
              (by omega) count).trans (congrFun located_original _)

end PaperProofs.Structure.LaminarTree.PSTRBootstrapOutside
