module

public import PaperProofs.Structure.PSTR_BootstrapStoreAccess_098

/-! Every proper clock of the ORIGINAL raw bootstrap and actual sentinel
has true containing-code fetch/decode/access. Original numeric obligations
are discharged at w32/RF=IF8192, not passed as new original qualifications. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRBootstrapSafe

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open PSTRCountKernel PSTRQueryLayout PSTRCountWorkspace

theorem actual_safe {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp)
    (cb : PSTRBootstrapSlices.Contains whole) (co : PSTROuterCountCode.Contains whole 61)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration heap)
    (clock : Nat) (hclock : clock < 8 * CapacityBits.width q + 61) :
    AtSafe (callInput q full command) whole
      (endpoint (base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
        (prepareNormalization q full).indexed.nodes.size q)
      (packingRun (callInput q full command) whole clock (packingInitial heap)) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let size := (prepareNormalization q full).indexed.nodes.size
  let heapWords := endpoint workspace size q
  let rom := callInput q full command
  let headed := executeOps rom PSTRLiveHeader.program (packingInitial heap)
  let wide := packingRun rom whole (8 * CapacityBits.width q + 16) (packingInitial heap)
  let parked := executeOps rom PSTRCountInit.park wide
  let located := executeOps rom PSTRCountWorkspace.program parked
  let boot := packingRun rom whole (8 * CapacityBits.width q + 56) (packingInitial heap)
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have dimensions := PSTROriginalCountRoom.dimension_rooms full
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have hroom : workspace + 15 < heapWords := by
    change workspace + 15 < endpoint workspace size q
    rw [endpoint_eq]
    omega
  have parentRoom : parentsBase workspace size < heapWords := by
    change workspace + 16 + size < endpoint workspace size q
    rw [endpoint_eq]
    omega
  have regs := PSTRLiveHeader.execute_registers full command (packingInitial heap) (by omega) raw.1 dimensions.2.2.2.2 raw.2.1
  have headed_fresh : (headed.register .fresh).toNat = q := by
    rw [regs.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt dimensions.2.2.2.2]
  have headed_pc : headed.pc = BitVec.ofNat bits 40 := by
    rw [executeOps_pc rom _ (packingInitial heap) PSTRLiveHeader.program_straight]
    change BitVec.ofNat bits 0 + BitVec.ofNat bits (5 * PSTRLiveHeader.program.length) = _
    rw [BitVec.zero_add, PSTRLiveHeader.program_length]
  have headed_active : headed.halted = false := by rw [executeOps_halted]; rfl
  have width := PSTRBootstrapSlices.width_run whole cb hwords hpcfit full command heap (by omega) raw.1 raw.2.1 raw.2.2
  have parking := PSTRCountInit.park_registers rom wide
  have parked_pc : parked.pc = BitVec.ofNat bits 120 := by
    rw [executeOps_pc rom _ wide PSTRCountInit.park_straight, width.2.1,
      PSTRCountInit.park_length, BitVec.ofNat_add_ofNat]
  have parked_active : parked.halted = false := by rw [executeOps_halted, width.1]
  have parked_heap : parked.heap = heap := parking.2.2.2.2.trans width.2.2.2.2
  have parked_rep : HeapRepresents q full capWords configuration parked.heap := by rw [parked_heap]; exact rep
  have locating := PSTRCountWorkspace.execute_base full command configuration capWords parked (by omega) hq parked_rep
  have located_pc : located.pc = BitVec.ofNat bits 215 := by
    rw [executeOps_pc rom _ parked PSTRCountWorkspace.program_straight, parked_pc,
      PSTRCountWorkspace.program_length, BitVec.ofNat_add_ofNat]
  have located_active : located.halted = false := locating.2.2.2.2.2.2.trans parked_active
  have bootData := PSTRBootstrapIn.actual_bootstrap whole cb hwords hpcfit full command configuration capWords heap
    (by omega) hq rep raw.1 raw.2.1 raw.2.2 rooms.1
  have bootRep := PSTRBootstrapIn.heap_represents whole cb hwords hpcfit full command configuration capWords heap
    (by omega) hq rep raw.1 raw.2.1 raw.2.2 rooms.1 (PSTROriginalCountRoom.bitmap_room full 8192 hq)
    (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide))
  have boot_base : boot.register .old = BitVec.ofNat bits (countsBase workspace) := bootData.2.2.1
  have boot_tree : boot.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using (PSTRStaticHeap.headers full configuration capWords boot.heap bootRep).1
  have parkRun := PSTRBootstrapSlices.park_run rom whole cb hwords hpcfit wide width.2.1 width.1
  have workspaceRun := PSTRBootstrapSlices.workspace_run rom whole cb hwords hpcfit parked parked_pc parked_active
  by_cases hhead : clock < 8
  · exact PSTRBootstrapStoreAccess.header_safe full command whole cb hwords hpcfit heapWords (packingInitial heap)
      (by omega) raw.1 dimensions.2.2.2.2 raw.2.1 rfl rfl clock hhead
  · by_cases hwide : clock < 8 * CapacityBits.width q + 16
    · have hm : 8 + 12 < whole.length := by have hh := cb.bound; omega
      have mask : whole[8 + 12]'hm = PSTRWidthEmbedded.maskOp :=
        (cb.code 20 (by rw [PSTRCountBootstrapCode.program_length]; decide)).trans (by rfl)
      rw [show clock = 8 + (clock - 8) by omega, PSTRWordSegments.run_add,
        PSTRBootstrapSlices.header_run rom whole cb hwords hpcfit (packingInitial heap) rfl rfl]
      exact PSTRWidthAccess.width_mask_safe rom whole 8 heapWords (PSTRBootstrapSlices.width_contains whole cb) hwords hpcfit
        (by have hh := cb.bound; omega) mask q headed headed_fresh headed_pc headed_active raw.2.2 (clock - 8) (by omega)
    · by_cases hpark : clock < 8 * CapacityBits.width q + 19
      · rw [show clock = (8 * CapacityBits.width q + 16) + (clock - (8 * CapacityBits.width q + 16)) by omega,
          PSTRWordSegments.run_add]
        exact PSTRBootstrapStoreAccess.park_safe rom whole cb hwords hpcfit heapWords wide width.2.1 width.1
          (clock - (8 * CapacityBits.width q + 16)) (by omega)
      · by_cases hlocate : clock < 8 * CapacityBits.width q + 38
        · rw [show clock = (8 * CapacityBits.width q + 16) + (3 + (clock - (8 * CapacityBits.width q + 19))) by omega,
            PSTRWordSegments.run_add, PSTRWordSegments.run_add, parkRun]
          exact PSTRBootstrapStoreAccess.workspace_safe full command configuration capWords heapWords parked whole cb hwords hpcfit
            (by omega) parked_rep (by change workspace < heapWords; omega) parked_pc parked_active
            (clock - (8 * CapacityBits.width q + 19)) (by omega)
        · by_cases hinit : clock < 8 * CapacityBits.width q + 56
          · rw [show clock = (8 * CapacityBits.width q + 16) + (3 + (19 + (clock - (8 * CapacityBits.width q + 38)))) by omega,
              PSTRWordSegments.run_add, PSTRWordSegments.run_add, parkRun, PSTRWordSegments.run_add, workspaceRun]
            exact PSTRBootstrapStoreAccess.init_safe full command capWords heapWords located whole cb hwords hpcfit
              locating.1 hroom located_pc located_active (clock - (8 * CapacityBits.width q + 38)) (by omega)
          · rw [show clock = (8 * CapacityBits.width q + 56) + (clock - (8 * CapacityBits.width q + 56)) by omega,
              PSTRWordSegments.run_add]
            exact PSTRBootstrapStoreAccess.sentinel_safe rom whole 61 workspace size heapWords
              (PSTROuterCountCode.sentinel_at whole 61 co) hwords hpcfit boot boot_base boot_tree parentRoom bootData.2.1 bootData.1
              (clock - (8 * CapacityBits.width q + 56)) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRBootstrapSafe
