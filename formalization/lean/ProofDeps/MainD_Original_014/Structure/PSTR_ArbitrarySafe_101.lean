module

public import Structure.PSTR_CountCompleteSafe_100
public import Structure.PSTR_ArbitraryOutside_086

/-! Original arbitrary-register count producer, now with the SAME witness
for complete data, all heap/table/capacity frames and all actual safety. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRArbitrarySafe

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace PSTRArbitraryOutside

theorem early_safe {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (whole : List PackingOp) (cb : PSTRBootstrapSlices.Contains whole)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length)) (heapWords : Nat)
    (state : WordState (indexWidth 32 full.length q))
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false)
    (clock : Nat) (hclock : clock < 14) :
    PSTRCountKernel.AtSafe (callInput q full command) whole heapWords (packingRun (callInput q full command) whole clock state) := by
  let bits := indexWidth 32 full.length q
  let rom := callInput q full command
  let headed := executeOps rom PSTRLiveHeader.program state
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have qfit := (PSTROriginalCountRoom.dimension_rooms full).2.2.2.2
  by_cases hfirst : clock < 8
  · exact PSTRBootstrapStoreAccess.header_safe full command whole cb hwords hpcfit heapWords state
      (by omega) raw.1 qfit raw.2.1 hp ha clock hfirst
  · have regs := PSTRLiveHeader.execute_registers full command state (by omega) raw.1 qfit raw.2.1
    have fresh : (headed.register .fresh).toNat = q := by
      rw [regs.2.1, BitVec.toNat_ofNat, Nat.mod_eq_of_lt qfit]
    have pc : headed.pc = BitVec.ofNat bits 40 := by
      rw [executeOps_pc rom _ state PSTRLiveHeader.program_straight, hp,
        PSTRLiveHeader.program_length, BitVec.ofNat_add_ofNat]
    have active : headed.halted = false := by rw [executeOps_halted, ha]
    have hm : 8 + 12 < whole.length := by have hh := cb.bound; omega
    have mask : whole[8 + 12]'hm = PSTRWidthEmbedded.maskOp :=
      (cb.code 20 (by rw [PSTRCountBootstrapCode.program_length]; decide)).trans (by rfl)
    rw [show clock = 8 + (clock - 8) by omega, PSTRWordSegments.run_add,
      PSTRBootstrapSlices.header_run rom whole cb hwords hpcfit state hp ha]
    exact PSTRWidthAccess.width_mask_safe rom whole 8 heapWords (PSTRBootstrapSlices.width_contains whole cb)
      hwords hpcfit (by have hh := cb.bound; omega) mask q headed fresh pc active raw.2.2 (clock - 8) (by omega)

theorem actual_complete {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp)
    (cb : PSTRBootstrapSlices.Contains whole) (co : PSTROuterCountCode.Contains whole 61)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (state : WordState (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration state.heap)
    (hp : state.pc = BitVec.ofNat (indexWidth 32 full.length q) 0) (ha : state.halted = false) :
    ∃ steps, 66 ≤ steps ∧
      steps ≤ 8 * CapacityBits.width q + 66 + 501 * (prepareNormalization q full).indexed.nodes.size ∧
      PSTRCountComplete.Complete full configuration 61 (capacityWords 8192 full.length q (treeSize q full))
        (packingRun (callInput q full command) whole steps state) ∧
      (∀ clock ≤ steps,
        let result := packingRun (callInput q full command) whole clock state
        HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
        ∀ physical, Fits (indexWidth 32 full.length q) physical →
          (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
          result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) = state.heap (BitVec.ofNat (indexWidth 32 full.length q) physical)) ∧
      (∀ clock ≤ steps, CapacityPrefixBounded q (capacityWords 8192 full.length q (treeSize q full))
        (logicalHeap q (capacityWords 8192 full.length q (treeSize q full))
          (packingRun (callInput q full command) whole clock state).heap)) ∧
      (∀ clock ≤ steps, ∀ address < tableWords full.length q (treeSize q full),
        logicalHeap q (capacityWords 8192 full.length q (treeSize q full))
          (packingRun (callInput q full command) whole clock state).heap address =
        logicalHeap q (capacityWords 8192 full.length q (treeSize q full)) state.heap address) ∧
      (∀ clock < steps, PSTRCountKernel.AtSafe (callInput q full command) whole
        (endpoint (base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
          (prepareNormalization q full).indexed.nodes.size q)
        (packingRun (callInput q full command) whole clock state)) := by
  let rom := callInput q full command
  have entry := PSTRArbitraryEntry.of_bootstrap whole cb
  obtain ⟨steps, lower, upper, complete, prefixes, fetches⟩ := PSTRCountCompleteSafe.actual_complete full command configuration
    whole cb co hwords hpcfit hq hl state.heap rep
  have frames : ∀ clock ≤ steps,
      let result := packingRun rom whole clock state
      HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
      ∀ physical, Fits (indexWidth 32 full.length q) physical →
        (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
        result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) = state.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) := by
    intro clock hclock
    dsimp only
    by_cases hearly : clock ≤ 14
    · have he := entry_prefix_heap rom whole entry hwords hpcfit state hp ha clock hearly
      constructor
      · rw [he]
        exact rep
      · intro physical _ _
        rw [he]
    · rw [PSTRArbitraryEntry.run_from_arbitrary rom whole entry hwords hpcfit state hp ha clock (by omega)]
      exact prefixes clock hclock
  refine ⟨steps, lower, upper, ?_, frames, ?_, ?_, ?_⟩
  · rw [PSTRArbitraryEntry.run_from_arbitrary rom whole entry hwords hpcfit state hp ha steps (by omega)]
    exact complete
  · intro clock hclock
    exact represents_capacity full configuration _ _ hq (frames clock hclock).1
  · intro clock hclock address ha
    have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
    have bitmap := PSTROriginalCountRoom.bitmap_room full 8192 hq
    apply persistent_logical_frame full state.heap (packingRun rom whole clock state).heap hq hl ?_ address (by omega)
    intro physical hphysical
    have hp : Fits (indexWidth 32 full.length q) physical :=
      hphysical.trans ((Nat.le_add_right _ 15).trans_lt rooms.1)
    exact (frames clock hclock).2 physical hp (Or.inl hphysical)

  · intro clock hclock
    by_cases hearly : clock < 14
    · exact early_safe full command whole cb hwords hpcfit _ state hp ha clock hearly
    · rw [PSTRArbitraryEntry.run_from_arbitrary rom whole entry hwords hpcfit state hp ha clock (by omega)]
      exact fetches clock hclock

end PaperProofs.Structure.LaminarTree.PSTRArbitrarySafe
