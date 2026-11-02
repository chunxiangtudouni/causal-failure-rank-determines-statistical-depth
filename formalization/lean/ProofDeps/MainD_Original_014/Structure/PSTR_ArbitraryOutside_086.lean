module

public import Structure.PSTR_CountCompleteOutside_085
public import Structure.PSTR_ArbitraryEntry_060

/-! The complete prefix certificate after a real heads jump0, with
arbitrary seven incoming registers. First14 are actually fetched/charged;
every earlier prefix is proved directly, and later clocks use real equality. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRArbitraryOutside

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace

theorem entry_prefix_heap {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp)
    (hc : PSTRArbitraryEntry.Contains whole) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (clock : Nat) (hclock : clock ≤ 14) :
    (packingRun rom whole clock state).heap = state.heap := by
  rw [PSTRWidthPrefix.straight_prefix rom whole PSTRArbitraryEntry.entryLead 0
    (by have hh := hc.bound; rw [PSTRArbitraryEntry.entryLead_length]; omega)
    (fun i hi => by simpa only [Nat.zero_add] using hc.code i hi)
    PSTRArbitraryEntry.entryLead_straight hw hpcfit state hp ha clock hclock]
  apply executeOps_heap_of_no_store
  intro op ho
  have hno : ∀ entry ∈ PSTRArbitraryEntry.entryLead, HeapPreservingOp entry := by
    simp [PSTRArbitraryEntry.entryLead, PSTRLiveHeader.program, PSTRRuntimeWidth.initCode,
      PSTRWidthKernel.testLeadAt, HeapPreservingOp]
  exact hno op (List.mem_of_mem_take ho)

theorem represents_capacity {bits q : Nat} (full : List (Finset (Fin q)))
    (configuration : Configuration q) (capWords : Nat) (heap : BitVec bits → BitVec bits)
    (hq : 0 < q) (rep : HeapRepresents q full capWords configuration heap) :
    CapacityPrefixBounded q capWords (logicalHeap q capWords heap) :=
  (rep.2.2.2.2.2.2.2.2 hq).2

theorem persistent_logical_frame {q : Nat} (full : List (Finset (Fin q)))
    (old fresh : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (frame : ∀ physical < base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q),
      fresh (BitVec.ofNat (indexWidth 32 full.length q) physical) = old (BitVec.ofNat (indexWidth 32 full.length q) physical))
    (address : Nat)
    (ha : address < capacityWords 8192 full.length q (treeSize q full) + (2 + (staticMetadata q full).length)) :
    logicalHeap q (capacityWords 8192 full.length q (treeSize q full)) fresh address =
      logicalHeap q (capacityWords 8192 full.length q (treeSize q full)) old address := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have hbase : 4 + packedCapacityWords q capWords bits + (2 + (staticMetadata q full).length) ≤ workspace := by
    dsimp only [workspace]
    rw [base_metadata_end q full hq]
    unfold PSTRStaticHeap.metadataAddress physicalHeaderWords
    omega
  exact PSTRRepairHeap.logical_frame old fresh capWords (2 + (staticMetadata q full).length) workspace address
    (by omega) hq (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide))
    ((show workspace + 3 ≤ workspace + 15 by omega).trans_lt rooms.1) hbase frame ha

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
        logicalHeap q (capacityWords 8192 full.length q (treeSize q full)) state.heap address) := by
  let rom := callInput q full command
  have entry := PSTRArbitraryEntry.of_bootstrap whole cb
  obtain ⟨steps, lower, upper, complete, prefixes⟩ := PSTRCountCompleteOutside.actual_complete full command configuration
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
  refine ⟨steps, lower, upper, ?_, frames, ?_, ?_⟩
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

end PaperProofs.Structure.LaminarTree.PSTRArbitraryOutside
