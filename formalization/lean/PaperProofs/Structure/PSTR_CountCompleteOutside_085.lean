module

public import PaperProofs.Structure.PSTR_BootstrapOutside_084
public import PaperProofs.Structure.PSTR_IterationsOutside_083

/-! Original raw call -> actual complete physical count/parent data, with
EVERY clock preserving original HeapRep and the exclusive heads suffix.
The same witness supplies final data, clock bound and every prefix. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountCompleteOutside

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace

theorem ready_zero_prefix {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp)
    (cb : PSTRBootstrapSlices.Contains whole) (co : PSTROuterCountCode.Contains whole 61)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration heap) :
    PSTRCountReady.Ready full configuration 61 (capacityWords 8192 full.length q (treeSize q full)) 0
      (packingRun (callInput q full command) whole (8 * CapacityBits.width q + 61) (packingInitial heap)) ∧
    (∀ clock ≤ 8 * CapacityBits.width q + 61,
      let result := packingRun (callInput q full command) whole clock (packingInitial heap)
      HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
      ∀ physical, Fits (indexWidth 32 full.length q) physical →
        (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
          (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
        result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) = heap (BitVec.ofNat (indexWidth 32 full.length q) physical)) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let workspace := base q full capWords bits
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := callInput q full command
  let boot := packingRun rom whole (8 * CapacityBits.width q + 56) (packingInitial heap)
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have raw := PSTROriginalCountRoom.raw_rooms full.length q
  have rooms := PSTROriginalCountRoom.workspace_rooms full 8192 8192 (by decide) (by decide) (by decide) hq hl
  have bootPrefixes (clock : Nat) (hc : clock ≤ 8 * CapacityBits.width q + 56) :=
    PSTRBootstrapOutside.actual_prefix whole cb hwords hpcfit full command configuration capWords heap (by omega) hq rep
      raw.1 raw.2.1 raw.2.2 rooms.1 (PSTROriginalCountRoom.bitmap_room full 8192 hq)
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) clock hc
  have data := PSTRBootstrapIn.actual_bootstrap whole cb hwords hpcfit full command configuration capWords heap
    (by omega) hq rep raw.1 raw.2.1 raw.2.2 rooms.1
  have boot_rep : HeapRepresents q full capWords configuration boot.heap := (bootPrefixes _ le_rfl).1
  have hbase : boot.register .old = BitVec.ofNat bits (countsBase workspace) := data.2.2.1
  have ht : boot.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using
      (PSTRStaticHeap.headers full configuration capWords boot.heap boot_rep).1
  have hroom : Fits bits (parentsBase workspace size) := (Nat.le_add_right _ size).trans_lt rooms.2
  have hpRoom : Fits bits (parentsBase workspace (treeSize q full)) := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using hroom
  have hs := PSTROuterCountCode.sentinel_at whole 61 co
  have high_base (physical : Nat) (hh : physical < workspace ∨ endpoint workspace size q ≤ physical) :
      physical < workspace ∨ workspace + 16 ≤ physical := by
    rcases hh with low | high
    · exact Or.inl low
    · right
      rw [endpoint_eq] at high
      omega
  refine ⟨PSTRCountComplete.ready_zero_in full command configuration whole cb co hwords hpcfit hq hl heap rep, ?_⟩
  intro clock hclock
  dsimp only
  by_cases hboot : clock ≤ 8 * CapacityBits.width q + 56
  · have hp := bootPrefixes clock hboot
    exact ⟨hp.1, fun physical hf hh => hp.2 physical hf (high_base physical hh)⟩
  · rw [show clock = (8 * CapacityBits.width q + 56) + (clock - (8 * CapacityBits.width q + 56)) by omega,
      PSTRWordSegments.run_add,
      PSTRWidthPrefix.straight_prefix rom whole PSTRParentSentinel.program 61 hs.bound hs.code
        PSTRParentSentinel.program_straight hwords hpcfit boot data.2.1 data.1
        (clock - (8 * CapacityBits.width q + 56)) (by rw [PSTRParentSentinel.program_length]; omega)]
    refine ⟨PSTROuterMemory.sentinel_prefix_rep full rom configuration capWords boot (by omega) hq boot_rep
      (PSTROriginalCountRoom.bitmap_room full 8192 hq)
      (PA17A19QueryBridgeNumeric006b.scalar_room full 8192 (by decide)) hpRoom hbase
      (clock - (8 * CapacityBits.width q + 56)) (by omega), ?_⟩
    intro physical hf hh
    have different : BitVec.ofNat bits physical ≠ BitVec.ofNat bits (parentsBase workspace size) := by
      apply (ofNat_injective_of_fit _ _ hf hroom).not.mpr
      change physical < workspace ∨ endpoint workspace size q ≤ physical at hh
      rcases hh with low | high
      · change physical ≠ workspace + 16 + size
        omega
      · rw [endpoint_eq] at high
        change physical ≠ workspace + 16 + size
        omega
    exact (PSTROuterStoreFrame.sentinel_prefix_outside rom workspace size boot hbase ht _ different
      (clock - (8 * CapacityBits.width q + 56)) (by omega)).trans
        ((bootPrefixes (8 * CapacityBits.width q + 56) le_rfl).2 physical hf (high_base physical hh))

theorem actual_complete {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (whole : List PackingOp)
    (cb : PSTRBootstrapSlices.Contains whole) (co : PSTROuterCountCode.Contains whole 61)
    (hwords : WordsFit (indexWidth 32 full.length q) (packingCode whole))
    (hpcfit : Fits (indexWidth 32 full.length q) (5 * whole.length))
    (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration heap) :
    ∃ steps, 66 ≤ steps ∧
      steps ≤ 8 * CapacityBits.width q + 66 + 501 * (prepareNormalization q full).indexed.nodes.size ∧
      PSTRCountComplete.Complete full configuration 61 (capacityWords 8192 full.length q (treeSize q full))
        (packingRun (callInput q full command) whole steps (packingInitial heap)) ∧
      (∀ clock ≤ steps,
        let result := packingRun (callInput q full command) whole clock (packingInitial heap)
        HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration result.heap ∧
        ∀ physical, Fits (indexWidth 32 full.length q) physical →
          (physical < (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) ∨ endpoint (base q full (capacityWords 8192 full.length q (treeSize q full))
            (indexWidth 32 full.length q)) (prepareNormalization q full).indexed.nodes.size q ≤ physical) →
          result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) = heap (BitVec.ofNat (indexWidth 32 full.length q) physical)) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := callInput q full command
  let start := 8 * CapacityBits.width q + 61
  let boot := packingRun rom whole start (packingInitial heap)
  obtain ⟨ready, startPrefixes⟩ := ready_zero_prefix full command configuration whole cb co hwords hpcfit hq hl heap rep
  obtain ⟨loopSteps, hloopSteps, last, loopPrefixes⟩ := PSTRIterationsOutside.actual_iterations full command configuration 61
    whole co hwords hpcfit hq hl size 0 boot (by omega) ready
  have bound : loopSteps ≤ 387 * size + 114 * PSTRStaticLayout.edgeCount q full := by
    simpa only [size, PSTRCountChildRows.offset_zero, PSTRCountChildRows.offset_end,
      Nat.mul_zero, Nat.add_zero, Nat.zero_add] using hloopSteps
  have he := PSTRStaticLayout.edgeCount_eq q full hq hl
  have he_le : PSTRStaticLayout.edgeCount q full ≤ size := by rw [he]; exact Nat.sub_le _ _
  let looped := packingRun rom whole loopSteps boot
  have lastReady : PSTRCountReady.Ready full configuration 61 capWords size looped := by
    simpa only [Nat.zero_add] using last
  have ending := PSTRCountComplete.finish_from_ready full command configuration 61 whole co hwords hpcfit hq looped lastReady
  have ts := PSTROuterCountCode.test_at whole 61 co
  refine ⟨start + (loopSteps + 5), by dsimp only [start]; omega, by dsimp only [start]; omega, ?_, ?_⟩
  · rw [PSTRWordSegments.run_add, PSTRWordSegments.run_add]
    exact ending
  · intro clock hclock
    dsimp only
    by_cases hstart : clock ≤ start
    · exact startPrefixes clock hstart
    · by_cases hloop : clock - start ≤ loopSteps
      · rw [show clock = start + (clock - start) by omega, PSTRWordSegments.run_add]
        have p := loopPrefixes (clock - start) hloop
        refine ⟨p.1, ?_⟩
        intro physical hp hh
        exact (p.2 physical hp hh).trans ((startPrefixes start le_rfl).2 physical hp hh)
      · rw [show clock = start + (loopSteps + (clock - (start + loopSteps))) by omega,
          PSTRWordSegments.run_add, PSTRWordSegments.run_add,
          PSTRLeafCountPrefix.test_prefix_run rom whole (61 + 5) (61 + 478) ts.bound ts.code hwords hpcfit
            looped lastReady.pc lastReady.active (clock - (start + loopSteps)) (by omega),
          PSTRLeafCountPrefix.test_prefix_heap rom (61 + 478) looped (clock - (start + loopSteps)) (by omega)]
        refine ⟨lastReady.rep, ?_⟩
        intro physical hp hh
        exact ((loopPrefixes loopSteps le_rfl).2 physical hp hh).trans
          ((startPrefixes start le_rfl).2 physical hp hh)

end PaperProofs.Structure.LaminarTree.PSTRCountCompleteOutside
