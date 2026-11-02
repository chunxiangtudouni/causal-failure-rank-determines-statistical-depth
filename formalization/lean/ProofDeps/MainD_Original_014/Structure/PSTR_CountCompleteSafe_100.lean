module

public import Structure.PSTR_CountCompleteOutside_085
public import Structure.PSTR_BootstrapSafe_099
public import Structure.PSTR_IterationsSafe_096

/-! ORIGINAL raw call -> complete counts/parents at ONE witness, with all
prefix physical frames and EVERY proper-clock actual fetch/decode/access. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountCompleteSafe

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims
open AlgorithmClaims.PackedCapacityRAM PSTRQueryLayout PSTRCountWorkspace

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
          result.heap (BitVec.ofNat (indexWidth 32 full.length q) physical) = heap (BitVec.ofNat (indexWidth 32 full.length q) physical)) ∧
      (∀ clock < steps, PSTRCountKernel.AtSafe (callInput q full command) whole
        (endpoint (base q full (capacityWords 8192 full.length q (treeSize q full)) (indexWidth 32 full.length q))
          (prepareNormalization q full).indexed.nodes.size q)
        (packingRun (callInput q full command) whole clock (packingInitial heap))) := by
  let bits := indexWidth 32 full.length q
  let capWords := capacityWords 8192 full.length q (treeSize q full)
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := callInput q full command
  let heapWords := endpoint (base q full capWords bits) size q
  have positiveE : 0 < heapWords := by
    dsimp only [heapWords]
    rw [endpoint_eq]
    omega
  let start := 8 * CapacityBits.width q + 61
  let boot := packingRun rom whole start (packingInitial heap)
  obtain ⟨ready, startPrefixes⟩ := PSTRCountCompleteOutside.ready_zero_prefix full command configuration whole cb co hwords hpcfit hq hl heap rep
  obtain ⟨loopSteps, hloopSteps, last, loopPrefixes, loopFetch⟩ := PSTRIterationsSafe.actual_iterations full command configuration 61
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
  refine ⟨start + (loopSteps + 5), by dsimp only [start]; omega, by dsimp only [start]; omega, ?_, ?_, ?_⟩
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

  · intro clock hclock
    by_cases hstart : clock < start
    · exact PSTRBootstrapSafe.actual_safe full command configuration whole cb co hwords hpcfit hq hl heap rep clock hstart
    · by_cases hloop : clock - start < loopSteps
      · rw [show clock = start + (clock - start) by omega, PSTRWordSegments.run_add]
        exact loopFetch (clock - start) hloop
      · rw [show clock = start + (loopSteps + (clock - (start + loopSteps))) by omega,
          PSTRWordSegments.run_add, PSTRWordSegments.run_add]
        exact PSTRBranchAccess.test_safe rom whole (61 + 5) (61 + 478) heapWords ts hwords hpcfit
          looped lastReady.pc lastReady.active positiveE (clock - (start + loopSteps)) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRCountCompleteSafe
