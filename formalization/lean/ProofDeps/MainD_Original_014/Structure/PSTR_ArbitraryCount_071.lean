module

public import Structure.PSTR_CountComplete_066
public import Structure.PSTR_ArbitraryEntry_060

/-! A real heads tail jumps to ACTIVE pc0 with arbitrary registers. The
count producer executes the same first14 overwriting instructions and is
transported at its SAME total clock, including those actual instructions.
No reset or second uncharged helper execution is introduced. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRArbitraryCount

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

theorem actual_complete_late {q : Nat} (full : List (Finset (Fin q))) (command : Command)
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
        (packingRun (callInput q full command) whole steps (packingInitial heap)) := by
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := callInput q full command
  let boot := packingRun rom whole (8 * CapacityBits.width q + 61) (packingInitial heap)
  have start := PSTRCountComplete.ready_zero_in full command configuration whole cb co hwords hpcfit hq hl heap rep
  obtain ⟨loopSteps, hloopSteps, last⟩ := PSTRCountIteration.actual_iterations full command configuration 61 whole co
    hwords hpcfit hq hl size 0 boot (by omega) start
  have bound : loopSteps ≤ 387 * size + 114 * PSTRStaticLayout.edgeCount q full := by
    simpa only [size, PSTRCountChildRows.offset_zero, PSTRCountChildRows.offset_end,
      Nat.mul_zero, Nat.add_zero, Nat.zero_add] using hloopSteps
  have he := PSTRStaticLayout.edgeCount_eq q full hq hl
  have he_le : PSTRStaticLayout.edgeCount q full ≤ size := by rw [he]; exact Nat.sub_le _ _
  have ending := PSTRCountComplete.finish_from_ready full command configuration 61 whole co hwords hpcfit hq
    (packingRun rom whole loopSteps boot) (by simpa only [Nat.zero_add] using last)
  refine ⟨(8 * CapacityBits.width q + 61) + (loopSteps + 5), by omega, by omega, ?_⟩
  rw [PSTRWordSegments.run_add, PSTRWordSegments.run_add]
  exact ending

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
        (packingRun (callInput q full command) whole steps state) := by
  obtain ⟨steps, lower, upper, complete⟩ := actual_complete_late full command configuration whole cb co
    hwords hpcfit hq hl state.heap rep
  refine ⟨steps, lower, upper, ?_⟩
  rw [PSTRArbitraryEntry.run_from_arbitrary (callInput q full command) whole
    (PSTRArbitraryEntry.of_bootstrap whole cb) hwords hpcfit state hp ha steps (by omega)]
  exact complete

theorem entry_trace_bound {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (state : WordState bits) :
    (packingDynamicTrace rom whole 14 state).length ≤ 168 :=
  packingDynamicTrace_length_le rom whole 14 state

end PaperProofs.Structure.LaminarTree.PSTRArbitraryCount
