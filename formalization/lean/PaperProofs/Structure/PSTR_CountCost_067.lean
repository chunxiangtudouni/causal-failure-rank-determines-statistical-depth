module

public import PaperProofs.Structure.PSTR_CountComplete_066
public import PaperProofs.Structure.PSTR_WidthOriginal_037

/-! Original charged execution cost for the actual positive count body,
including its one real final HALT. This is not full CallClaims: all-clock
DynamicRunCorrect and the true query reply/tail remain separate duties. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRCountCost

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine CompactControllerClaims

theorem active_bound_work {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q) :
    8 * CapacityBits.width q + 66 + 501 * (prepareNormalization q full).indexed.nodes.size ≤
      575 * liveWork q (treeSize q full) := by
  have ht : 0 < (prepareNormalization q full).indexed.nodes.size := by
    simpa only [treeSize, ne_of_gt hq, ite_false] using PSTRWidthOriginal.positive_tree_size full hq
  have hw : CapacityBits.width q ≤ q + 1 :=
    Nat.clog_le_of_le_pow (Nat.le_of_lt (Nat.lt_pow_self (by decide)))
  have hqwork : q + 1 ≤ (q + 1) * (prepareNormalization q full).indexed.nodes.size :=
    Nat.le_mul_of_pos_right _ ht
  have htwork : (prepareNormalization q full).indexed.nodes.size ≤
      (q + 1) * (prepareNormalization q full).indexed.nodes.size := by
    have h := Nat.mul_le_mul_right (prepareNormalization q full).indexed.nodes.size (show 1 ≤ q + 1 by omega)
    simpa only [one_mul] using h
  simp only [liveWork, ne_of_gt hq, ite_false, queryWork, treeSize]
  omega

theorem actual_halted_counts {q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (configuration : Configuration q) (hq : 0 < q) (hl : LaminarSchedule full)
    (heap : BitVec (indexWidth 32 full.length q) → BitVec (indexWidth 32 full.length q))
    (rep : HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration heap) :
    ∃ steps,
      let before := packingRun (callInput q full command) PSTRCountProgram.program steps (packingInitial heap)
      PSTRCountComplete.Complete full configuration 61 (capacityWords 8192 full.length q (treeSize q full)) before ∧
      let after := packingRun (callInput q full command) PSTRCountProgram.program (steps + 1) (packingInitial heap)
      after.halted = true ∧ after.heap = before.heap ∧
      HeapRepresents q full (capacityWords 8192 full.length q (treeSize q full)) configuration after.heap ∧
      callCost q full PSTRCountProgram.program command (steps + 1) heap ≤ 10000 * liveWork q (treeSize q full) := by
  let bits := indexWidth 32 full.length q
  let rom := callInput q full command
  have hb := PSTROriginalCountRoom.word_lower full.length q
  have hwords := PSTRCountProgram.code_fit (bits := bits) (by omega)
  have hpcfit := PSTRCountProgram.pc_fit (bits := bits) (by omega)
  obtain ⟨steps, hsteps, complete⟩ := PSTRCountComplete.actual_complete full command configuration PSTRCountProgram.program
    PSTRCountProgram.bootstrap_contains PSTRCountProgram.outer_contains hwords hpcfit hq hl heap rep
  let before := packingRun rom PSTRCountProgram.program steps (packingInitial heap)
  have hp : before.pc = BitVec.ofNat bits (5 * PSTRCountProgram.program.length) := by
    rw [PSTRCountProgram.program_length]
    exact complete.pc
  have halt := PSTRCountKernel.halt_at_exit rom PSTRCountProgram.program steps (packingInitial heap) hwords hpcfit
    complete.active hp
  have halted : (packingRun rom PSTRCountProgram.program (steps + 1) (packingInitial heap)).halted = true :=
    congrArg WordState.halted halt
  have heap_eq : (packingRun rom PSTRCountProgram.program (steps + 1) (packingInitial heap)).heap = before.heap := by
    have hh := congrArg (fun state : WordState bits => state.heap) halt
    exact hh
  refine ⟨steps, complete, halted, heap_eq, ?_, ?_⟩
  · rw [heap_eq]
    exact complete.rep
  · have hs := hsteps.trans (active_bound_work full hq)
    have trace := packingDynamicTrace_length_le (callInput q full command) PSTRCountProgram.program (steps + 1) (packingInitial heap)
    have hwork : 1 ≤ liveWork q (treeSize q full) := by
      have ht := PSTRWidthOriginal.positive_tree_size full hq
      simp only [liveWork, ne_of_gt hq, ite_false, queryWork]
      exact Nat.succ_le_of_lt (Nat.mul_pos (Nat.succ_pos _) ht)
    unfold callCost
    rw [PSTRCountProgram.code_length]
    omega

end PaperProofs.Structure.LaminarTree.PSTRCountCost
