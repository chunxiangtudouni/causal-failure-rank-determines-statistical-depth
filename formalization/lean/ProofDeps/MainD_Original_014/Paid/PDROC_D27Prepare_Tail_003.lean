module

public import Paid.PDROC_D27Prepare_Tail_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.D27Prepare.Tail

open PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open PDMenu.ComputeFrame
open Program Memory

/-- A complete genuine rejected halving guard, literal update, and jump
back to the guard. The count is29 actual ISA transitions, independent of
the numeric rational ceiling. Prefix witnesses retain both real bodies. -/
theorem halve_cycle_trace (input : List Cell) (before : State) (memory : SlotMemory) (x j : ℕ)
    (matched : MemoryMatch before memory) (location : before.pc = pc 43) (positive : 0 < x)
    (hzero : Has memory 13 (.natural 0)) (hx : Has memory 47 (.natural x))
    (hj : Has memory 10 (.natural j)) (htwo : Has memory 15 (.natural 2))
    (hone : Has memory 14 (.natural 1)) :
    ∃ (guarded after : State) (trace : List State),
      guarded = {comparisonResult before 0 13 47 true with pc := pc 44} ∧
      MemoryMatch guarded memory ∧ MemoryMatch after (halveNext memory x j) ∧
      after.pc = pc 43 ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length = 30 ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      (∀ state ∈ trace, state = guarded ∨ state = after ∨
        (∃ count ≤ 7, linearExecute input ((natCompareSlots .less 13 47).take count) before = some state) ∨
        ∃ count ≤ 20, linearExecute input (budgetHalveStep.take count) guarded = some state) ∧
      ∃ terminal : State, linearExecute input budgetHalveStep guarded = some terminal ∧
        after = {terminal with pc := pc 43} := by
  have comparison : Comparison.less.nat 0 x = true := by simp [Comparison.nat, positive]
  let guarded : State := {comparisonResult before 0 13 47 true with pc := pc 44}
  have guardRun := Search.nat_compare_page_trace input 43 (by decide) before location .less 13 47 45 44 0 x
    rfl matched.base (match_has before memory 13 (.natural 0) matched hzero)
    (match_has before memory 47 (.natural x) matched hx)
  simp only [comparison, ↓reduceIte] at guardRun
  obtain ⟨guardTrace, guardHead, guardLast, guardLength, guardChain,
    guardHeap, guardLive, guardFresh, guardOutput, guardPrefix⟩ := guardRun
  have guardMatch : MemoryMatch guarded memory :=
    ⟨guardHeap.trans matched.heap, guardLive.trans matched.live, guardFresh.trans matched.base⟩
  obtain ⟨after, updateTrace, afterMatch, afterPc, updateOutput,
    updateHead, updateLast, updateLength, updateChain, updatePrefix, terminal⟩ :=
    halve_update_trace input guarded memory x j guardMatch rfl hx hj htwo hone
  let trace := joinTrace guardTrace updateTrace
  have head := joinTrace_head guardTrace updateTrace before guarded guardHead guardLast updateHead
  have last := joinTrace_last guardTrace updateTrace after updateLast
  have chain := joinTrace_chain program input guardTrace updateTrace guarded guardChain updateChain guardLast updateHead
  have length : trace.length = 30 := by
    simp only [trace, joinTrace, List.length_append, List.length_dropLast, guardLength, updateLength]
  refine ⟨guarded, after, trace, rfl, guardMatch, afterMatch, afterPc,
    updateOutput.trans guardOutput, head, last, length, chain, ?_, terminal⟩
  intro state member
  rcases List.mem_append.mp member with early | late
  · have memberGuard := List.mem_of_mem_dropLast early
    rcases guardPrefix state memberGuard with same | prefixRun
    · exact Or.inl same
    · exact Or.inr (Or.inr (Or.inl prefixRun))
  · rcases updatePrefix state late with same | prefixRun
    · exact Or.inr (Or.inl same)
    · exact Or.inr (Or.inr (Or.inr prefixRun))

end PDROC.D27Prepare.Tail
