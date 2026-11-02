module

public import Paid.PDROC_D27Prepare_TailBounds_001
public import Paid.PDROC_D27Prepare_Tail_003
public import Paid.PDROC_D27Prepare_Resources_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.D27Prepare.TailBounds

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute (linearExecute)
open Program Memory Tail Resources

/-- An actual29-transition binary loop cycle, with every actual register,
live heap value and output bounded by the same uniform operand envelope. -/
theorem halve_cycle_bounded (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (memory : SlotMemory) (x j : ℕ)
    (matched : MemoryMatch before memory) (location : before.pc = pc 43)
    (bounded : StateBounds 64 (operandBudget P fee) before)
    (positive : 0 < x) (hx : x ≤ ⌈Budget.originalRatio P fee⌉₊)
    (hj : j ≤ P.bisectionBudget fee)
    (hzero : Has memory 13 (.natural 0)) (hvalue : Has memory 47 (.natural x))
    (hcounter : Has memory 10 (.natural j)) (htwo : Has memory 15 (.natural 2))
    (hone : Has memory 14 (.natural 1)) :
    ∃ (after : State) (trace : List State), MemoryMatch after (halveNext memory x j) ∧
      after.pc = pc 43 ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length = 30 ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      ∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state := by
  obtain ⟨guarded, after, trace, guardedEq, guardedMatch, afterMatch, afterPc, output,
    head, last, length, chain, covered, terminal, terminalExecute, afterEq⟩ :=
    halve_cycle_trace input before memory x j matched location positive hzero hvalue hcounter htwo hone
  have zeroSlot := match_has before memory 13 (.natural 0) matched hzero
  have valueSlot := match_has before memory 47 (.natural x) matched hvalue
  have addressBits := address_bits P fee
  have enough : 2 ≤ operandBudget P fee := by
    have : 8 ≤ operandBudget P fee := by
      simpa only [natBits, show Nat.log2 64 = 6 by decide] using addressBits
    omega
  have guardBounds := natCompareSlots_prefix_bounds input before 13 47 64 (operandBudget P fee)
    .less 0 x bounded matched.base zeroSlot.1 valueSlot.1 zeroSlot.2 valueSlot.2
    (by decide) (by decide) addressBits enough
  have comparison : Comparison.less.nat 0 x = true := by simp [Comparison.nat, positive]
  have guardExecute : linearExecute input (natCompareSlots .less 13 47) before =
      some (comparisonResult before 0 13 47 true) := by
    simpa only [comparison] using natCompareSlots_execute input before 0 13 47 0 x .less
      matched.base (by simpa using zeroSlot.1) (by simpa using valueSlot.1)
      (by simpa using zeroSlot.2) (by simpa using valueSlot.2)
  have guardedBound : StateBounds 64 (operandBudget P fee) guarded := by
    rw [guardedEq]
    exact (guardBounds.final guardExecute).with_pc (pc 44)
  have semantic := halve_semantic_bounds P fee memory x j
    (memory_of_state guarded memory 64 (operandBudget P fee) guardedMatch guardedBound)
    hx hj hvalue hcounter htwo hone
  have addresses : ∀ command ∈ budgetHalveStepCommands, CommandAddresses 64 command := by
    intro command member
    simp only [budgetHalveStepCommands, List.mem_cons, List.not_mem_nil, or_false] at member
    rcases member with rfl | rfl <;> norm_num [CommandAddresses]
  have bodyBounds := slotSequence_prefix_bounds budgetHalveStepCommands input guarded memory
    (halveNext memory x j) 64 (operandBudget P fee) guardedMatch guardedBound addresses addressBits
    (halve_body_eval memory x j hvalue hcounter htwo hone) semantic
  rw [budgetHalveStep_compiled] at bodyBounds
  have afterBound : StateBounds 64 (operandBudget P fee) after := by
    rw [afterEq]
    exact (bodyBounds.final terminalExecute).with_pc (pc 43)
  refine ⟨after, trace, afterMatch, afterPc, output, head, last, length, chain, ?_⟩
  intro state member
  rcases covered state member with same | same | guardPrefix | bodyPrefix
  · simpa only [same] using guardedBound
  · simpa only [same] using afterBound
  · obtain ⟨count, _, executed⟩ := guardPrefix
    exact guardBounds count state executed
  · obtain ⟨count, _, executed⟩ := bodyPrefix
    exact bodyBounds count state executed

theorem halve_exit_bounded (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (memory : SlotMemory)
    (matched : MemoryMatch before memory) (location : before.pc = pc 43)
    (bounded : StateBounds 64 (operandBudget P fee) before)
    (hzero : Has memory 13 (.natural 0)) (hvalue : Has memory 47 (.natural 0)) :
    ∃ (after : State) (trace : List State), MemoryMatch after memory ∧
      after.pc = pc 45 ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length = 9 ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      ∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state := by
  have zeroSlot := match_has before memory 13 (.natural 0) matched hzero
  have valueSlot := match_has before memory 47 (.natural 0) matched hvalue
  let terminal := comparisonResult before 0 13 47 false
  let after : State := {terminal with pc := pc 45}
  have comparison : Comparison.less.nat 0 0 = false := by decide
  have run := Search.nat_compare_page_trace input 43 (by decide) before location .less 13 47 45 44 0 0
    rfl matched.base zeroSlot valueSlot
  simp [comparison] at run
  obtain ⟨trace, head, last, length, chain, heap, live, fresh, output, prefixes⟩ := run
  have addressBits := address_bits P fee
  have enough : 2 ≤ operandBudget P fee := by
    have : 8 ≤ operandBudget P fee := by
      simpa only [natBits, show Nat.log2 64 = 6 by decide] using addressBits
    omega
  have guardBounds := natCompareSlots_prefix_bounds input before 13 47 64 (operandBudget P fee)
    .less 0 0 bounded matched.base zeroSlot.1 valueSlot.1 zeroSlot.2 valueSlot.2
    (by decide) (by decide) addressBits enough
  have executed : linearExecute input (natCompareSlots .less 13 47) before = some terminal := by
    simpa only [terminal, comparison] using natCompareSlots_execute input before 0 13 47 0 0 .less
      matched.base (by simpa using zeroSlot.1) (by simpa using valueSlot.1)
      (by simpa using zeroSlot.2) (by simpa using valueSlot.2)
  have afterBound : StateBounds 64 (operandBudget P fee) after :=
    (guardBounds.final executed).with_pc (pc 45)
  refine ⟨after, trace, ⟨heap.trans matched.heap, live.trans matched.live, fresh.trans matched.base⟩,
    rfl, output, head, last, length, chain, ?_⟩
  intro state member
  rcases prefixes state member with same | prefixRun
  · simpa [same, after, terminal] using afterBound
  · obtain ⟨count, _, actual⟩ := prefixRun
    exact guardBounds count state actual

end PDROC.D27Prepare.TailBounds
