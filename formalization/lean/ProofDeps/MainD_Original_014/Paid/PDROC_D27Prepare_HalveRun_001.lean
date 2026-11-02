module

public import Paid.PDROC_D27Prepare_TailBounds_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.D27Prepare.HalveRun

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open Program Memory Tail TailBounds Resources

/-- Complete actual binary halving loop. Fuel is the mathematical clog
potential, never the numeric value of the possibly enormous ceiling.
All original slots except47/10 are preserved, and every actual state has
the same operand envelope. No successful loop is a caller premise. -/
theorem loop_trace (input : List Cell) (P : Parameters) (fee : ℚ) :
    ∀ fuel x j (before : State) (memory : SlotMemory),
      Budget.remaining x = fuel →
      MemoryMatch before memory → before.pc = pc 43 →
      StateBounds 64 (operandBudget P fee) before →
      x ≤ ⌈Budget.originalRatio P fee⌉₊ →
      j + Budget.remaining x = P.bisectionBudget fee →
      Has memory 13 (.natural 0) → Has memory 47 (.natural x) →
      Has memory 10 (.natural j) → Has memory 15 (.natural 2) → Has memory 14 (.natural 1) →
      ∃ (after : State) (finalMemory : SlotMemory) (trace : List State),
        MemoryMatch after finalMemory ∧ Has finalMemory 10 (.natural (P.bisectionBudget fee)) ∧
        after.pc = pc 45 ∧ after.output = before.output ∧
        trace.head? = some before ∧ trace.getLast? = some after ∧
        trace.length ≤ 29 * fuel + 9 ∧
        trace.IsChain (fun a b => step program input a = some b) ∧
        (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
        ∀ address, address ≠ 47 → address ≠ 10 → ∀ value,
          Has memory address value → Has finalMemory address value := by
  intro fuel
  induction fuel with
  | zero =>
      intro x j before memory potential matched location bounded _ target hzero hvalue hcounter _ _
      have xZero : x = 0 := by
        by_contra different
        have positive := Budget.remaining_pos x (Nat.pos_of_ne_zero different)
        omega
      subst x
      have jEqual : j = P.bisectionBudget fee := Budget.finished_value j _ target
      obtain ⟨after, trace, afterMatch, afterPc, output, head, last, length, chain, allBounds⟩ :=
        halve_exit_bounded input P fee before memory matched location bounded hzero hvalue
      refine ⟨after, memory, trace, afterMatch, ?_, afterPc, output, head, last, ?_, chain, allBounds, ?_⟩
      · simpa only [jEqual] using hcounter
      · omega
      · intro address _ _ value old
        exact old
  | succ fuel ih =>
      intro x j before memory potential matched location bounded ceiling target hzero hvalue hcounter htwo hone
      have positive : 0 < x := by
        by_contra nonpositive
        have xZero : x = 0 := by omega
        subst x
        rw [Budget.remaining_zero] at potential
        omega
      have counterBound : j ≤ P.bisectionBudget fee := by omega
      obtain ⟨middle, first, middleMatch, middlePc, firstOutput, firstHead, firstLast,
        firstLength, firstChain, firstBounds⟩ :=
        halve_cycle_bounded input P fee before memory x j matched location bounded positive
          ceiling counterBound hzero hvalue hcounter htwo hone
      have middleBound := firstBounds middle (List.mem_of_getLast? firstLast)
      have nextPotential : Budget.remaining (x / 2) = fuel := by
        have decreased := Budget.remaining_step x positive
        omega
      have nextCeiling : x / 2 ≤ ⌈Budget.originalRatio P fee⌉₊ :=
        (Nat.div_le_self x 2).trans ceiling
      have nextTarget : j + 1 + Budget.remaining (x / 2) = P.bisectionBudget fee :=
        Budget.iteration_invariant j x _ positive target
      have nextZero : Has (halveNext memory x j) 13 (.natural 0) := by
        apply Has.write_other
        · exact Has.write_other memory 13 47 (.natural 0) (.natural (x / 2)) hzero (by decide)
        · decide
      have nextValue : Has (halveNext memory x j) 47 (.natural (x / 2)) := by
        apply Has.write_other
        · apply Has.write_same
        · decide
      have nextCounter : Has (halveNext memory x j) 10 (.natural (j + 1)) := Has.write_same _ _ _
      have nextTwo : Has (halveNext memory x j) 15 (.natural 2) := by
        apply Has.write_other
        · exact Has.write_other memory 15 47 (.natural 2) (.natural (x / 2)) htwo (by decide)
        · decide
      have nextOne : Has (halveNext memory x j) 14 (.natural 1) := by
        apply Has.write_other
        · exact Has.write_other memory 14 47 (.natural 1) (.natural (x / 2)) hone (by decide)
        · decide
      obtain ⟨after, finalMemory, later, afterMatch, finalCounter, afterPc, laterOutput,
        laterHead, laterLast, laterLength, laterChain, laterBounds, laterPreserves⟩ :=
        ih (x / 2) (j + 1) middle (halveNext memory x j) nextPotential middleMatch middlePc
          middleBound nextCeiling nextTarget nextZero nextValue nextCounter nextTwo nextOne
      refine ⟨after, finalMemory, joinTrace first later, afterMatch, finalCounter, afterPc,
        laterOutput.trans firstOutput,
        joinTrace_head first later before middle firstHead firstLast laterHead,
        joinTrace_last first later after laterLast, ?_,
        joinTrace_chain program input first later middle firstChain laterChain firstLast laterHead, ?_, ?_⟩
      · simp only [joinTrace, List.length_append, List.length_dropLast, firstLength]
        rw [Nat.mul_succ]
        omega
      · intro state member
        rcases List.mem_append.mp member with early | late
        · exact firstBounds state (List.mem_of_mem_dropLast early)
        · exact laterBounds state late
      · intro address notValue notCounter value old
        apply laterPreserves address notValue notCounter value
        apply Has.write_other
        · exact Has.write_other memory address 47 value (.natural (x / 2)) old notValue
        · exact notCounter

theorem original_loop_trace (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (memory : SlotMemory)
    (matched : MemoryMatch before memory) (location : before.pc = pc 43)
    (bounded : StateBounds 64 (operandBudget P fee) before)
    (hzero : Has memory 13 (.natural 0))
    (hvalue : Has memory 47 (.natural (⌈Budget.originalRatio P fee⌉₊ - 1)))
    (hcounter : Has memory 10 (.natural 0)) (htwo : Has memory 15 (.natural 2))
    (hone : Has memory 14 (.natural 1)) :
    ∃ (after : State) (finalMemory : SlotMemory) (trace : List State),
      MemoryMatch after finalMemory ∧ Has finalMemory 10 (.natural (P.bisectionBudget fee)) ∧
      after.pc = pc 45 ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length ≤ 29 * P.bisectionBudget fee + 9 ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      ∀ address, address ≠ 47 → address ≠ 10 → ∀ value,
        Has memory address value → Has finalMemory address value := by
  have potential : Budget.remaining (⌈Budget.originalRatio P fee⌉₊ - 1) = P.bisectionBudget fee := by
    change Budget.remaining (⌈Budget.originalRatio P fee⌉₊ - 1) = Nat.clog 2 ⌈Budget.originalRatio P fee⌉₊
    exact Budget.remaining_start _
  exact loop_trace input P fee (P.bisectionBudget fee) (⌈Budget.originalRatio P fee⌉₊ - 1) 0 before memory
    potential matched location bounded (Nat.sub_le _ _) (by simpa only [Nat.zero_add] using potential)
    hzero hvalue hcounter htwo hone

end PDROC.D27Prepare.HalveRun
