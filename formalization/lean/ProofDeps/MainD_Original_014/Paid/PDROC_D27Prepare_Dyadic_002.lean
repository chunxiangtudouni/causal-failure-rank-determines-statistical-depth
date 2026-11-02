module

public import Paid.PDROC_D27Prepare_Dyadic_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

namespace PDROC.D27Prepare.Dyadic

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDMenu.ComputeFrame
open Program Memory Tail Resources

/-- Actual page22/23 loop computes the original dyadic2^-N using N
iterations, with all physical prefix bounds and no initial-clock oracle. -/
theorem loop_trace (input : List Cell) (P : Parameters) (fee : ℚ) :
    ∀ fuel i (before : State) (memory : SlotMemory), i + fuel = P.certificate.stages →
      MemoryMatch before memory → before.pc = pc 22 →
      StateBounds 64 (operandBudget P fee) before →
      Has memory 0 (.natural P.certificate.stages) → Has memory 35 (.natural i) →
      Has memory 14 (.natural 1) → Has memory 21 (.rational (1 / 2)) →
      Has memory 39 (.rational ((1 / 2 : ℚ) ^ i)) →
      ∃ (after : State) (finalMemory : SlotMemory) (trace : List State),
        MemoryMatch after finalMemory ∧ Has finalMemory 35 (.natural P.certificate.stages) ∧
        Has finalMemory 39 (.rational ((1 / 2 : ℚ) ^ P.certificate.stages)) ∧
        after.pc = pc 24 ∧ after.output = before.output ∧
        trace.head? = some before ∧ trace.getLast? = some after ∧ trace.length ≤ 29 * fuel + 9 ∧
        trace.IsChain (fun a b => step program input a = some b) ∧
        (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
        ∀ address, address ≠ 35 → address ≠ 39 → ∀ value,
          Has memory address value → Has finalMemory address value := by
  intro fuel
  induction fuel with
  | zero =>
      intro i before memory fits matched location bounded hN hindex _ _ hpower
      have iEqual : i = P.certificate.stages := by omega
      subst i
      obtain ⟨after, trace, afterMatch, afterPc, output, head, last, length, chain, allBounds⟩ :=
        exit_bounded input P fee before memory matched location bounded hN hindex
      refine ⟨after, memory, trace, afterMatch, hindex, hpower, afterPc, output,
        head, last, ?_, chain, allBounds, ?_⟩
      · omega
      · intro address _ _ value old
        exact old
  | succ fuel ih =>
      intro i before memory fits matched location bounded hN hindex hone hhalf hpower
      have inside : i < P.certificate.stages := by omega
      obtain ⟨middle, first, middleMatch, middlePc, firstOutput, firstHead, firstLast,
        firstLength, firstChain, firstBounds⟩ :=
        cycle_bounded input P fee before memory i matched location bounded inside hN hindex hone hhalf hpower
      have middleBound := firstBounds middle (List.mem_of_getLast? firstLast)
      have nextN : Has (dyadicNext memory i) 0 (.natural P.certificate.stages) := by
        apply Has.write_other
        · exact Has.write_other memory 0 35 (.natural P.certificate.stages) (.natural (i + 1)) hN (by decide)
        · decide
      have nextIndex : Has (dyadicNext memory i) 35 (.natural (i + 1)) := by
        apply Has.write_other
        · apply Has.write_same
        · decide
      have nextOne : Has (dyadicNext memory i) 14 (.natural 1) := by
        apply Has.write_other
        · exact Has.write_other memory 14 35 (.natural 1) (.natural (i + 1)) hone (by decide)
        · decide
      have nextHalf : Has (dyadicNext memory i) 21 (.rational (1 / 2)) := by
        apply Has.write_other
        · exact Has.write_other memory 21 35 (.rational (1 / 2)) (.natural (i + 1)) hhalf (by decide)
        · decide
      have nextPower : Has (dyadicNext memory i) 39 (.rational ((1 / 2 : ℚ) ^ (i + 1))) := Has.write_same _ _ _
      obtain ⟨after, finalMemory, later, afterMatch, finalIndex, finalPower, afterPc, laterOutput,
        laterHead, laterLast, laterLength, laterChain, laterBounds, laterPreserves⟩ :=
        ih (i + 1) middle (dyadicNext memory i) (by omega) middleMatch middlePc middleBound
          nextN nextIndex nextOne nextHalf nextPower
      refine ⟨after, finalMemory, joinTrace first later, afterMatch, finalIndex, finalPower, afterPc,
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
      · intro address notIndex notPower value old
        apply laterPreserves address notIndex notPower value
        apply Has.write_other
        · exact Has.write_other memory address 35 value (.natural (i + 1)) old notIndex
        · exact notPower

theorem original_loop_trace (input : List Cell) (P : Parameters) (fee : ℚ)
    (before : State) (memory : SlotMemory) (matched : MemoryMatch before memory)
    (location : before.pc = pc 22) (bounded : StateBounds 64 (operandBudget P fee) before)
    (hN : Has memory 0 (.natural P.certificate.stages)) (hindex : Has memory 35 (.natural 0))
    (hone : Has memory 14 (.natural 1)) (hhalf : Has memory 21 (.rational (1 / 2)))
    (hpower : Has memory 39 (.rational 1)) :
    ∃ (after : State) (finalMemory : SlotMemory) (trace : List State),
      MemoryMatch after finalMemory ∧ Has finalMemory 35 (.natural P.certificate.stages) ∧
      Has finalMemory 39 (.rational ((1 / 2 : ℚ) ^ P.certificate.stages)) ∧
      after.pc = pc 24 ∧ after.output = before.output ∧
      trace.head? = some before ∧ trace.getLast? = some after ∧
      trace.length ≤ 29 * P.certificate.stages + 9 ∧
      trace.IsChain (fun a b => step program input a = some b) ∧
      (∀ state ∈ trace, StateBounds 64 (operandBudget P fee) state) ∧
      ∀ address, address ≠ 35 → address ≠ 39 → ∀ value,
        Has memory address value → Has finalMemory address value := by
  exact loop_trace input P fee P.certificate.stages 0 before memory (by omega) matched location bounded
    hN hindex hone hhalf (by simpa only [pow_zero] using hpower)

end PDROC.D27Prepare.Dyadic
