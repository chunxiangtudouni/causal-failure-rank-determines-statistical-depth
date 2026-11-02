module

public import Paid.PDROC_D27Prepare_Tail_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Tail

theorem binomial_exit_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (matched : MemoryMatch before memory)
    (location : before.pc=pc 27) (bounded : StateBounds 64 (operandBudget P fee) before)
    (data : BinomialData P memory (P.certificate.stages+1)) :
    ∃ after : State,MemoryMatch after memory ∧ after.pc=pc 31 ∧
      Segment binomialRegion input before after 64 (operandBudget P fee) 9 := by
  have addressBits := operandBudget_address_bits P fee
  have enough : 2≤operandBudget P fee := by
    have address : 1+natBits 64=8 := by decide
    omega
  obtain ⟨after,afterPc,afterHeap,afterLive,segment⟩ :=
    Q.nat_compare_segment binomialRegion input 27 (by decide) before location .lessEqual
      40 0 31 28 (P.certificate.stages+1) P.certificate.stages rfl matched.base
      (match_has before memory 40 _ matched data.index)
      (match_has before memory 0 _ matched data.stages) _ bounded addressBits
      (by decide) (by decide) enough
  have comparison : Comparison.lessEqual.nat (P.certificate.stages+1) P.certificate.stages=false := by
    simp [Comparison.nat]
  simp only [comparison] at afterPc
  exact ⟨after,⟨afterHeap.trans matched.heap,afterLive.trans matched.live,
    segment.fresh.trans matched.base⟩,afterPc,segment⟩

/-- N+1 actual iterations, independent of the numerical value of K.
The base case executes the final guard; no precomputed tail is supplied. -/
theorem binomial_loop_segment (P : Parameters) (fee : ℚ) (input : List Cell) :
    ∀ fuel i (before : State) (memory : SlotMemory),i+fuel=P.certificate.stages+1 →
      MemoryMatch before memory → before.pc=pc 27 →
      StateBounds 64 (operandBudget P fee) before → BinomialData P memory i →
      ∃ (after : State) (finalMemory : SlotMemory),MemoryMatch after finalMemory ∧
        BinomialData P finalMemory (P.certificate.stages+1) ∧ after.pc=pc 31 ∧
        Segment binomialRegion input before after 64 (operandBudget P fee) (92*fuel+9) := by
  intro fuel
  induction fuel with
  | zero =>
    intro i before memory fits matched location bounded data
    have equal : i=P.certificate.stages+1 := by omega
    subst i
    obtain ⟨after,afterMatch,afterPc,segment⟩ :=
      binomial_exit_segment P fee input before memory matched location bounded data
    exact ⟨after,memory,afterMatch,data,afterPc,by simpa using segment⟩
  | succ fuel ih =>
    intro i before memory fits matched location bounded data
    have index : i≤P.certificate.stages := by omega
    obtain ⟨middle,middleMatch,middlePc,first⟩ :=
      binomial_cycle_segment P fee input before memory i matched location bounded index data
    obtain ⟨after,finalMemory,afterMatch,afterData,afterPc,later⟩ :=
      ih (i+1) middle (binomialCycleMemory P memory i) (by omega) middleMatch middlePc
        first.final_bounds (binomial_cycle_data P memory i data)
    exact ⟨after,finalMemory,afterMatch,afterData,afterPc,
      (first.trans later).weaken_budget (by omega)⟩

end PDROC.D27Prepare.Tail
