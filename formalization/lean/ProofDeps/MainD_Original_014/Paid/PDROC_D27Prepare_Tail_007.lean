module

public import Paid.PDROC_D27Prepare_Tail_006
public import Paid.PDROC_D27Prepare_Q_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Memory PDROC.D27Prepare.Resources
open PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.Tail

theorem binomial_guard_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (i : ℕ) (matched : MemoryMatch before memory)
    (location : before.pc=pc 27) (bounded : StateBounds 64 (operandBudget P fee) before)
    (index : i≤P.certificate.stages) (data : BinomialData P memory i) :
    ∃ after : State,MemoryMatch after memory ∧
      after.pc=(if Comparison.less.nat P.tools i then pc 29 else pc 30) ∧
      Segment binomialRegion input before after 64 (operandBudget P fee) 18 := by
  have addressBits := operandBudget_address_bits P fee
  have enough : 2≤operandBudget P fee := by
    have address : 1+natBits 64=8 := by decide
    omega
  obtain ⟨outer,outerPc,outerHeap,outerLive,outerSegment⟩ :=
    Q.nat_compare_segment binomialRegion input 27 (by decide) before location .lessEqual
      40 0 31 28 i P.certificate.stages rfl matched.base
      (match_has before memory 40 _ matched data.index)
      (match_has before memory 0 _ matched data.stages) _ bounded addressBits
      (by decide) (by decide) enough
  have comparison : Comparison.lessEqual.nat i P.certificate.stages=true := by
    simp [Comparison.nat,index]
  simp only [comparison,↓reduceIte] at outerPc
  have outerMatch : MemoryMatch outer memory :=
    ⟨outerHeap.trans matched.heap,outerLive.trans matched.live,outerSegment.fresh.trans matched.base⟩
  obtain ⟨after,afterPc,afterHeap,afterLive,innerSegment⟩ :=
    Q.nat_compare_segment binomialRegion input 28 (by decide) outer outerPc .less
      1 40 30 29 P.tools i rfl outerMatch.base
      (match_has outer memory 1 _ outerMatch data.tools)
      (match_has outer memory 40 _ outerMatch data.index) _ outerSegment.final_bounds addressBits
      (by decide) (by decide) enough
  exact ⟨after,⟨afterHeap.trans outerMatch.heap,afterLive.trans outerMatch.live,
    innerSegment.fresh.trans outerMatch.base⟩,afterPc,outerSegment.trans innerSegment⟩

/-- One actual iteration visits both guards, conditionally adds the
coefficient, then performs all seven original binomial writes. -/
theorem binomial_cycle_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (memory : SlotMemory) (i : ℕ) (matched : MemoryMatch before memory)
    (location : before.pc=pc 27) (bounded : StateBounds 64 (operandBudget P fee) before)
    (index : i≤P.certificate.stages) (data : BinomialData P memory i) :
    ∃ after : State,MemoryMatch after (binomialCycleMemory P memory i) ∧ after.pc=pc 27 ∧
      Segment binomialRegion input before after 64 (operandBudget P fee) 92 := by
  obtain ⟨guarded,guardMatch,guardPc,guardSegment⟩ :=
    binomial_guard_segment P fee input before memory i matched location bounded index data
  obtain ⟨added,addedMatch,addedPc,addSegment⟩ :
      ∃ added : State,MemoryMatch added (binomialAddMemory P memory i) ∧ added.pc=pc 30 ∧
        Segment binomialRegion input guarded added 64 (operandBudget P fee) 12 := by
    by_cases included : P.tools < i
    · have location29 : guarded.pc=pc 29 := by
        simpa [Comparison.nat,included] using guardPc
      obtain ⟨added,addMatch,addPc,segment⟩ := binomial_add_segment P fee input guarded memory i
        guardMatch location29 guardSegment.final_bounds index data.tail data.choose
      exact ⟨added,by simpa only [binomialAddMemory,ite_eq_left included] using addMatch,addPc,segment⟩
    · have location30 : guarded.pc=pc 30 := by
        simpa [Comparison.nat,included] using guardPc
      exact ⟨guarded,by simpa only [binomialAddMemory,ite_eq_right included] using guardMatch,location30,
        (Segment.refl binomialRegion input guarded 64 (operandBudget P fee) guardSegment.final_bounds).weaken_budget
          (by decide)⟩
  obtain ⟨after,afterMatch,afterPc,updateSegment⟩ := binomial_update_segment P fee input added
    (binomialAddMemory P memory i) i addedMatch addedPc addSegment.final_bounds index
    (binomial_add_preserves P memory i 0 _ (by decide) data.stages)
    (binomial_add_preserves P memory i 40 _ (by decide) data.index)
    (binomial_add_preserves P memory i 14 _ (by decide) data.natOne)
    (binomial_add_preserves P memory i 41 _ (by decide) data.choose)
  exact ⟨after,afterMatch,afterPc,(guardSegment.trans addSegment).trans updateSegment⟩

end PDROC.D27Prepare.Tail
