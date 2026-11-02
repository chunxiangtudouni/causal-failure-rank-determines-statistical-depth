module

public import Paid.PDROC_D27Prepare_J_003
public import Paid.PDROC_D27Prepare_Tail_004
public import Paid.PDROC_D27Prepare_Resources_010

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources PDROC.D27Prepare.Q

namespace PDROC.D27Prepare.J

/-- All actual pages32--36, including fee=0 and both branches of the
original minimum. Only the first-floor cell43 is written. -/
theorem first_floor_segment (P : Parameters) (fee : ℚ) (input : List Cell) (before : State)
    (raw : Search.RawConstants P fee before) (location : before.pc = pc 32)
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, Search.RawConstants P fee after ∧ after.pc = pc 37 ∧
      Search.SlotHas after 43 (.rational (P.firstChargeFloor fee)) ∧
      Segment {43} input before after 64 (operandBudget P fee) 26 := by
  suffices complete : ∃ after : State, after.pc = pc 37 ∧
      Search.SlotHas after 43 (.rational (P.firstChargeFloor fee)) ∧
      Segment {43} input before after 64 (operandBudget P fee) 26 by
    obtain ⟨after, afterPc, value, segment⟩ := complete
    have kept : Search.RawConstants P fee after := Search.RawConstants.transport P fee before after raw
      (by
        intro address read
        exact segment.final_frame.1.1 address (by simp only [Finset.mem_singleton]; omega))
      segment.final_frame.2 segment.fresh
    exact ⟨after, kept, afterPc, value, segment⟩
  have addressBits := operandBudget_address_bits P fee
  have enough : 2 ≤ operandBudget P fee := by
    have h := linear_le_operandBudget P fee
    omega
  obtain ⟨middle, middlePc, middleHeap, middleLive, first⟩ :=
    Tail.rat_compare_segment {43} input 32 (by decide) before location .equal 5 16 34 33 fee 0 rfl
      raw.fresh raw.feeValue raw.ratZero (operandBudget P fee) bounded addressBits (by decide) (by decide) enough
  have middleRaw := Search.RawConstants.transport P fee before middle raw
    (fun address _ => congrFun middleHeap address) (fun address member => by simpa only [middleLive] using member) first.fresh
  by_cases feeZero : fee = 0
  · have at33 : middle.pc = pc 33 := by simpa [Comparison.rat, feeZero] using middlePc
    obtain ⟨after, afterPc, value, later⟩ := copy_page_segment {43} input (operandBudget P fee)
      33 37 4 43 (by decide) rfl (by decide) (by decide) (by decide) middle at33
      middleRaw.fresh (.rational P.reviewFee) middleRaw.reviewFee first.final_bounds addressBits
    exact ⟨after, afterPc, by simpa only [firstChargeFloor, ite_eq_left feeZero] using value,
      (first.trans later).weaken_budget (by decide)⟩
  · have at34 : middle.pc = pc 34 := by simpa [Comparison.rat, feeZero] using middlePc
    obtain ⟨compared, comparedPc, comparedHeap, comparedLive, second⟩ :=
      Tail.rat_compare_segment {43} input 34 (by decide) middle at34 .lessEqual 4 5 36 35 P.reviewFee fee rfl
        middleRaw.fresh middleRaw.reviewFee middleRaw.feeValue (operandBudget P fee) first.final_bounds
        addressBits (by decide) (by decide) enough
    have comparedRaw := Search.RawConstants.transport P fee middle compared middleRaw
      (fun address _ => congrFun comparedHeap address)
      (fun address member => by simpa only [comparedLive] using member) second.fresh
    by_cases reviewFirst : P.reviewFee ≤ fee
    · have at35 : compared.pc = pc 35 := by simpa [Comparison.rat, reviewFirst] using comparedPc
      obtain ⟨after, afterPc, value, later⟩ := copy_page_segment {43} input (operandBudget P fee)
        35 37 4 43 (by decide) rfl (by decide) (by decide) (by decide) compared at35
        comparedRaw.fresh (.rational P.reviewFee) comparedRaw.reviewFee second.final_bounds addressBits
      exact ⟨after, afterPc, by simpa only [firstChargeFloor, ite_eq_right feeZero, min_eq_left reviewFirst] using value,
        (first.trans second).trans later⟩
    · have at36 : compared.pc = pc 36 := by simpa [Comparison.rat, reviewFirst] using comparedPc
      obtain ⟨after, afterPc, value, later⟩ := copy_page_segment {43} input (operandBudget P fee)
        36 37 5 43 (by decide) rfl (by decide) (by decide) (by decide) compared at36
        comparedRaw.fresh (.rational fee) comparedRaw.feeValue second.final_bounds addressBits
      exact ⟨after, afterPc, by simpa only [firstChargeFloor, ite_eq_right feeZero, min_eq_right (lt_of_not_ge reviewFirst).le] using value,
        (first.trans second).trans later⟩

end PDROC.D27Prepare.J
