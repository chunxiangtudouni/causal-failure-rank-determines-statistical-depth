module

public import Paid.PDROC_D27Prepare_Q_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDROC.D27Prepare.Program PDROC.D27Prepare.Resources

namespace PDROC.D27Prepare.Q

theorem select_max_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (location : before.pc = pc 16) (fresh : before.register .fresh = .natural 0)
    (x y : ℕ) (hx : Search.SlotHas before 52 (.natural x))
    (hy : Search.SlotHas before 53 (.natural y))
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, after.pc = pc 19 ∧ Search.SlotHas after 9 (.natural (max x y)) ∧
      Segment region input before after 64 (operandBudget P fee) 17 := by
  have addressBits := operandBudget_address_bits P fee
  have enough : 2 ≤ operandBudget P fee := by
    have h := linear_le_operandBudget P fee
    omega
  obtain ⟨middle, middlePc, middleHeap, middleLive, first⟩ :=
    nat_compare_segment region input 16 (by decide) before location .less 52 53 17 18 x y rfl
      fresh hx hy (operandBudget P fee) bounded addressBits (by decide) (by decide) enough
  have middleFresh := first.fresh.trans fresh
  have transfer (address : ℕ) (value : Cell) (old : Search.SlotHas before address value) :
      Search.SlotHas middle address value := by
    simpa only [Search.SlotHas, middleHeap, middleLive] using old
  by_cases smaller : x < y
  · have at18 : middle.pc = pc 18 := by simpa [Comparison.nat, smaller] using middlePc
    obtain ⟨after, afterPc, value, later⟩ := copy_segment P fee input 18 19 53 9
      (by decide) rfl (by decide) (by decide) (by decide) middle at18 middleFresh
      (.natural y) (transfer 53 _ hy) first.final_bounds
    exact ⟨after, afterPc, by simpa only [max_eq_right smaller.le] using value, first.trans later⟩
  · have at17 : middle.pc = pc 17 := by simpa [Comparison.nat, smaller] using middlePc
    obtain ⟨after, afterPc, value, later⟩ := copy_segment P fee input 17 19 52 9
      (by decide) rfl (by decide) (by decide) (by decide) middle at17 middleFresh
      (.natural x) (transfer 52 _ hx) first.final_bounds
    exact ⟨after, afterPc, by simpa only [max_eq_left (Nat.le_of_not_gt smaller)] using value, first.trans later⟩

theorem ensure_one_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (location : before.pc = pc 19) (fresh : before.register .fresh = .natural 0)
    (x : ℕ) (hx : Search.SlotHas before 9 (.natural x))
    (one : Search.SlotHas before 14 (.natural 1))
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, after.pc = pc 21 ∧ Search.SlotHas after 9 (.natural (max 1 x)) ∧
      Segment region input before after 64 (operandBudget P fee) 17 := by
  have addressBits := operandBudget_address_bits P fee
  have enough : 2 ≤ operandBudget P fee := by
    have h := linear_le_operandBudget P fee
    omega
  obtain ⟨middle, middlePc, middleHeap, middleLive, first⟩ :=
    nat_compare_segment region input 19 (by decide) before location .less 9 14 21 20 x 1 rfl
      fresh hx one (operandBudget P fee) bounded addressBits (by decide) (by decide) enough
  have middleFresh := first.fresh.trans fresh
  have transfer (address : ℕ) (value : Cell) (old : Search.SlotHas before address value) :
      Search.SlotHas middle address value := by
    simpa only [Search.SlotHas, middleHeap, middleLive] using old
  by_cases smaller : x < 1
  · have at20 : middle.pc = pc 20 := by simpa [Comparison.nat, smaller] using middlePc
    obtain ⟨after, afterPc, value, later⟩ := copy_segment P fee input 20 21 14 9
      (by decide) rfl (by decide) (by decide) (by decide) middle at20 middleFresh
      (.natural 1) (transfer 14 _ one) first.final_bounds
    exact ⟨after, afterPc, by simpa only [max_eq_left (by omega : x ≤ 1)] using value, first.trans later⟩
  · have at21 : middle.pc = pc 21 := by simpa [Comparison.nat, smaller] using middlePc
    exact ⟨middle, at21, by simpa only [max_eq_right (by omega : 1 ≤ x)] using transfer 9 _ hx,
      first.weaken_budget (by decide)⟩

theorem select_Q_segment (P : Parameters) (fee : ℚ) (input : List Cell)
    (before : State) (location : before.pc = pc 16) (fresh : before.register .fresh = .natural 0)
    (x y : ℕ) (hx : Search.SlotHas before 52 (.natural x))
    (hy : Search.SlotHas before 53 (.natural y)) (one : Search.SlotHas before 14 (.natural 1))
    (bounded : StateBounds 64 (operandBudget P fee) before) :
    ∃ after : State, after.pc = pc 21 ∧ Search.SlotHas after 9 (.natural (max 1 (max x y))) ∧
      Segment region input before after 64 (operandBudget P fee) 34 := by
  obtain ⟨middle, middlePc, middleValue, first⟩ :=
    select_max_segment P fee input before location fresh x y hx hy bounded
  have middleOne := progress_slot before middle first.final_frame 14 (by decide) _ one
  obtain ⟨after, afterPc, value, later⟩ := ensure_one_segment P fee input middle middlePc
    (first.fresh.trans fresh) (max x y) middleValue middleOne first.final_bounds
  exact ⟨after, afterPc, value, first.trans later⟩

end PDROC.D27Prepare.Q
