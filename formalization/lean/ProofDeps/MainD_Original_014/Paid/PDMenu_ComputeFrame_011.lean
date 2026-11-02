module

public import Paid.PDMenu_ComputeFrame_010

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu.ComputeFrame

open PaperProofs.Paid.Computation

theorem FetchesCode.append_left {program : Program} {origin : ℕ} {first later : List Instruction}
    (fetched : FetchesCode program origin (first++later)) : FetchesCode program origin first := by
  intro offset inside
  have hf := fetched offset (by rw [List.length_append]; omega)
  exact hf.trans (List.getElem?_append_left inside)

theorem FetchesCode.append_right {program : Program} {origin : ℕ} {first later : List Instruction}
    (fetched : FetchesCode program origin (first++later)) : FetchesCode program (origin+first.length) later := by
  intro offset inside
  have hf := fetched (first.length+offset) (by rw [List.length_append]; omega)
  rw [Nat.add_assoc]
  apply hf.trans
  rw [List.getElem?_append_right (by omega),Nat.add_sub_cancel_left]

/-- Whole-program literal list layout transports a selected block's
actual fetches. Direct/indirect branch operands are never relocated. -/
theorem FetchesCode.middle {program : Program} {origin : ℕ} {beforeCode block afterCode : List Instruction}
    (fetched : FetchesCode program origin (beforeCode++block++afterCode)) :
    FetchesCode program (origin+beforeCode.length) block :=
  fetched.append_left.append_right

end PDMenu.ComputeFrame
