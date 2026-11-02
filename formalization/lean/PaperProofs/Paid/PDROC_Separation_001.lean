module

public import PaperProofs.Paid.Claims

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDROC

/-- Combine the original overlay and no-correction upper bounds on the
extended nonnegative reals, including infinite free baselines. -/
theorem separation_min_upper (A D S V : ℝ≥0∞)
    (hAD : V ≤ A + 9 * D) (hS : V ≤ 7 * S) :
    V ≤ 9 * min (A + D) S := by
  have hA : A ≤ 9 * A := le_mul_of_one_le_left' (by norm_num)
  have hleft : V ≤ 9 * (A + D) := hAD.trans <| calc
    A + 9 * D ≤ 9 * A + 9 * D := add_le_add hA le_rfl
    _ = 9 * (A + D) := (mul_add 9 A D).symm
  have hright : V ≤ 9 * S := hS.trans
    (mul_le_mul' (by norm_num : (7 : ℝ≥0∞) ≤ 9) le_rfl)
  rw [mul_min]
  exact le_min hleft hright

end PDROC
