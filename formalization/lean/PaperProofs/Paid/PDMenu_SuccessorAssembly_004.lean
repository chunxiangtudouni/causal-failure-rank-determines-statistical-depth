module

public import PaperProofs.Paid.PDMenu_EndpointMinimum_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs

/-- A conditional assembly lemma only. The tool-injection policy comparison
is explicit here and is not an assumption of the original full-policy value. -/
theorem paidSuccessorOrder_of_tools_antitone (P : Paid.Parameters)
    (hmono : ∀ (fee : ℚ) (hfee : 0 ≤ fee) (n k : ℕ) (penalty : ℝ≥0∞),
      P.freshPaidPenalty fee hfee n (k + 1) penalty ≤ P.freshPaidPenalty fee hfee n k penalty) :
    P.PaidSuccessorOrder := by
  intro fee hfee n k penalty _hn _hp
  refine ⟨zero_le, ?_, paidBadSuccessor_le_penalty P fee hfee n k penalty⟩
  cases k with
  | zero => exact P.freshPaidPenalty_le_penalty fee hfee (n - 1) 0 penalty
  | succ k =>
    apply le_min
    · exact P.freshPaidPenalty_le_penalty fee hfee (n - 1) (k + 1) penalty
    · exact (hmono fee hfee (n - 1) k penalty).trans (le_add_left le_rfl)

end PDMenu
