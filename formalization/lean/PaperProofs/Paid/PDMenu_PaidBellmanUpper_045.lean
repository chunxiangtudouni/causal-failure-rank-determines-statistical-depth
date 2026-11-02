module

public import PaperProofs.Paid.PDMenu_PaidEndpointUpper_044

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- The original endpoint objective is an upper bound for the independently
defined full paid policy value, including every correction/failure bill. -/
theorem freshPaidPenalty_le_paidEndpointObjective (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k m : ℕ) (penalty : ℝ≥0∞) (hn : 0 < n) (hp : penalty ≠ ⊤) :
    P.freshPaidPenalty fee hfee n k penalty ≤ P.paidEndpointObjective fee hfee n k penalty m := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_zero_of_lt hn)
  cases k with
  | zero =>
    simpa only [Parameters.paidEndpointObjective, Parameters.paidGoodSuccessor,
      Parameters.paidBadSuccessor, Nat.succ_sub_one] using
      freshPaidPenalty_noRepair_endpoint_upper P fee hfee r 0 m penalty hp
  | succ k =>
    rcases le_total penalty (ENNReal.ofReal (fee : ℝ) + P.freshPaidPenalty fee hfee r k penalty) with h | h
    · simpa only [Parameters.paidEndpointObjective, Parameters.paidGoodSuccessor,
        Parameters.paidBadSuccessor, Nat.succ_sub_one, min_eq_left h] using
        freshPaidPenalty_noRepair_endpoint_upper P fee hfee r (k + 1) m penalty hp
    · simpa only [Parameters.paidEndpointObjective, Parameters.paidGoodSuccessor,
        Parameters.paidBadSuccessor, Nat.succ_sub_one, min_eq_right h] using
        freshPaidPenalty_repair_endpoint_upper P fee hfee r k m penalty hp

/-- Complete constructive upper direction of the original D16 Bellman
identity. No optimizer attainment, continuation guarantee or Bellman input
is assumed. The reverse inequality is still a separate task. -/
theorem freshPaidPenalty_bellman_upper (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (n k : ℕ) (penalty : ℝ≥0∞) (hn : 0 < n) (hp : penalty ≠ ⊤) :
    P.freshPaidPenalty fee hfee n k penalty ≤
      min penalty (⨅ m : ℕ, P.paidEndpointObjective fee hfee n k penalty m) :=
  le_min (P.freshPaidPenalty_le_penalty fee hfee n k penalty)
    (le_iInf (fun m => freshPaidPenalty_le_paidEndpointObjective P fee hfee n k m penalty hn hp))

end PDMenu
