module

public import PaperProofs.Paid.PDMenu_MenuStoredRecursion_079
public import PaperProofs.Paid.MultiplierSearch

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Paid PaperProofs.Paid.Parameters

theorem menuComputedEntry_zero_penalty (P : Parameters) (fee : ℚ) (N K n k : ℕ)
    (hpos : 0 < n) (hn : n ≤ N) (hk : k ≤ K) :
    menuEntryAt (P.solveMenuTable fee 0 K N) n k = abandonEntry := by
  cases n with
  | zero => exact (Nat.not_lt_zero _ hpos).elim
  | succ n =>
    rw [solveMenuTable_cell_prefix P fee 0 K N (n + 1) hn k,
      solveMenuTable_last_entry_succ P fee 0 K n k hk]
    exact ite_eq_left rfl

theorem solveZero_record (P : Parameters) (fee : ℚ) :
    P.solveRecord (P.solveMultiplier fee 0) = abandonEntry :=
  menuComputedEntry_zero_penalty P fee P.certificate.stages P.tools P.certificate.stages P.tools
    P.certificate.stages_pos le_rfl le_rfl

theorem solveZero_risk (P : Parameters) (fee : ℚ) : P.solveRisk (P.solveMultiplier fee 0) = 1 := by
  unfold Parameters.solveRisk
  rw [solveZero_record]
  rfl

theorem solveZero_cost (P : Parameters) (fee : ℚ) : P.solveCost fee (P.solveMultiplier fee 0) = 0 := by
  unfold Parameters.solveCost
  rw [solveZero_record]
  simp only [abandonEntry, mul_zero, add_zero]

end PDMenu
