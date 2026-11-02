module

public import PaperProofs.Paid.PDMenu_SearchInitialBounds_131
public import PaperProofs.Paid.PDMenu_MenuZeroSolve_125

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Paid

/-- Complete original D19, with the actual majority's full failed-path bill,
original independent paid infimum and literal Lambda initial solve bracket. -/
theorem majorityInitialBracket (P : Parameters) : P.MajorityInitialBracket := by
  intro fee hfee C accounting
  have hw := majorityInitialBracket_baseline_fields P fee hfee C accounting
  exact ⟨hw.1, hw.2.1, hw.2.2.1, hw.2.2.2,
    searchSolveCorrect P fee hfee C accounting 0 le_rfl P.Lambda_pos.le,
    searchSolveCorrect P fee hfee C accounting P.Lambda P.Lambda_pos.le le_rfl,
    solveZero_risk P fee, solveZero_cost P fee,
    searchUpper_risk_le_value_div P fee hfee C accounting,
    searchUpper_value_div_le_baseline P fee hfee C accounting,
    searchUpper_risk_le_three_quarters P fee hfee C accounting⟩

end PDMenu
