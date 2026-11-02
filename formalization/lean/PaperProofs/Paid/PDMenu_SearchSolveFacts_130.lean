module

public import PaperProofs.Paid.PDMenu_SearchSolveCorrect_126
public import PaperProofs.Paid.PDMenu_MenuCompilerComplete_129

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem searchSolveCorrect (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (multiplier : ℚ) (hnonneg : 0 ≤ multiplier) (hLambda : multiplier ≤ P.Lambda) :
    P.SolveCorrect fee hfee C accounting (P.solveMultiplier fee multiplier) :=
  solveCorrect_of_menuMeans P (PDROC.menuCompilerMeans P) fee hfee C accounting multiplier hnonneg hLambda

theorem searchSolveStats (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee) (multiplier : ℚ) :
    0 ≤ P.solveCost fee (P.solveMultiplier fee multiplier) ∧
      0 ≤ P.solveRisk (P.solveMultiplier fee multiplier) ∧ P.solveRisk (P.solveMultiplier fee multiplier) ≤ 1 := by
  have hs := solveMenuTable_stats P fee multiplier P.certificate.stages P.tools P.certificate.stages le_rfl P.tools
  exact ⟨add_nonneg hs.1 (mul_nonneg hfee hs.2.1), hs.2.2.2.1, hs.2.2.2.2⟩

theorem searchSolve_objective (P : Parameters) (fee multiplier : ℚ) :
    (P.solveRecord (P.solveMultiplier fee multiplier)).objective fee multiplier =
      P.solveCost fee (P.solveMultiplier fee multiplier) + multiplier * P.solveRisk (P.solveMultiplier fee multiplier) := rfl

theorem searchSolve_objective_nonneg (P : Parameters) (fee : ℚ) (hfee : 0 ≤ fee)
    (multiplier : ℚ) (hm : 0 ≤ multiplier) :
    0 ≤ (P.solveRecord (P.solveMultiplier fee multiplier)).objective fee multiplier := by
  rw [searchSolve_objective]
  have hs := searchSolveStats P fee hfee multiplier
  exact add_nonneg hs.1 (mul_nonneg hm hs.2.1)

end PDMenu
