module

public import PaperProofs.Paid.PDMenu_MenuNativeValue_128
public import PaperProofs.Paid.MultiplierSearch

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

/-- Reusable D19 solve assembly. The original actual Means proof is an
explicit dependency here; final D19 must instantiate it with the completed
D18 theorem rather than leave it as an extra original-target premise. -/
theorem solveCorrect_of_menuMeans (P : Parameters) (hmeans : P.MenuCompilerMeans)
    (fee : ℚ) (hfee : 0 ≤ fee) (C : P.PaymentContract) (accounting : NormalAccounting P.sharedInstance)
    (multiplier : ℚ) (hnonneg : 0 ≤ multiplier) (hLambda : multiplier ≤ P.Lambda) :
    P.SolveCorrect fee hfee C accounting (P.solveMultiplier fee multiplier) := by
  obtain ⟨_, _, hbill, hrisk⟩ := hmeans fee multiplier hfee hnonneg hLambda
    P.certificate.stages P.tools C.val C.property accounting
  refine ⟨rfl, hbill, hrisk, ?_⟩
  change paidPenaltyValue (P.input fee hfee) C.val accounting (ENNReal.ofReal (multiplier : ℝ)) = _
  rw [← P.freshPaidPenaltyOriginalIdentification fee hfee C accounting (ENNReal.ofReal (multiplier : ℝ))]
  exact PDMenuNativeValue.menuTableValueCorrect P fee multiplier hfee hnonneg hLambda
    P.certificate.stages P.tools P.certificate.stages P.tools le_rfl le_rfl

end PDMenu
