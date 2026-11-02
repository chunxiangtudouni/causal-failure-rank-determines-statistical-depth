module

public import PaperProofs.Paid.PDMenu_SearchZeroExit_156
public import PaperProofs.Paid.PDMenu_SearchBudgetStops_155

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

theorem finiteMultiplierTermination (P : Parameters) : P.FiniteMultiplierTermination := by
  intro fee hfee C accounting
  refine ⟨idealSearch_zero_records P fee hfee C accounting, ?_⟩
  intro hgap
  have hs := idealSearchState_stopped P fee hfee hgap C accounting
  have hstop := stoppedTwoFactor P fee hfee C accounting (P.bisectionBudget fee) hs
  have hn : ¬P.zeroChargeRisk fee ≤ P.certificate.risk := not_le.mpr hgap
  refine ⟨hs, zeroCharge_value_floor P fee hfee hgap C accounting, ?_, ?_⟩
  · simpa only [PaperProofs.Paid.Parameters.idealSearchRule, PaperProofs.Paid.Parameters.idealSearchSeedLaw,
      ite_eq_right hn, PaperProofs.Paid.Parameters.idealSearchState] using hstop.1
  · simpa only [PaperProofs.Paid.Parameters.idealSearchRule, PaperProofs.Paid.Parameters.idealSearchSeedLaw,
      ite_eq_right hn, PaperProofs.Paid.Parameters.idealSearchState] using hstop.2

end PDMenu
