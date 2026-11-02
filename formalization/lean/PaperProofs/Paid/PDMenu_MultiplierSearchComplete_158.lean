module

public import PaperProofs.Paid.PDMenu_SearchFiniteTermination_157
public import PaperProofs.Paid.PDMenu_ZeroChargeAndPositive_152

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Paid

universe u

theorem multiplierSearchClaims (P : Parameters) : P.MultiplierSearchClaims.{u} :=
  ⟨majorityInitialBracket P, exactMixtureAndGap P, stoppedTwoFactor P,
    zeroChargeOptimum P, positiveChargeLower P, finiteMultiplierTermination P⟩

end PDMenu
