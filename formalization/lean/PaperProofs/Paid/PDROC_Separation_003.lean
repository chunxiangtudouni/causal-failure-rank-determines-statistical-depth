module

public import PaperProofs.Paid.PDROC_Separation_001
public import PaperProofs.Paid.PDROC_OverlayFinal_001
public import PaperProofs.Paid.PDLower_NoCorrection_001
public import PaperProofs.Paid.PDLower_Price_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid

namespace PDROC

/-- The original D30 upper bound with the uncapped same-contract free
baseline. The overlay and no-correction comparisons are already proved. -/
theorem uncappedSeparationUpper (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.uncappedValue C accounting fee hf ≤
      9 * P.separationScale C .uncapped accounting fee := by
  change P.uncappedValue C accounting fee hf ≤
    9 * min (P.freeValue C .uncapped accounting + P.feeScale fee) P.saturationScale
  apply separation_min_upper
  · exact paidOverlayValue P fee hf C accounting
  · exact PDLower.noCorrectionValueComparison P C accounting fee hf

/-- Complete original D30 for the original uncapped policy infima, with
no Native resource qualification or additional comparison premise. -/
theorem uncappedSeparation (P : Parameters) (C : P.PaymentContract)
    (accounting : NormalAccounting P.sharedInstance) (fee : ℚ) (hf : 0 ≤ fee) :
    P.UncappedSeparation C accounting fee hf := by
  constructor
  · exact PDLower.separationLower P C .uncapped accounting fee hf
  · exact uncappedSeparationUpper P C accounting fee hf

end PDROC
