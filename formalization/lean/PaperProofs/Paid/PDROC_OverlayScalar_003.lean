module

public import PaperProofs.Paid.PDROC_OverlayScalar_002
public import PaperProofs.Paid.PDROC_Surrogate_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal

namespace PDROC

/-- Complete original D13, with only the original parameter input. -/
theorem overlayLocalClaims (P : PaperProofs.Paid.Parameters) : P.OverlayLocalClaims :=
  overlayLocalClaims_of_uniformLocalSurrogate P (uniformLocalSurrogate P)

/-- The two all-path ENNReal increments in the original D14 witness fit the
original D15 budget. The statement also holds at zero fee. -/
theorem overlayIncrement_le (P : PaperProofs.Paid.Parameters) (fee : ℚ) (hfee : 0 ≤ fee) :
    P.overlayObservationIncrement fee + P.overlayCorrectionAmount fee ≤
      (17 / 2 : ℝ≥0∞) * P.feeScale fee :=
  overlayIncrement_le_of_overlayLocalClaims P (overlayLocalClaims P) fee hfee

end PDROC
