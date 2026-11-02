module

public import PaperProofs.Paid.PDROC_NativeSeparation_002
public import PaperProofs.Paid.PDROC_CalibratedAssembly_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDLower

/-- Complete original D29, for its original fixed calibrated algorithm,
contracts, qualification and whole-policy native comparator. -/
theorem nativeSeparationClaims (P : PaperProofs.Paid.Parameters) : P.NativeSeparationClaims :=
  PDROC.nativeSeparationClaims_of_calibratedNativeEight P (PDROC.calibratedNativeEightClaims P)

end PDLower
