module

public import PaperProofs.Paid.PDROC_EndpointBounds_005
public import PaperProofs.Paid.PDROC_EndpointDP_007
public import PaperProofs.Paid.PDROC_Calibration_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid

namespace PDROC

/-- Exact original D23, assembled from the actual finite-array law and
the original-Q tail/calibration-room bounds. -/
theorem boundedEndpointClaims (P : Parameters) : P.BoundedEndpointClaims :=
  boundedEndpointClaims_of_dp_law P (fun m _ _ => endpointDP_error_and_nonneg P m)

/-- Exact original D24 with its actual D23 dependency supplied, retaining
the original two coins, rational calibration, Q, error and charge fields. -/
theorem exactCalibrationClaims (P : Parameters) : P.ExactCalibrationClaims :=
  exactCalibrationClaims_of_boundedEndpointClaims P (boundedEndpointClaims P)

end PDROC
