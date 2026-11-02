module

public import PaperProofs.Paid.PDROC_CalibratedAssembly_002
public import PaperProofs.Paid.PDMenu_MultiplierSearchComplete_158
public import PaperProofs.Paid.PDROC_EndpointFinal_001
public import PaperProofs.Paid.PDMenu_CalibrationMarks_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid

namespace PDROC.CalibratedAssembly

/-- Eliminate finite termination using the independently proved complete
original D22 theorem, with its actual Nat.clog search and zero-charge exit. -/
theorem nativeEight_of_implementation (P : Parameters)
    (implementation : P.CalibratedImplementationClaims) : P.CalibratedNativeEightClaims :=
  nativeEight_of_implementation_and_termination P implementation (PDMenu.finiteMultiplierTermination P)

/-- All original backend fields except D25 are independently discharged.
The final runtime/law theorem supplies D25 rather than a performance oracle. -/
theorem backend_of_implementation (P : Parameters)
    (implementation : P.CalibratedImplementationClaims) : P.CalibratedBackendClaims :=
  ⟨PDROC.boundedEndpointClaims P, PDROC.exactCalibrationClaims P,
    PDMenu.calibrationMarksClaims P, implementation, nativeEight_of_implementation P implementation⟩

end PDROC.CalibratedAssembly
