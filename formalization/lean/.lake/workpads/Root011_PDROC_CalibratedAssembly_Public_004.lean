module

import PaperProofs.Paid.PDROC_CalibratedAssembly_004

set_option autoImplicit false
set_option warningAsError true

open PaperProofs.Paid

example (P : Parameters) : P.CalibratedImplementationClaims :=
  PDROC.calibratedImplementationClaims P

example (P : Parameters) : P.CalibratedNativeEightClaims :=
  PDROC.calibratedNativeEightClaims P

example (P : Parameters) : P.CalibratedBackendClaims :=
  PDROC.calibratedBackendClaims P

#print axioms PDROC.calibratedImplementationClaims
#print axioms PDROC.calibratedNativeEightClaims
#print axioms PDROC.calibratedBackendClaims
