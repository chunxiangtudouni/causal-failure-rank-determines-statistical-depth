module

import RootD27Core_CanonicalCapsule_ActualFull_004
public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true

namespace PDCompute

/-- The complete original seven-field computation target, without extra premises. -/
public theorem computationalClaims : PaperProofs.Paid.Computation.ComputationalClaims :=
  RootD27.Core.CanonicalCapsule.computationalClaims

end PDCompute
