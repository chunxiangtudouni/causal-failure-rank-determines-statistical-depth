module

import Paid.RootD27Core_UniformRational_098
public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true

namespace RootD27.Core.CanonicalCapsule

/-- The complete original claim. Only its formal statement is public;
the numeric implementation proof remains behind an ordinary module boundary. -/
public theorem uniform_rational_implementation_claims :
    PaperProofs.Paid.Computation.UniformRationalImplementationClaims :=
  RootD27.Core.uniform_rational_implementation_claims

end RootD27.Core.CanonicalCapsule
