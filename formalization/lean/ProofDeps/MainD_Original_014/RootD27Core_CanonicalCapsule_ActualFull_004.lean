module

import RootD27Core_CanonicalCapsule_Conjuncts_003
import Paid.PDROC_BitVM_VM_OriginalClaims_015
public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true

namespace RootD27.Core.CanonicalCapsule

/-- The complete original seven-field target, with no remaining premise. -/
public theorem computationalClaims : PaperProofs.Paid.Computation.ComputationalClaims :=
  computationalClaims_of_uniform_bit
    PDROC.BitVM.VM.OriginalClaims.uniform_bit_implementation_claims

end RootD27.Core.CanonicalCapsule
