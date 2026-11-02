module

import PaperProofs.Paid.PDCompute_Codec_001
import PaperProofs.Paid.PDCompute_CodeRefinement_002
import RootD27Core_CanonicalCapsule_Claims_001
import PaperProofs.Paid.PDROC_Sampler_007
import PaperProofs.Paid.PDROC_DataBits_011
public import PaperProofs.Paid.ComputationalClaims

set_option autoImplicit false
set_option warningAsError true

namespace RootD27.Core.CanonicalCapsule

/-- Assemble exactly the seven original fields. The remaining bit theorem
is an explicit argument here; this adapter alone is not the original closure. -/
public theorem computationalClaims_of_uniform_bit
    (hbit : PaperProofs.Paid.Computation.UniformBitImplementationClaims) :
    PaperProofs.Paid.Computation.ComputationalClaims :=
  ⟨PDCompute.codecClaims, PDCompute.codeRefinementClaims,
    uniform_rational_implementation_claims, hbit,
    PDROC.exactRationalCoinClaims, PDROC.privateSeedSamplingClaims,
    PDROC.DataBits.cachedDataBitClaims⟩

end RootD27.Core.CanonicalCapsule
