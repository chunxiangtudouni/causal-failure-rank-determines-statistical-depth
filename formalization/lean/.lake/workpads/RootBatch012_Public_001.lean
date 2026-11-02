module

import PaperProofs.Paid.PDCompute_Complete_001

set_option autoImplicit false
set_option warningAsError true

open PaperProofs.Paid.Computation

example : ComputationalClaims := PDCompute.computationalClaims
example : CodecClaims := PDCompute.computationalClaims.1
example : CodeRefinementClaims := PDCompute.computationalClaims.2.1
example : UniformRationalImplementationClaims := PDCompute.computationalClaims.2.2.1
example : UniformBitImplementationClaims := PDCompute.computationalClaims.2.2.2.1
example : ExactRationalCoinClaims := PDCompute.computationalClaims.2.2.2.2.1
example : PrivateSeedSamplingClaims := PDCompute.computationalClaims.2.2.2.2.2.1
example : ∀ P : PaperProofs.Paid.Parameters, P.CachedDataBitClaims :=
  PDCompute.computationalClaims.2.2.2.2.2.2

#print axioms PDCompute.computationalClaims
