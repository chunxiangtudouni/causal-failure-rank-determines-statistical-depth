module

public import PaperProofs.Paid.PDLower_NativeFinal_001
public import PaperProofs.Paid.PDLower_UniformPrice_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDLower

/-- Complete original D36, with the original one cutoff uniform over
nonnegative fees and all original joint qualifications. -/
theorem fixedPoolNativePriceClaims (pool : PaperProofs.Paid.FixedSharedPool) :
    pool.FixedPoolNativePriceClaims :=
  fixedPoolNativePriceClaims_of_nativeSeparation pool nativeSeparationClaims

end PDLower
