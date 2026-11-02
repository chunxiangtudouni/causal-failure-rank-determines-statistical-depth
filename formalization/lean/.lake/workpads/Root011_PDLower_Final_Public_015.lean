module
import PaperProofs.Paid.PDLower_PriceFinal_001
set_option autoImplicit false
set_option warningAsError true

example (P : PaperProofs.Paid.Parameters) : P.NativeSeparationClaims :=
  PDLower.nativeSeparationClaims P

example (pool : PaperProofs.Paid.FixedSharedPool) : pool.FixedPoolNativePriceClaims :=
  PDLower.fixedPoolNativePriceClaims pool

#print axioms PDLower.nativeSeparationClaims
#print axioms PDLower.fixedPoolNativePriceClaims
