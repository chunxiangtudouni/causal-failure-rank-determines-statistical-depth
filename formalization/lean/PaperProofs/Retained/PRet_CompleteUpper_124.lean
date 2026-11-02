module

public import PaperProofs.Retained.PRet_ReferenceCost_123
public import PaperProofs.Retained.PRet_Overflow_Original_003

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetCompleteUpper124

open Common

/-- Complete ORIGINAL finite-girth native upper law: actual risk, whole
variable fees, same-tape truncation, original caps and H0 are all discharged. -/
theorem nativeUpperPriceLaw {I : Instance} (input : StatisticalInput I) : NativeUpperPriceLaw input :=
  PRetReferenceCost123.nativeUpperPriceLaw_of_truncation input
    (PRetOverflow.truncationAndNativeImplementation input)

end PaperProofs.Retained.PRetCompleteUpper124
