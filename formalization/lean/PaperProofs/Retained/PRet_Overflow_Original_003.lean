module

public import PaperProofs.Retained.PRet_Overflow_Union_002
public import PaperProofs.Retained.PRet_NativeImplementation_118

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetOverflow

variable {I : Instance}

theorem truncationAndNativeImplementation (input : StatisticalInput I) : TruncationAndNativeImplementation input := by
  intro C hretained accounting delta exponent budget positiveDelta smallDelta choice
  refine ⟨?_,?_,?_,?_⟩
  · exact PRetTruncation120.retainedRunActualBill_le_ideal input C hretained accounting budget (referenceQuota input exponent)
  · exact (PRetTruncation120.retainedRisk_le_ideal_add_overflow input C hretained accounting budget
      (referenceQuota input exponent)).trans (add_le_add le_rfl
        (retainedOverflow_le_half input C hretained accounting delta positiveDelta smallDelta exponent budget choice))
  · exact PRetNativeImplementation118.allPrefixBounds input C hretained accounting budget exponent
  · exact PRetNativeImplementation118.nativeImplementation input C hretained accounting budget exponent

end PRetOverflow
