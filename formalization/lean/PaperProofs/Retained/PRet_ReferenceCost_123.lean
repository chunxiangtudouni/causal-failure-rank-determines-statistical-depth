module

public import PaperProofs.Retained.PRet_NativeUpper_121
public import PaperProofs.Retained.PRet_ActualCost_122
public import PaperProofs.Retained.PRet_RiskMassFlow_Original_018
public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetReferenceCost123

open Common Common.Native Statistics MeasureTheory
open scoped ENNReal

/-- BOTH original ReferenceRiskAndCost fields, for the actual original
retained rule and all original contracts/accountings/budgets. -/
theorem referenceRiskAndCost {I : Instance} (input : StatisticalInput I) : ReferenceRiskAndCost input :=
  ⟨PRetRiskMassFlow.referenceRiskAndCost_risk input,
    PRetActualCost122.referenceExpectedCost_of_observationEnvelope input
      (PDROC.RetainedEnvelopeRun.expectedObservationBill_le_observationEnvelope input)⟩

/-- The original finite-girth native upper law, with only the separately
proved original truncation interface left for the final assembly. -/
theorem nativeUpperPriceLaw_of_truncation {I : Instance} (input : StatisticalInput I)
    (truncation : TruncationAndNativeImplementation input) : NativeUpperPriceLaw input :=
  PRetNativeUpper121.nativeUpperPriceLaw_of_interfaces input (referenceRiskAndCost input) truncation

end PaperProofs.Retained.PRetReferenceCost123
