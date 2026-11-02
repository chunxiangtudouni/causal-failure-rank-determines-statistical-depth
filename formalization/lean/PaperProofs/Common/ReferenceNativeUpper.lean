module

public import PaperProofs.Common.ReferenceTruncation
public import PaperProofs.Common.ReferenceOverflowRealization

/-!
The concrete original-cap upper connection uses proved review, actual
same-tape truncation, and actual overflow bounds. This module exposes the
conditional API; ReferenceNativeRisk instantiates B17 from ReferenceMassFlow.
The supplied original H0 qualification is still required; this module does
not derive it from numeric caps or restrict the full comparison infimum.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem referenceBounded_risk_of_referenceRisk (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (hreference : ReferenceRiskGuarantee input C accounting)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget) :
    risk input C .uncapped accounting
      (referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent).rule (Measure.dirac ()) ≤
        ENNReal.ofReal delta :=
  referenceBounded_risk_of_guarantees input C hcurrent accounting hreference
    (referenceTruncationGuarantee input) (referenceOverflowGuarantee input)
    delta hd hsmall exponent budget choice

/-- An actual native policy under the original certificates, rather than
only a bound on an abstract value. All charges on failed paths remain. -/
theorem referenceNative_policy_of_referenceRisk (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (hreference : ReferenceRiskGuarantee input C accounting)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceOriginalQualification input C hcurrent.1 accounting I.tools budget exponent) :
    ∃ policy : Policy input C .native accounting Unit,
      policy.rule = (referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent).rule ∧
      risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
      expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
        expectedBill input C .uncapped accounting
          (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) := by
  let bounded := referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent
  let reviews := referenceReviewBounds input C hcurrent.1 accounting I.tools budget exponent
    choice.positive choice.small
  let native := bounded.enforceCaps input C accounting (referenceQuota input exponent)
    reviews qualification.normal_calls qualification.stage_quota qualification.total_calls
  refine ⟨native, rfl, ?_, ?_⟩
  · rw [enforceCaps_risk_eq input C accounting bounded (referenceQuota input exponent)
      reviews qualification.normal_calls qualification.stage_quota qualification.total_calls (Measure.dirac ())]
    exact referenceBounded_risk_of_referenceRisk input C hcurrent accounting hreference delta hd hsmall exponent budget choice
  · rw [enforceCaps_expectedBill_eq input C accounting bounded (referenceQuota input exponent)
      reviews qualification.normal_calls qualification.stage_quota qualification.total_calls (Measure.dirac ())]
    exact lintegral_mono (referenceTruncationGuarantee input C hcurrent.1 accounting I.tools budget exponent
      choice.positive choice.small).1

/-- Full-policy native infimum upper connection with an explicit B17 input.
ReferenceNativeRisk removes this input using its proved theorem; the
separate leading-term cost target B18 is not assumed here. -/
theorem native_value_le_reference_ideal_of_referenceRisk (input : StatisticalInput I)
    (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (hreference : ReferenceRiskGuarantee input C accounting)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceOriginalQualification input C hcurrent.1 accounting I.tools budget exponent) :
    value input C .native accounting (ENNReal.ofReal delta) ≤
      expectedBill input C .uncapped accounting
        (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) :=
  native_value_le_reference_ideal_of_guarantees input C hcurrent accounting hreference
    (referenceTruncationGuarantee input) (referenceOverflowGuarantee input)
    delta hd hsmall exponent budget choice qualification

end PaperProofs.Common.Native
