module

public import PaperProofs.Common.ReferenceNativeUpper
public import PaperProofs.Common.ReferenceMassFlow

/-!
The actual original-cap risk/price-to-ideal interface with B17 instantiated
by its proved true-entry mass telescope. The original selected-controller
normal-call certificate and numeric caps remain precisely as in the paper.
They do not restrict the full-policy comparison infimum. No leading-term
cost bound, Bellman claim or finite expected-cost premise is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem referenceBounded_risk (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget) :
    risk input C .uncapped accounting
      (referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent).rule (Measure.dirac ()) ≤
        ENNReal.ofReal delta :=
  referenceBounded_risk_of_referenceRisk input C hcurrent accounting
    (referenceRiskGuarantee input C accounting) delta hd hsmall exponent budget choice

/-- This is an actual native Policy under the ORIGINAL qualification.
The separate proof that a chosen normal-I/O implementation satisfies H0
is not supplied by this theorem and is not a comparison-policy condition. -/
theorem referenceNative_policy (input : StatisticalInput I) (C : Contract I)
    (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceOriginalQualification input C hcurrent.1 accounting I.tools budget exponent) :
    ∃ policy : Policy input C .native accounting Unit,
      policy.rule = (referenceBoundedPolicy input C hcurrent.1 accounting I.tools budget exponent).rule ∧
      risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
      expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
        expectedBill input C .uncapped accounting
          (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) :=
  referenceNative_policy_of_referenceRisk input C hcurrent accounting
    (referenceRiskGuarantee input C accounting) delta hd hsmall exponent budget choice qualification

theorem native_value_le_reference_ideal (input : StatisticalInput I)
    (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceOriginalQualification input C hcurrent.1 accounting I.tools budget exponent) :
    value input C .native accounting (ENNReal.ofReal delta) ≤
      expectedBill input C .uncapped accounting
        (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) :=
  native_value_le_reference_ideal_of_referenceRisk input C hcurrent accounting
    (referenceRiskGuarantee input C accounting) delta hd hsmall exponent budget choice qualification

end PaperProofs.Common.Native
