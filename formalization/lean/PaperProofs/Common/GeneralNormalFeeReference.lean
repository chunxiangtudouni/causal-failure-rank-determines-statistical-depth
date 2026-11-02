module

public import PaperProofs.Common.NormalResourceClaims
public import PaperProofs.Common.NormalFeeClaims
public import PaperProofs.Common.ReferenceNativeRisk

/-!
The original M11 upper instantiated at the ACTUAL original-cap reference
controller, not at an unspecified safe witness.  The selected native policy
is the existing bounded script with caps enforced.  B22a proves its risk
and variable-cost bound; the source's complete-execution H0 and numeric
caps are its only resource qualification.  A general fixed universe-zero
fee family supplies its original normal-charge upper on this actual policy.
No fee transport across modes, seeds or representations is assumed.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.GeneralNormalFees

variable {I : Instance}

/-- Exact existing bounded-reference rule, with its proved review bound
and the ORIGINAL complete-execution H0 used to enforce ORIGINAL caps. -/
def completeNativeReferencePolicy (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ)
    (qualification : ReferenceCompleteOriginalQualification input C hearly accounting available budget exponent) :
    Policy input C .native accounting Unit :=
  let source := referenceBoundedPolicy input C hearly accounting available budget exponent
  let original := (referenceCompleteOriginalQualification_iff input C hearly accounting available budget exponent).mp qualification
  source.enforceCaps input C accounting (referenceQuota input exponent)
    (referenceRule_reviewQuotaCertificate input C hearly accounting available budget (referenceQuota input exponent))
    original.normal_calls original.stage_quota original.total_calls

theorem completeNativeReferencePolicy_rule (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ)
    (qualification : ReferenceCompleteOriginalQualification input C hearly accounting available budget exponent) :
    (completeNativeReferencePolicy input C hearly accounting available budget exponent qualification).rule =
      (referenceBoundedPolicy input C hearly accounting available budget exponent).rule := rfl

private theorem policy_eq_of_rule_eq {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (left right : Policy input C mode accounting Seed)
    (heq : left.rule = right.rule) : left = right := by
  cases left
  cases right
  cases heq
  rfl

/-- B22a's actual risk and variable-fee bound, for this explicitly selected
policy. Neither is an added input premise of the M11 fee assembly. -/
theorem completeNativeReferencePolicy_performance
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceCompleteOriginalQualification input C hcurrent.1 accounting I.tools budget exponent) :
    let policy := completeNativeReferencePolicy input C hcurrent.1 accounting I.tools budget exponent qualification
    risk input C .native accounting policy.rule (Measure.dirac ()) ≤ ENNReal.ofReal delta ∧
      expectedBill input C .native accounting policy.rule (Measure.dirac ()) ≤
        expectedBill input C .uncapped accounting
          (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) := by
  obtain ⟨policy, hrule, hsafe, hbill⟩ := referenceNative_policy input C hcurrent accounting
    delta hd hsmall exponent budget choice
    ((referenceCompleteOriginalQualification_iff input C hcurrent.1 accounting I.tools budget exponent).mp qualification)
  have heq : completeNativeReferencePolicy input C hcurrent.1 accounting I.tools budget exponent qualification = policy :=
    policy_eq_of_rule_eq input C .native accounting _ policy
      ((completeNativeReferencePolicy_rule input C hcurrent.1 accounting I.tools budget exponent qualification).trans hrule.symm)
  dsimp only
  rw [heq]
  exact ⟨hsafe, hbill⟩

/-- Full actual-controller M11 upper. The only normal-fee premise is the
source's bound on this actual constructed native execution. Family charges
need not factor through a public trace or be invariant under re-encoding. -/
theorem FeeFamily.totalNativeValue_le_referenceIdeal_add
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (delta : ℝ) (hd : 0 < delta) (hsmall : delta ≤ 1 / 2)
    (exponent : ℕ) (budget : ℚ) (choice : ReferenceRiskChoice I.stageCount delta exponent budget)
    (qualification : ReferenceCompleteOriginalQualification input C hcurrent.1 accounting I.tools budget exponent)
    (family : FeeFamily.{0} input C .native accounting) (C0 : ℝ≥0∞)
    (hcharge : ConstructedNormalChargeUpper input
      (family.charges Unit inferInstance
        (completeNativeReferencePolicy input C hcurrent.1 accounting I.tools budget exponent qualification)) C0) :
    family.totalValue input C .native accounting (ENNReal.ofReal delta) ≤
      expectedBill input C .uncapped accounting
        (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) + C0 := by
  have hperformance := completeNativeReferencePolicy_performance input C hcurrent accounting
    delta hd hsmall exponent budget choice qualification
  exact (family.totalValue_upper_of_constructed input C .native accounting (ENNReal.ofReal delta) C0
    (Measure.dirac ())
    (completeNativeReferencePolicy input C hcurrent.1 accounting I.tools budget exponent qualification)
    hperformance.1 hcharge).trans (add_le_add hperformance.2 le_rfl)

/-- Original complete normal-fee remark for the actual native reference.
SuccessLower and constructed C0 upper are exactly the two source normal-fee
assumptions. Safety and the variable comparison with ideal are conclusions
from the existing reference proofs, not hidden conditions in this target. -/
def ReferenceNormalFeeClaims (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (hcurrent : C.IsCurrentAllocation) (accounting : NormalAccounting I)
    (delta : ℝ), 0 < delta → delta ≤ 1 / 2 →
    ∀ (exponent : ℕ) (budget : ℚ) (_choice : ReferenceRiskChoice I.stageCount delta exponent budget)
      (qualification : ReferenceCompleteOriginalQualification input C hcurrent.1 accounting I.tools budget exponent)
      (family : FeeFamily.{0} input C .native accounting) (C0 : ℝ≥0∞),
      family.SuccessLower input C .native accounting C0 →
      ConstructedNormalChargeUpper input
        (family.charges Unit inferInstance
          (completeNativeReferencePolicy input C hcurrent.1 accounting I.tools budget exponent qualification)) C0 →
      (value input C .native accounting (ENNReal.ofReal delta) + (1 - ENNReal.ofReal delta) * C0 ≤
        family.totalValue input C .native accounting (ENNReal.ofReal delta)) ∧
      family.totalValue input C .native accounting (ENNReal.ofReal delta) ≤
        expectedBill input C .uncapped accounting
          (referenceIdealPolicy input C hcurrent.1 accounting I.tools budget).rule (Measure.dirac ()) + C0

theorem referenceNormalFeeClaims (input : StatisticalInput I) : ReferenceNormalFeeClaims input := by
  intro C hcurrent accounting delta hd hsmall exponent budget choice qualification family C0 hlower hcharge
  exact ⟨family.totalValue_lower input C .native accounting (ENNReal.ofReal delta) C0 hlower,
    family.totalNativeValue_le_referenceIdeal_add input C hcurrent accounting delta hd hsmall exponent budget
      choice qualification C0 hcharge⟩

end PaperProofs.Common.Native.GeneralNormalFees
