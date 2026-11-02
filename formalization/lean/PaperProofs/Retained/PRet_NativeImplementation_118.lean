module

public import PaperProofs.Retained.CompletedQualification
public import PaperProofs.Common.NativeCapTransfer

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetNativeImplementation118

open Common Common.Native

variable {I : Instance}

/-- Exact all-prefix resource field of the actual bounded retained script.
It does not assume successful completion or favorable returned actions. -/
theorem allPrefixBounds (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (exponent : ℕ) :
    ∀ sample n,
      (∀ stage, (run input C .uncapped accounting
        (boundedPolicy input C hretained accounting budget exponent).rule sample n).ledger.reviews stage ≤ referenceQuota input exponent stage) ∧
      (run input C .uncapped accounting (boundedPolicy input C hretained accounting budget exponent).rule sample n).ledger.executions.length ≤
        min I.stageCount I.toolCount := by
  intro sample n
  exact ⟨retainedRule_reviewQuotaCertificate input C hretained accounting budget (referenceQuota input exponent) sample n,
    run_actualCorrections_le input C .uncapped accounting _
      (boundedPolicy input C hretained accounting budget exponent).legal sample n⟩

/-- THIS bounded script under precisely its original H0/stage/total caps.
The normal-call certificate is neither weakened nor imposed on comparators. -/
def nativeBoundedPolicy (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (exponent : ℕ)
    (qualification : OriginalQualification input C hretained accounting budget exponent) : Policy input C .native accounting Unit :=
  (boundedPolicy input C hretained accounting budget exponent).enforceCaps input C accounting (referenceQuota input exponent)
    (retainedRule_reviewQuotaCertificate input C hretained accounting budget (referenceQuota input exponent))
    qualification.normal_calls qualification.stage_quota qualification.total_calls

theorem nativeBounded_run_eq (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (exponent : ℕ)
    (qualification : OriginalQualification input C hretained accounting budget exponent) (sample : Unit × input.World) (n : ℕ) :
    run input C .native accounting (nativeBoundedPolicy input C hretained accounting budget exponent qualification).rule sample n =
      run input C .uncapped accounting (boundedPolicy input C hretained accounting budget exponent).rule sample n :=
  enforceCaps_run_eq input C accounting (boundedPolicy input C hretained accounting budget exponent) (referenceQuota input exponent)
    (retainedRule_reviewQuotaCertificate input C hretained accounting budget (referenceQuota input exponent))
    qualification.normal_calls qualification.stage_quota qualification.total_calls sample n

theorem nativeImplementation (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (exponent : ℕ)
    (qualification : OriginalQualification input C hretained accounting budget exponent) :
    ∃ policy : Policy input C .native accounting Unit,
      policy.rule = (boundedPolicy input C hretained accounting budget exponent).rule ∧
      ∀ sample n, run input C .native accounting policy.rule sample n =
        run input C .uncapped accounting (boundedPolicy input C hretained accounting budget exponent).rule sample n :=
  ⟨nativeBoundedPolicy input C hretained accounting budget exponent qualification, rfl,
    nativeBounded_run_eq input C hretained accounting budget exponent qualification⟩

end PaperProofs.Retained.PRetNativeImplementation118
