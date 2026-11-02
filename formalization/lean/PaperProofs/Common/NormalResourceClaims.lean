module

public import PaperProofs.Common.BoundedNormalIO

/-!
The ORIGINAL normal-resource assumptions of frozen model.tex:35--55 and
price-proofs.tex:277--292.  H0 is supplied as a bound for the selected
controller's complete executions, exactly as the source says.  It is not
deduced from an arbitrary accounting function, inserted into comparison
policy legality, or replaced by zero accounting.

The source does not specify a platform adapter or per-action normal-call
prices.  Such an adapter is an implementation obligation if a concrete
platform is later selected, not an extra mathematical theorem asserted by
the manuscript.  All resource conclusions below refer to the original
accounting function and original numeric caps.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace PaperProofs.Common.Native

universe u

variable {I : Instance}

/-- General M08 native-run part: all real prefixes, every seed universe,
including failed and incomplete paths.  H0 is not a comparator cap. -/
def NativeRunResourceClaims (input : StatisticalInput I) : Prop :=
  ∀ (Seed : Type u) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed), LegalRule input C .native accounting rule →
      ∀ (sample : Seed × input.World) (n : ℕ),
        LedgerWellFormed (run input C .native accounting rule sample n).ledger ∧
        FiniteCounters (run input C .native accounting rule sample n).ledger ∧
        (run input C .native accounting rule sample n).ledger.obeysCaps C ∧
        (run input C .native accounting rule sample n).ledger.executions.length ≤
          min I.stageCount I.toolCount

/-- Only the three original sufficient resource assumptions.  The third is
the source's complete-execution H0 premise for THIS fixed bounded script;
review bounds and native legality are conclusions, not premise fields. -/
structure ReferenceCompleteOriginalQualification (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ) : Prop where
  stage_quota : ∀ stage, referenceQuota input exponent stage ≤ C.reviewQuota stage
  total_calls : C.normalCallBound + ∑ stage, referenceQuota input exponent stage +
    min I.stageCount I.toolCount ≤ C.totalCallCap
  normal_calls_completed : CompletedNormalCallBound input C .uncapped accounting
    (referenceBoundedPolicy input C hearly accounting available budget exponent).rule C.normalCallBound

/-- The existing all-prefix qualification is exactly the manuscript's
complete-execution qualification, because the actual bounded script halts
on every path.  This does not posit a new normal-I/O upper bound. -/
theorem referenceCompleteOriginalQualification_iff
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ) :
    ReferenceCompleteOriginalQualification input C hearly accounting available budget exponent ↔
      ReferenceOriginalQualification input C hearly accounting available budget exponent := by
  constructor
  · intro h
    exact ⟨h.stage_quota, h.total_calls,
      (referenceBounded_normalCalls_iff_completed input C hearly accounting available budget exponent
        C.normalCallBound).mpr h.normal_calls_completed⟩
  · intro h
    exact ⟨h.stage_quota, h.total_calls,
      (referenceBounded_normalCalls_iff_completed input C hearly accounting available budget exponent
        C.normalCallBound).mp h.normal_calls⟩

/-- Selected-controller M08: the original complete-H0 assumption and numeric
caps produce an actual native policy with the SAME rule and entire run.
Its all-prefix normal H0, review quotas, total H and ledger bounds are
conclusions. No native policy, all-prefix H0, or successful-path premise is
assumed in this statement. -/
def ReferenceCompleteResourceClaims (input : StatisticalInput I) : Prop :=
  ∀ (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (exponent : ℕ),
    0 < budget → budget ≤ 1 / 2 →
    ReferenceCompleteOriginalQualification input C hearly accounting available budget exponent →
      ∃ policy : Policy input C .native accounting Unit,
        policy.rule = (referenceBoundedPolicy input C hearly accounting available budget exponent).rule ∧
        (∀ sample n, run input C .native accounting policy.rule sample n =
          run input C .uncapped accounting
            (referenceBoundedPolicy input C hearly accounting available budget exponent).rule sample n) ∧
        NormalCallCertificate input C .native accounting policy C.normalCallBound ∧
        ∀ sample n,
          LedgerWellFormed (run input C .native accounting policy.rule sample n).ledger ∧
          FiniteCounters (run input C .native accounting policy.rule sample n).ledger ∧
          (run input C .native accounting policy.rule sample n).ledger.obeysCaps C ∧
          (run input C .native accounting policy.rule sample n).ledger.executions.length ≤
            min I.stageCount I.toolCount

def NormalResourceClaims (input : StatisticalInput I) : Prop :=
  NativeRunResourceClaims.{u} input ∧ ReferenceCompleteResourceClaims input

theorem nativeRunResourceClaims (input : StatisticalInput I) : NativeRunResourceClaims.{u} input := by
  intro Seed C accounting rule hlegal sample n
  exact ⟨run_ledgerWellFormed input C .native accounting rule hlegal sample n,
    run_finiteCounters input C .native accounting rule hlegal sample n,
    run_native_obeysCaps input C accounting rule hlegal sample n,
    run_actualCorrections_le input C .native accounting rule hlegal sample n⟩

theorem referenceCompleteResourceClaims (input : StatisticalInput I) : ReferenceCompleteResourceClaims input := by
  intro C hearly accounting available budget exponent hbudget hsmall hcomplete
  have hq := (referenceCompleteOriginalQualification_iff input C hearly accounting available budget exponent).mp hcomplete
  obtain ⟨policy, hrule, hrun⟩ := referenceNativeImplementation input C hearly accounting available budget exponent
    hbudget hsmall hq
  refine ⟨policy, hrule, hrun, ?_, ?_⟩
  · intro sample n
    rw [hrun]
    exact hq.normal_calls sample n
  · exact nativeRunResourceClaims input Unit C accounting policy.rule policy.legal

theorem normalResourceClaims (input : StatisticalInput I) : NormalResourceClaims.{u} input :=
  ⟨nativeRunResourceClaims input, referenceCompleteResourceClaims input⟩

end PaperProofs.Common.Native
