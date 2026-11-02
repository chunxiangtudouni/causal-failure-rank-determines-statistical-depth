module

public import PaperProofs.Retained.Controller
public import PaperProofs.Common.BoundedNormalIO
public import PaperProofs.Common.ReferenceTermination

/-!
The original complete-execution H0 qualification of the actual retained
quota-bounded script is equivalent to its prefix H0 certificate. The quota
gate and finite returned-action termination are proved from the original retained
script with its terminal-permission guard, independently of risk, fees, normal accounting, success and H0.
-/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal BigOperators

namespace PaperProofs.Retained

open Common Common.Native Statistics

variable {I : Instance}

theorem retainedTestingAction_review_lt_quota (input : StatisticalInput I)
    (quota : I.Stage → ℕ) (history : List (VisibleEvent I)) (cache : BudgetCache I)
    (current stage : I.Stage)
    (haction : retainedTestingAction input (some quota) history cache current = .review stage) :
    current = stage ∧ (historyObservations history stage).length < quota stage := by
  cases hk : rankCase I current cache.errors with
  | none => simp [retainedTestingAction, hk] at haction
  | some kind =>
    cases kind with
    | infiniteRank => simp [retainedTestingAction, hk] at haction
    | noTool | finiteBad depth =>
      simp only [retainedTestingAction, hk, Option.bind_some, referenceBudgetTarget] at haction
      by_cases hv : ∀ symbol ∈ historyObservations history current,
          symbol < (input.experiment current).alphabetSize
      · rw [dite_eq_left hv] at haction
        split_ifs at haction with hh hq
        have heq := Action.review.inj haction
        subst stage
        exact ⟨rfl, hq⟩
      · rw [dite_eq_right hv] at haction
        cases haction

theorem terminalMatchingAction_ne_review (I : Instance) (history : List (VisibleEvent I))
    (stage : I.Stage) : terminalMatchingAction I history ≠ .review stage := by
  intro haction
  unfold terminalMatchingAction at haction
  dsimp only at haction
  split at haction
  · cases haction
  · split at haction
    · cases haction
    · split at haction
      · split at haction
        · cases haction
        · split_ifs at haction
      · cases haction

theorem retainedCandidate_review_lt_quota (input : StatisticalInput I) (budget : ℚ)
    (quota : I.Stage → ℕ) (history : List (VisibleEvent I)) (stage : I.Stage)
    (haction : retainedCandidate input budget (some quota) history = .review stage) :
    (historyObservations history stage).length < quota stage := by
  unfold retainedCandidate at haction
  split at haction
  · cases haction
  · split at haction
    · dsimp only at haction
      split at haction
      · cases haction
      · split at haction
        · cases haction
        · split at haction
          · exact (retainedTestingAction_review_lt_quota input quota history _ _ stage haction).2
          · split at haction
            · cases haction
            · split_ifs at haction
    · split_ifs at haction
      exact False.elim (terminalMatchingAction_ne_review I history stage haction)

theorem retainedRule_review_lt_quota (input : StatisticalInput I) (budget : ℚ)
    (quota : I.Stage → ℕ) (seed : Unit) (history : List (VisibleEvent I)) (stage : I.Stage)
    (haction : retainedRule input budget (some quota) seed history = .review stage) :
    (historyObservations history stage).length < quota stage := by
  by_cases hallow : PRetRetainedGuard007.allows history (retainedCandidate input budget (some quota) history)
  · exact retainedCandidate_review_lt_quota input budget quota history stage
      (by simpa only [retainedRule, PRetRetainedGuard007.guarded, ite_eq_left hallow] using haction)
  · simp only [retainedRule, PRetRetainedGuard007.guarded, ite_eq_right hallow] at haction
    cases haction

private theorem reportedWrite_reviews (C : Contract I) (s : State I)
    (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- The actual bounded retained script obeys every stage quota on every
reachable prefix, including failed and abandoned executions. -/
theorem prefix_retainedRule_reviews_le_quota (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (budget : ℚ) (quota : I.Stage → ℕ)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting (retainedRule input budget (some quota))
      seed truth tapes n s) :
    ∀ stage : I.Stage, s.ledger.reviews stage ≤ (quota stage : ℕ∞) := by
  induction hp with
  | initial => intro stage; exact bot_le
  | @next n s result earlier step ih =>
    generalize haction : retainedRule input budget (some quota) seed s.history = action at step
    cases step with
    | review current live port resources =>
      have hgate := retainedRule_review_lt_quota input budget quota seed s.history current haction
      intro stage
      by_cases heq : stage = current
      · subst stage
        simp only [record, reviewLedger, Function.update_self]
        rw [← prefix_historyObservations_length input C mode accounting
          (retainedRule input budget (some quota)) seed truth tapes earlier current]
        exact_mod_cast Nat.succ_le_of_lt hgate
      · simpa only [record, reviewLedger, Function.update_of_ne heq] using ih stage
    | write current bit live port resources =>
      intro stage
      simpa only [record, reportedWrite_reviews] using ih stage
    | allocate | execute | advance | stop | abandon => exact ih

theorem retainedRule_reviewQuotaCertificate (input : StatisticalInput I)
    (C : Contract I) (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (quota : I.Stage → ℕ) :
    ReviewQuotaCertificate input C accounting (retainedRule input budget (some quota)) quota := by
  intro sample n stage
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting
    (retainedRule input budget (some quota))
    (retainedRule_uncapped_legal input C hretained accounting budget (some quota)) sample n
  exact prefix_retainedRule_reviews_le_quota input C .uncapped accounting budget quota
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage

/-- Bounded retained runs halt after finitely many returned actions;
this is independent of risk, fees, budget validity and normal accounting. -/
theorem retainedBounded_halted (input : StatisticalInput I)
    (C : Contract I) (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (quota : I.Stage → ℕ) (sample : Unit × input.World) :
    (run input C .uncapped accounting (retainedRule input budget (some quota)) sample
      (quotaActionBound I quota + 1)).halted = true :=
  run_halted_of_reviewQuotaCertificate input C accounting _
    (retainedRule_uncapped_legal input C hretained accounting budget (some quota)) quota
    (retainedRule_reviewQuotaCertificate input C hretained accounting budget quota) sample

/-- This selected retained script needs only the original H0 bound on
complete executions; it is equivalent to the existing all-prefix field. -/
theorem retainedBounded_normalCalls_iff_completed (input : StatisticalInput I)
    (C : Contract I) (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (exponent H0 : ℕ) :
    NormalCallCertificate input C .uncapped accounting
      (boundedPolicy input C hretained accounting budget exponent) H0 ↔
    CompletedNormalCallBound input C .uncapped accounting
      (boundedPolicy input C hretained accounting budget exponent).rule H0 := by
  apply normalCallCertificate_iff_completed_of_halts
  intro sample
  exact ⟨_, retainedBounded_halted input C hretained accounting budget
    (referenceQuota input exponent) sample⟩

/-- Same numerical qualification as the original script, with H0 stated
only on complete executions. This is not imposed on comparison policies. -/
structure CompletedOriginalQualification (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (exponent : ℕ) : Prop where
  stage_quota : ∀ i, referenceQuota input exponent i ≤ C.reviewQuota i
  total_calls : C.normalCallBound + ∑ i, referenceQuota input exponent i +
    min I.stageCount I.toolCount ≤ C.totalCallCap
  normal_calls : CompletedNormalCallBound input C .uncapped accounting
    (boundedPolicy input C hretained accounting budget exponent).rule C.normalCallBound

theorem completedOriginalQualification_iff (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (exponent : ℕ) :
    CompletedOriginalQualification input C hretained accounting budget exponent ↔
      OriginalQualification input C hretained accounting budget exponent := by
  constructor
  · intro h
    exact ⟨h.stage_quota, h.total_calls,
      (retainedBounded_normalCalls_iff_completed input C hretained accounting budget exponent
        C.normalCallBound).mpr h.normal_calls⟩
  · intro h
    exact ⟨h.stage_quota, h.total_calls,
      (retainedBounded_normalCalls_iff_completed input C hretained accounting budget exponent
        C.normalCallBound).mp h.normal_calls⟩

end PaperProofs.Retained
