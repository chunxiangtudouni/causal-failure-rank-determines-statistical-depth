module

public import PaperProofs.Common.ReferenceControllerPreservation

/-!
Uniform, pathwise observation bounds for the unchanged quota-truncated
reference rule. The review gate is proved directly from finite visible
history. No review certificate is assumed as a Policy field or hypothesis.
The bounds include zero quotas, threshold hits at the quota, abort prefixes,
and every truth/tape with an arbitrary seed universe.
-/

@[expose] public section

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

/-- A testing review is possible only strictly below its original quota.
The inclusive threshold check occurs before this gate in the actual rule. -/
theorem referenceTestingAction_review_lt_quota (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (cache : ReferenceReplayCache I) (stage : I.Stage)
    (haction : referenceTestingAction input initialAvailable budget (some quota) cache stage = .review stage) :
    (historyObservations cache.seen stage).length < quota stage := by
  cases hk : referenceAvailableKind I initialAvailable cache with
  | none => simp [referenceTestingAction, hk] at haction
  | some kind =>
    cases kind with
    | infiniteRank => simp [referenceTestingAction, hk] at haction
    | noTool | finiteBad depth =>
      cases ht : referenceAvailableCacheTarget I initialAvailable budget cache with
      | none => simp [referenceTestingAction, hk, ht] at haction
      | some target =>
        by_cases hv : ∀ symbol ∈ historyObservations cache.seen stage,
            symbol < (input.experiment stage).alphabetSize
        · simp only [referenceTestingAction, hk, ht, dite_eq_left hv] at haction
          by_cases hh : (input.experiment stage).rationalWordHits target
              (historyObservationWord input cache.seen stage hv) = true
          · rw [ite_eq_left hh] at haction
            cases haction
          · rw [ite_eq_right hh] at haction
            by_cases hq : (historyObservations cache.seen stage).length < quota stage
            · exact hq
            · simp only [hq, ite_false] at haction
              cases haction
        · simp only [referenceTestingAction, hk, ht, dite_eq_right hv] at haction
          cases haction

theorem referenceCandidateAction_review_lt_quota (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (history : List (VisibleEvent I)) (stage : I.Stage)
    (haction : referenceCandidateAction input initialAvailable budget (some quota) history = .review stage) :
    (historyObservations history stage).length < quota stage := by
  cases hp : referenceAvailableReplay input initialAvailable budget history with
  | none => simp [referenceCandidateAction, hp] at haction
  | some cache =>
    have hseen := (referenceAvailableReplay_some_spec input initialAvailable budget history cache hp).2.2.2.2.2
    cases hh : cache.halted with
    | true => simp [referenceCandidateAction, hp, hh] at haction
    | false =>
      cases hs : referenceReplayStage I cache with
      | none =>
        simp only [referenceCandidateAction, hp, hh, Bool.false_eq_true, ite_false, hs] at haction
        split_ifs at haction
      | some currentStage =>
        cases hphase : cache.phase with
        | testing =>
          have ht : referenceTestingAction input initialAvailable budget (some quota) cache currentStage = .review stage := by
            simpa only [referenceCandidateAction, hp, hh, Bool.false_eq_true, ite_false, hs, hphase] using haction
          rcases referenceTestingAction_supported input initialAvailable budget (some quota) cache currentStage with
            hreview | ⟨bit, hwrite⟩ | habandon
          · have heq : currentStage = stage := Action.review.inj (hreview.symm.trans ht)
            subst currentStage
            rw [← hseen]
            exact referenceTestingAction_review_lt_quota input initialAvailable budget quota cache stage ht
          · rw [hwrite] at ht
            cases ht
          · rw [habandon] at ht
            cases ht
        | written | executed tool => simp [referenceCandidateAction, hp, hh, hs, hphase] at haction
        | allocated tool =>
          cases hv : referenceVisibleHandle history currentStage <;>
            simp [referenceCandidateAction, hp, hh, hs, hphase, hv] at haction
        | reported =>
          cases hc : referenceReplayCorrect cache currentStage with
          | true => simp [referenceCandidateAction, hp, hh, hs, hphase, hc] at haction
          | false =>
            cases hr : referenceReplayRisk budget cache with
            | none => simp [referenceCandidateAction, hp, hh, hs, hphase, hc, hr] at haction
            | some current =>
              cases hv : referenceVisibleHandle history currentStage with
              | none => simp [referenceCandidateAction, hp, hh, hs, hphase, hc, hr, hv] at haction
              | some handle =>
                cases ht : referenceAvailableRepairTool I initialAvailable currentStage (historyUsed cache.entryHistory) <;>
                  simp [referenceCandidateAction, hp, hh, hs, hphase, hc, hr, hv, ht] at haction

/-- This implication holds for every finite history, including malformed
ones. The visible fallback abandonment cannot introduce another review. -/
theorem referenceRule_review_lt_quota {Seed : Type*} (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (seed : Seed) (history : List (VisibleEvent I)) (stage : I.Stage)
    (haction : referenceRule input initialAvailable budget (some quota) seed history = .review stage) :
    (historyObservations history stage).length < quota stage := by
  by_cases hallow : historyAllowsAction history (referenceCandidateAction input initialAvailable budget (some quota) history)
  · have ha : referenceCandidateAction input initialAvailable budget (some quota) history = .review stage := by
      simpa only [referenceRule, ite_eq_left hallow] using haction
    exact referenceCandidateAction_review_lt_quota input initialAvailable budget quota history stage ha
  · simp only [referenceRule, ite_eq_right hallow] at haction
    cases haction

private theorem reportedWrite_reviews (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- Actual bounded-reference prefixes obey their quota on every path.
No validity restriction on the budget or availability set is needed. -/
theorem prefix_referenceRule_reviews_le_quota {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting (referenceRule input initialAvailable budget (some quota)) seed truth tapes n s) :
    ∀ stage : I.Stage, s.ledger.reviews stage ≤ (quota stage : ℕ∞) := by
  induction hp with
  | initial => intro stage; exact bot_le
  | @next n s result earlier step ih =>
    generalize haction : referenceRule input initialAvailable budget (some quota) seed s.history = action at step
    cases step with
    | review current live port resources =>
      have hgate := referenceRule_review_lt_quota input initialAvailable budget quota seed s.history current haction
      intro stage
      by_cases heq : stage = current
      · subst stage
        simp only [record, reviewLedger, Function.update_self]
        rw [← prefix_historyObservations_length input C mode accounting
          (referenceRule input initialAvailable budget (some quota)) seed truth tapes earlier current]
        exact_mod_cast Nat.succ_le_of_lt hgate
      · simpa only [record, reviewLedger, Function.update_of_ne heq] using ih stage
    | write current bit live port resources =>
      intro stage
      simpa only [record, reportedWrite_reviews] using ih stage
    | allocate | execute | advance | stop | abandon => exact ih

/-- The original sample-space quota certificate is derived from the actual
rule and Prefix theorem; it is not required as a legality assumption. -/
theorem referenceRule_reviewQuotaCertificate {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ) :
    ReviewQuotaCertificate input C accounting
      (referenceRule (Seed := Seed) input initialAvailable budget (some quota)) quota := by
  intro sample n stage
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting
    (referenceRule (Seed := Seed) input initialAvailable budget (some quota))
    (referenceRule_uncapped_legal input C hearly accounting initialAvailable budget (some quota)) sample n
  exact prefix_referenceRule_reviews_le_quota input C .uncapped accounting initialAvailable budget quota
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage

end PaperProofs.Common.Native
