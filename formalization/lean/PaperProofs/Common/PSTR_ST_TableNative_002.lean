module

public import PaperProofs.Common.PSTR_ST_Table_001

/-!
Uniform, pathwise observation bounds for the unchanged quota-truncated
reference rule. The review gate is proved directly from finite visible
history. No review certificate is assumed as a Policy field or hypothesis.
The bounds include zero quotas, threshold hits at the quota, abort prefixes,
and every truth/tape with an arbitrary seed universe.
-/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics

open PaperProofs.Statistics
open CompactPrice

variable {I : Instance}

theorem tableRule_uncapped_legal (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (limit : ReferenceObservationLimit I) :
    LegalRule input C .uncapped accounting (tableRule input available budget limit) := by
  intro seed truth tapes n s hp hactive
  let action := tableCandidate input available budget limit s.history
  by_cases hallow : historyAllowsAction s.history action
  · have hnext := historyAllowsAction_sound input C hearly accounting
      (tableRule input available budget limit) seed truth tapes hp hactive action hallow
    simpa only [tableRule, action, ite_eq_left hallow] using hnext
  · have hnext : Step input C .uncapped accounting tapes s .abandon (stopState s true) := .abandon s hactive
    exact ⟨_, by simpa only [tableRule, action, ite_eq_right hallow] using hnext⟩

def tableUncappedPolicy (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (limit : ReferenceObservationLimit I) : Policy input C .uncapped accounting Unit where
  rule := tableRule input available budget limit
  measurable_rule :=
    (measurable_of_countable (fun history => tableRule input available budget limit () history)).comp measurable_snd
  legal := tableRule_uncapped_legal input C hearly accounting available budget limit

theorem tableTestingAction_supported (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (cache : ReferenceReplayCache I) (stage : I.Stage) :
    tableTestingAction input initialAvailable risk limit cache stage = .review stage ∨
      (∃ bit, tableTestingAction input initialAvailable risk limit cache stage = .write stage bit) ∨
      tableTestingAction input initialAvailable risk limit cache stage = .abandon := by
  cases hk : tableKind I initialAvailable cache with
  | none =>
    simp only [tableTestingAction, hk]
    exact Or.inr (Or.inr trivial)
  | some kind =>
    cases kind with
    | infiniteRank =>
      simp only [tableTestingAction, hk]
      exact Or.inr (Or.inl ⟨false, rfl⟩)
    | noTool | finiteBad depth =>
      cases ht : tableTarget I initialAvailable risk cache with
      | none =>
        simp only [tableTestingAction, hk, ht]
        exact Or.inr (Or.inr trivial)
      | some target =>
        by_cases hv : ∀ symbol ∈ historyObservations cache.seen stage,
            symbol < (input.experiment stage).alphabetSize
        · simp only [tableTestingAction, hk, ht, dite_eq_left hv]
          by_cases hh : (input.experiment stage).rationalWordHits target
              (historyObservationWord input cache.seen stage hv) = true
          · simp only [ite_eq_left hh]
            exact Or.inr (Or.inl ⟨_, rfl⟩)
          · simp only [ite_eq_right hh]
            cases limit with
            | none => exact Or.inl rfl
            | some quota =>
              dsimp only
              by_cases hq : (historyObservations cache.seen stage).length < quota stage
              · simp only [ite_eq_left hq]; exact Or.inl trivial
              · simp only [ite_eq_right hq]; exact Or.inr (Or.inr trivial)
        · simp only [tableTestingAction, hk, ht, dite_eq_right hv]
          exact Or.inr (Or.inr trivial)

/-- A testing review is possible only strictly below its original quota.
The inclusive threshold check occurs before this gate in the actual rule. -/
theorem tableTestingAction_review_lt_quota (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (cache : ReferenceReplayCache I) (stage : I.Stage)
    (haction : tableTestingAction input initialAvailable budget (some quota) cache stage = .review stage) :
    (historyObservations cache.seen stage).length < quota stage := by
  cases hk : tableKind I initialAvailable cache with
  | none => simp [tableTestingAction, hk] at haction
  | some kind =>
    cases kind with
    | infiniteRank => simp [tableTestingAction, hk] at haction
    | noTool | finiteBad depth =>
      cases ht : tableTarget I initialAvailable budget cache with
      | none => simp [tableTestingAction, hk, ht] at haction
      | some target =>
        by_cases hv : ∀ symbol ∈ historyObservations cache.seen stage,
            symbol < (input.experiment stage).alphabetSize
        · simp only [tableTestingAction, hk, ht, dite_eq_left hv] at haction
          by_cases hh : (input.experiment stage).rationalWordHits target
              (historyObservationWord input cache.seen stage hv) = true
          · rw [ite_eq_left hh] at haction
            cases haction
          · rw [ite_eq_right hh] at haction
            by_cases hq : (historyObservations cache.seen stage).length < quota stage
            · exact hq
            · simp only [hq, ite_false] at haction
              cases haction
        · simp only [tableTestingAction, hk, ht, dite_eq_right hv] at haction
          cases haction

theorem tableCandidate_review_lt_quota (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (history : List (VisibleEvent I)) (stage : I.Stage)
    (haction : tableCandidate input initialAvailable budget (some quota) history = .review stage) :
    (historyObservations history stage).length < quota stage := by
  cases hp : tableReplay input initialAvailable budget history with
  | none => simp [tableCandidate, hp] at haction
  | some cache =>
    have hseen := (tableReplay_some_spec input initialAvailable budget history cache hp).2.2.2.2.2
    cases hh : cache.halted with
    | true => simp [tableCandidate, hp, hh] at haction
    | false =>
      cases hs : referenceReplayStage I cache with
      | none =>
        simp only [tableCandidate, hp, hh, Bool.false_eq_true, ite_false, hs] at haction
        split_ifs at haction
      | some currentStage =>
        cases hphase : cache.phase with
        | testing =>
          have ht : tableTestingAction input initialAvailable budget (some quota) cache currentStage = .review stage := by
            simpa only [tableCandidate, hp, hh, Bool.false_eq_true, ite_false, hs, hphase] using haction
          rcases tableTestingAction_supported input initialAvailable budget (some quota) cache currentStage with
            hreview | ⟨bit, hwrite⟩ | habandon
          · have heq : currentStage = stage := Action.review.inj (hreview.symm.trans ht)
            subst currentStage
            rw [← hseen]
            exact tableTestingAction_review_lt_quota input initialAvailable budget quota cache stage ht
          · rw [hwrite] at ht
            cases ht
          · rw [habandon] at ht
            cases ht
        | written | executed tool => simp [tableCandidate, hp, hh, hs, hphase] at haction
        | allocated tool =>
          cases hv : referenceVisibleHandle history currentStage <;>
            simp [tableCandidate, hp, hh, hs, hphase, hv] at haction
        | reported =>
          cases hc : referenceReplayCorrect cache currentStage with
          | true => simp [tableCandidate, hp, hh, hs, hphase, hc] at haction
          | false =>
            cases hr : referenceReplayRisk budget cache with
            | none => simp [tableCandidate, hp, hh, hs, hphase, hc, hr] at haction
            | some current =>
              cases hv : referenceVisibleHandle history currentStage with
              | none => simp [tableCandidate, hp, hh, hs, hphase, hc, hr, hv] at haction
              | some handle =>
                cases ht : (tableReply I initialAvailable currentStage (historyUsed cache.entryHistory)).tool <;>
                  simp [tableCandidate, hp, hh, hs, hphase, hc, hr, hv, ht] at haction

/-- This implication holds for every finite history, including malformed
ones. The visible fallback abandonment cannot introduce another review. -/
theorem tableRule_review_lt_quota  (input : StatisticalInput I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (seed : Unit) (history : List (VisibleEvent I)) (stage : I.Stage)
    (haction : tableRule input initialAvailable budget (some quota) seed history = .review stage) :
    (historyObservations history stage).length < quota stage := by
  by_cases hallow : historyAllowsAction history (tableCandidate input initialAvailable budget (some quota) history)
  · have ha : tableCandidate input initialAvailable budget (some quota) history = .review stage := by
      simpa only [tableRule, ite_eq_left hallow] using haction
    exact tableCandidate_review_lt_quota input initialAvailable budget quota history stage ha
  · simp only [tableRule, ite_eq_right hallow] at haction
    cases haction

private theorem reportedWrite_reviews (C : Contract I) (s : State I) (stage : I.Stage) (bit : Bool) :
    (reportedWriteLedger C s stage bit).reviews = s.ledger.reviews := by
  classical
  simp only [reportedWriteLedger]
  split_ifs <;> rfl

/-- Actual bounded-reference prefixes obey their quota on every path.
No validity restriction on the budget or availability set is needed. -/
theorem prefix_tableRule_reviews_le_quota  (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ)
    (seed : Unit) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting (tableRule input initialAvailable budget (some quota)) seed truth tapes n s) :
    ∀ stage : I.Stage, s.ledger.reviews stage ≤ (quota stage : ℕ∞) := by
  induction hp with
  | initial => intro stage; exact bot_le
  | @next n s result earlier step ih =>
    generalize haction : tableRule input initialAvailable budget (some quota) seed s.history = action at step
    cases step with
    | review current live port resources =>
      have hgate := tableRule_review_lt_quota input initialAvailable budget quota seed s.history current haction
      intro stage
      by_cases heq : stage = current
      · subst stage
        simp only [record, reviewLedger, Function.update_self]
        rw [← prefix_historyObservations_length input C mode accounting
          (tableRule input initialAvailable budget (some quota)) seed truth tapes earlier current]
        exact_mod_cast Nat.succ_le_of_lt hgate
      · simpa only [record, reviewLedger, Function.update_of_ne heq] using ih stage
    | write current bit live port resources =>
      intro stage
      simpa only [record, reportedWrite_reviews] using ih stage
    | allocate | execute | advance | stop | abandon => exact ih

/-- The original sample-space quota certificate is derived from the actual
rule and Prefix theorem; it is not required as a legality assumption. -/
theorem tableRule_reviewQuotaCertificate  (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (initialAvailable : Finset I.Tool) (budget : ℚ) (quota : I.Stage → ℕ) :
    ReviewQuotaCertificate input C accounting
      (tableRule  input initialAvailable budget (some quota)) quota := by
  intro sample n stage
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting
    (tableRule  input initialAvailable budget (some quota))
    (tableRule_uncapped_legal input C hearly accounting initialAvailable budget (some quota)) sample n
  exact prefix_tableRule_reviews_le_quota input C .uncapped accounting initialAvailable budget quota
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage

theorem tableRule_halted (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (quota : I.Stage → ℕ) (sample : Unit × input.World) :
    (run input C .uncapped accounting (tableRule input available budget (some quota))
      sample (quotaActionBound I quota + 1)).halted = true :=
  run_halted_of_reviewQuotaCertificate input C accounting _
    (tableRule_uncapped_legal input C hearly accounting available budget (some quota)) quota
    (tableRule_reviewQuotaCertificate input C hearly accounting available budget quota) sample

theorem tableRule_normalCalls_iff_completed
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (quota : I.Stage → ℕ) (H0 : ℕ) :
    NormalCallCertificate input C .uncapped accounting
      (tableUncappedPolicy input C hearly accounting available budget (some quota)) H0 ↔
    CompletedNormalCallBound input C .uncapped accounting
      (tableRule input available budget (some quota)) H0 := by
  apply normalCallCertificate_iff_completed_of_halts
  intro sample
  exact ⟨_, tableRule_halted input C hearly accounting available budget quota sample⟩

/-- Original numeric caps plus complete-H0 for THIS table tie imply a native
policy with the identical table rule/run and all-prefix original cap bounds.
No statistical performance or physical implementation claim is assumed. -/
theorem tableNativeImplementation (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (exponent : ℕ)
    (qualification : OriginalQualification input C accounting available budget exponent) :
    ∃ policy : Policy input C .native accounting Unit,
      policy.rule = tableRule input available budget (some (referenceQuota input exponent)) ∧
      (∀ sample clock, run input C .native accounting policy.rule sample clock =
        run input C .uncapped accounting (tableRule input available budget (some (referenceQuota input exponent))) sample clock) ∧
      (∀ sample clock, (run input C .native accounting policy.rule sample clock).ledger.obeysCaps C ∧
        (run input C .native accounting policy.rule sample clock).ledger.normalCalls ≤ (C.normalCallBound : ℕ∞)) := by
  let source := tableUncappedPolicy input C hearly accounting available budget (some (referenceQuota input exponent))
  have reviews := tableRule_reviewQuotaCertificate input C hearly accounting available budget (referenceQuota input exponent)
  have normal : NormalCallCertificate input C .uncapped accounting source C.normalCallBound :=
    (tableRule_normalCalls_iff_completed input C hearly accounting available budget
      (referenceQuota input exponent) C.normalCallBound).mpr qualification.normal_completed
  let native := source.enforceCaps input C accounting (referenceQuota input exponent)
    reviews normal qualification.stage_quota qualification.total_calls
  have hrun := enforceCaps_run_eq input C accounting source (referenceQuota input exponent)
    reviews normal qualification.stage_quota qualification.total_calls
  refine ⟨native, rfl, hrun, ?_⟩
  intro sample clock
  refine ⟨run_native_obeysCaps input C accounting native.rule native.legal sample clock, ?_⟩
  rw [hrun]
  exact normal sample clock

end PaperProofs.Common.Native.PSTRStatistics

