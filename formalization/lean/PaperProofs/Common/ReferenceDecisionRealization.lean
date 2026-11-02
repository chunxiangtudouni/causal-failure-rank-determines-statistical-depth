module

public import PaperProofs.Common.ReferenceOverflowRealization

/-!
Actual posterior-test writes and null infinite-review paths for the ideal reference
controller, retaining its original initial-available-set parameter. The
entry/testing induction is the same visible replay, with availability as
an explicit argument; no risk or termination conclusion is a Policy field.

The actual error inclusion and per-entry error bound are proved below.
The full finite-stage success/risk-budget induction, and consequently the
original ReferenceRiskGuarantee, are not claimed by this module.
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

theorem referenceAvailableCacheTarget_some_spec (I : Instance) (available : Finset I.Tool)
    (budget target : ℚ) (cache : ReferenceReplayCache I)
    (htarget : referenceAvailableCacheTarget I available budget cache = some target) :
    ∃ kind current, referenceAvailableKind I available cache = some kind ∧
      referenceReplayRisk budget cache = some current ∧ ReferenceBudgetValid current ∧
      cache.events.length ≤ I.stageCount ∧ referenceBudgetTarget kind current = some target := by
  cases hb : cache.halted || decide (cache.phase ≠ .testing) with
  | true => simp only [referenceAvailableCacheTarget, hb, ite_true] at htarget; cases htarget
  | false =>
    simp only [referenceAvailableCacheTarget, hb, Bool.false_eq_true, ite_false] at htarget
    obtain ⟨kind, hk, hrest⟩ := Option.bind_eq_some_iff.mp htarget
    obtain ⟨current, hc, hrest⟩ := Option.bind_eq_some_iff.mp hrest
    by_cases hv : 0 < current ∧ current ≤ 1 / 4 ∧ cache.events.length ≤ I.stageCount
    · rw [ite_eq_left hv] at hrest
      exact ⟨kind, current, hk, hc, ⟨hv.1, hv.2.1⟩, hv.2.2, hrest⟩
    · rw [ite_eq_right hv] at hrest
      cases hrest

theorem referenceAvailableEntryTarget_valid (input : StatisticalInput I) (available : Finset I.Tool)
    (budget p : ℚ) (history : List (VisibleEvent I))
    (htarget : referenceAvailableEntryTarget input available budget history = some p) : 0 < p ∧ p ≤ 1 / 4 := by
  obtain ⟨cache, _, ht⟩ := Option.bind_eq_some_iff.mp htarget
  obtain ⟨kind, current, _, _, hv, _, hb⟩ := referenceAvailableCacheTarget_some_spec I available budget p cache ht
  have hp := referenceBudgetTarget_valid_floor kind current p hv hb
  exact ⟨hp.1, hp.2.1⟩
private def ReplayEventShape (cache next : ReferenceReplayCache I) (event : VisibleEvent I) : Prop :=
  match event with
  | .observation stage symbol => cache.phase = .testing ∧
      next = {cache with seen := cache.seen ++ [.observation stage symbol]}
  | .wrote _ _ _ => next.phase = .written
  | .report _ _ _ => next.phase = .reported
  | .committed _ tool => next.phase = .allocated tool
  | .executed _ tool => next.phase = .executed tool
  | .advanced stage => next = {cache with
      seen := cache.seen ++ [.advanced stage]
      entryHistory := cache.seen ++ [.advanced stage]
      phase := .testing}
  | .stopped | .abandoned => next.halted = true

private theorem some_if_some {α : Type*} (P : Prop) [Decidable P] (value next : α)
    (h : (if P then some value else none) = some next) : P ∧ next = value := by
  by_cases hp : P
  · rw [ite_eq_left hp] at h
    exact ⟨hp, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hp] at h
    cases h

private theorem replay_event_shape (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hstep : referenceAvailableStep input available budget cache event = some next) :
    ReplayEventShape cache next event := by
  cases hh : cache.halted with
  | true => simp only [referenceAvailableStep, hh, ite_true] at hstep; cases hstep
  | false =>
    cases event with
    | observation stage symbol =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      exact ⟨hg.2.2.1, by simpa only [hh] using he⟩
    | wrote stage bit serial =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl
    | report stage truth serial =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl
    | committed handle tool =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl
    | executed handle tool =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl
    | advanced stage =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      simpa only [ReplayEventShape, hh] using he
    | stopped | abandoned =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl

private theorem replay_packet_after (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history packet : List (VisibleEvent I)) (cache next : ReferenceReplayCache I)
    (hparse : referenceAvailableReplay input available budget history = some cache)
    (hnext : referenceAvailableReplay input available budget (history ++ packet) = some next) :
    packet.foldlM (referenceAvailableStep input available budget) cache = some next := by
  have hs := referenceAvailableReplay_some_spec input available budget history cache hparse
  have hs' := referenceAvailableReplay_some_spec input available budget (history ++ packet) next hnext
  rw [List.foldlM_append, hs.2.1] at hs'
  simpa using hs'.2.1

private theorem replay_single_after (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hparse : referenceAvailableReplay input available budget history = some cache)
    (hnext : referenceAvailableReplay input available budget (history ++ [event]) = some next) :
    referenceAvailableStep input available budget cache event = some next := by
  simpa using replay_packet_after input available budget history [event] cache next hparse hnext

private theorem prefix_eq_run_sample {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) n s) : run input C .uncapped accounting rule sample n = s := by
  have he := prefix_eq_run input C .uncapped accounting rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hw : replayWorld input (input.truthAt sample.2) (worldTapes input sample.2) = sample.2 := by
    funext stage
    exact Prod.eta _
  simpa only [hw] using he

private theorem cacheTarget_bounds (I : Instance) (available : Finset I.Tool) (budget p : ℚ) (cache : ReferenceReplayCache I)
    (ht : referenceAvailableCacheTarget I available budget cache = some p) : 0 < p ∧ p < 1 := by
  obtain ⟨kind, current, _, _, hv, _, htarget⟩ := referenceAvailableCacheTarget_some_spec I available budget p cache ht
  have hb := referenceBudgetTarget_valid_floor kind current p hv htarget
  exact ⟨hb.1, lt_of_le_of_lt hb.2.1 (by norm_num)⟩
private theorem natCast_succ_le_of_lt (r : ℕ) (T : ℕ∞) (h : (r : ℕ∞) < T) : ((r + 1 : ℕ) : ℕ∞) ≤ T := by
  cases T using ENat.recTopCoe with
  | top => exact le_top
  | coe t => exact ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp h))

/-- The induction's first-exit lower bound becomes strict when the actual
ideal controller requests another review. The lower bound is propagated
from birth and previous real reviews below, not postulated globally. -/
private theorem review_stop_strict {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget none) seed truth tapes n s)
    (cache : ReferenceReplayCache I) (haligned : ReferenceStateAligned input available budget cache s)
    (hphase : cache.phase = .testing) (hactive : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (p : ℚ) (htarget : referenceAvailableCacheTarget I available budget cache = some p)
    (haction : referenceRule input available budget none seed s.history = .review stage)
    (hbefore : s.ledger.reviews stage ≤ (input.experiment stage).posteriorThresholdStop p (tapes stage)) :
    s.ledger.reviews stage < (input.experiment stage).posteriorThresholdStop p (tapes stage) := by
  have htesting := referenceRule_testing_eq_of_aligned input C accounting available budget none seed truth tapes
    hp hactive cache haligned hphase stage hcursor
  have htest : referenceTestingAction input available budget none cache stage = .review stage := htesting.symm.trans haction
  obtain ⟨q, hq, hnonhit⟩ := referenceTestingAction_review_nonhit input available budget none cache stage htest
  have heq : q = p := Option.some.inj (hq.symm.trans htarget)
  subst q
  have hvalid : ∀ symbol ∈ historyObservations s.history stage, symbol < (input.experiment stage).alphabetSize :=
    fun symbol hm => prefix_historyObservation_alphabet input C .uncapped accounting
      (referenceRule input available budget none) seed truth tapes hp stage symbol hm
  have hvalidCache : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize := by
    simpa only [haligned.seen] using hvalid
  have hfalse : (input.experiment stage).rationalWordHits p (historyObservationWord input s.history stage hvalid) = false := by
    simpa only [haligned.seen] using hnonhit hvalidCache
  have hb := cacheTarget_bounds I available budget p cache htarget
  have hiff := prefix_historyObservationWord_hits_iff input C .uncapped accounting
    (referenceRule input available budget none) seed truth tapes hp stage hvalid p hb.1 hb.2
  apply lt_of_le_of_ne hbefore
  intro he
  have hfinite := prefix_reviews_natCast_toNat input C .uncapped accounting
    (referenceRule input available budget none) seed truth tapes hp stage
  have ht : (input.experiment stage).posteriorThresholdStop p (tapes stage) = ((s.ledger.reviews stage).toNat : ℕ∞) :=
    he.symm.trans hfinite.symm
  have hh := hiff.mpr ((input.experiment stage).posteriorThresholdStop_hits p (tapes stage) _ ht)
  rw [hfalse] at hh
  cases hh

private def TestingOrigin {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (sample : Seed × input.World)
    (cache : ReferenceReplayCache I) (s : State I) (stage : I.Stage) : Prop :=
  ∃ history : List (VisibleEvent I),
    entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history ∧
    cache.entryHistory = history ∧
    referenceAvailableEntryTarget input available budget history = referenceAvailableCacheTarget I available budget cache ∧
    ∀ p : ℚ, referenceAvailableCacheTarget I available budget cache = some p →
      s.ledger.reviews stage ≤ (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2

private theorem entryHistory_at_increment {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (n : ℕ) (old next : State I) (stage : I.Stage)
    (hold : run input C .uncapped accounting rule sample n = old)
    (hnext : run input C .uncapped accounting rule sample (n + 1) = next)
    (hbefore : old.cursor < stage.val) (hcursor : next.cursor = stage.val) :
    entryHistory input C .uncapped accounting rule stage sample = some next.history := by
  apply (entryHistory_some_iff input C .uncapped accounting rule stage sample next.history).mpr
  refine ⟨n + 1, by simpa only [hnext] using hcursor, ?_, by rw [hnext]⟩
  intro k hk he
  have hm := run_cursor_monotone input C .uncapped accounting rule hlegal sample (Nat.le_of_lt_succ hk)
  dsimp only at hm
  rw [hold, he] at hm
  omega

/-- The entry record survives every real testing review. The associated
first-exit lower bound starts at zero at the genuine birth and advances
one sample at a time using actual non-hits of that same selected target. -/
private theorem prefix_testing_origin {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s) :
    ∀ cache : ReferenceReplayCache I, ReferenceStateAligned input available budget cache s →
      s.halted = false → cache.phase = .testing →
      ∀ stage : I.Stage, s.cursor = stage.val → TestingOrigin input C accounting available budget sample cache s stage := by
  induction hp with
  | initial =>
    intro cache haligned _ _ stage hcursor
    have hi := referenceAvailableReplay_initial input available budget hbudget hsmall
    have he : cache = referenceReplayInitial I := Option.some.inj (haligned.parsed.symm.trans hi)
    subst cache
    refine ⟨[], entryHistory_stageZero input C .uncapped accounting
      (referenceRule input available budget none) stage hcursor.symm sample, rfl, ?_, ?_⟩
    · simp only [referenceAvailableEntryTarget, hi, Option.bind_eq_bind, Option.bind_some]
    · intro _ _
      exact bot_le
  | @next n s result earlier step ih =>
    intro cache haligned hactive hphase stage hcursor
    obtain ⟨oldCache, holdAligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget hbudget hsmall none
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier
    have hrunOld := prefix_eq_run_sample input C accounting (referenceRule input available budget none) sample earlier
    have hrunNext := prefix_eq_run_sample input C accounting (referenceRule input available budget none) sample (.next earlier step)
    generalize haction : referenceRule input available budget none sample.1 s.history = action at step
    cases step with
    | review current live port resources =>
      change s.cursor = stage.val at hcursor
      have heq : current = stage := Fin.ext (live.2.symm.trans hcursor)
      subst current
      have hsingle := replay_single_after input available budget s.history oldCache cache
        (.observation stage ((worldTapes input sample.2) stage (s.ledger.reviews stage).toNat).val)
        holdAligned.parsed haligned.parsed
      obtain ⟨holdPhase, hcache⟩ := replay_event_shape input available budget oldCache cache _ hsingle
      subst cache
      obtain ⟨history, hentry, hsnapshot, htarget, hprogress⟩ := ih oldCache holdAligned live.1 holdPhase stage live.2
      have hframe := referenceCacheTarget_observation I available budget oldCache stage
        ((worldTapes input sample.2) stage (s.ledger.reviews stage).toNat).val
      refine ⟨history, hentry, hsnapshot, htarget.trans hframe.symm, ?_⟩
      intro p hp
      have hpOld : referenceAvailableCacheTarget I available budget oldCache = some p := hframe.symm.trans hp
      have hstrict := review_stop_strict input C accounting available budget sample.1 (input.truthAt sample.2)
        (worldTapes input sample.2) earlier oldCache holdAligned holdPhase live.1 stage live.2 p hpOld haction
        (hprogress p hpOld)
      have hfinite := prefix_reviews_natCast_toNat input C .uncapped accounting
        (referenceRule input available budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier stage
      have hstrict' : ((s.ledger.reviews stage).toNat : ℕ∞) <
          (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 := by
        have hw : worldTapes input sample.2 stage = (sample.2 stage).2 := by funext k; rfl
        simpa only [hfinite, hw] using hstrict
      have hsucc := natCast_succ_le_of_lt _ _ hstrict'
      simpa only [record, reviewLedger, Function.update_self, Nat.cast_add, Nat.cast_one, hfinite] using hsucc
    | advance current live written resources =>
      have hsingle := replay_single_after input available budget s.history oldCache cache (.advanced current)
        holdAligned.parsed haligned.parsed
      have hcache := replay_event_shape input available budget oldCache cache _ hsingle
      change cache = {oldCache with
        seen := oldCache.seen ++ [.advanced current]
        entryHistory := oldCache.seen ++ [.advanced current]
        phase := .testing} at hcache
      subst cache
      have hfuture : s.cursor < stage.val := by
        change s.cursor + 1 = stage.val at hcursor
        omega
      have hentry := entryHistory_at_increment input C accounting (referenceRule input available budget none)
        (referenceRule_uncapped_legal input C hearly accounting available budget none) sample n s _ stage hrunOld hrunNext hfuture hcursor
      refine ⟨(record accounting s (.advance current) [.advanced current] (advanceLedger s current) (s.cursor + 1) false).history,
        hentry, haligned.seen, ?_, ?_⟩
      · simp only [referenceAvailableEntryTarget, haligned.parsed, Option.bind_eq_bind, Option.bind_some]
      · intro p _
        have hzero := (prefix_cursorInvariant input C .uncapped accounting (referenceRule input available budget none)
          sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier).future_reviews stage hfuture
        change s.ledger.reviews stage ≤ _
        rw [hzero]
        exact zero_le
    | write current bit live port resources =>
      have hpacket := replay_packet_after input available budget s.history (writeResponses C s current bit) oldCache cache
        holdAligned.parsed haligned.parsed
      have hpacket' : [VisibleEvent.wrote current bit s.clock, VisibleEvent.report current (s.ledger.truth current) s.clock].foldlM
          (referenceAvailableStep input available budget) oldCache = some cache := by
        simpa only [writeResponses, hearly, ite_true, writeLedger, List.singleton_append] using hpacket
      cases hw : referenceAvailableStep input available budget oldCache (.wrote current bit s.clock) with
      | none => simp [hw] at hpacket'
      | some writtenCache =>
        have hr : referenceAvailableStep input available budget writtenCache
            (.report current (s.ledger.truth current) s.clock) = some cache := by simpa [hw] using hpacket'
        have hc : cache.phase = .reported := replay_event_shape input available budget writtenCache cache _ hr
        rw [hphase] at hc
        cases hc
    | allocate handle tool active valid compatible unused unallocated window resources =>
      have hsingle := replay_single_after input available budget s.history oldCache cache (.committed handle tool)
        holdAligned.parsed haligned.parsed
      have hc : cache.phase = .allocated tool := replay_event_shape input available budget oldCache cache _ hsingle
      rw [hphase] at hc
      cases hc
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      have hsingle := replay_single_after input available budget s.history oldCache cache (.executed handle tool)
        holdAligned.parsed haligned.parsed
      have hc : cache.phase = .executed tool := replay_event_shape input available budget oldCache cache _ hsingle
      rw [hphase] at hc
      cases hc
    | stop | abandon => cases hactive


private theorem candidate_write_testing (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : referenceAvailableReplay input available budget history = some cache)
    (stage : I.Stage) (bit : Bool)
    (haction : referenceCandidateAction input available budget none history = .write stage bit) :
    cache.phase = .testing ∧ referenceReplayStage I cache = some stage ∧
      referenceTestingAction input available budget none cache stage = .write stage bit := by
  cases hh : cache.halted with
  | true => simp [referenceCandidateAction, hparse, hh] at haction
  | false =>
    cases hs : referenceReplayStage I cache with
    | none =>
      simp only [referenceCandidateAction, hparse, hh, Bool.false_eq_true, ite_false, hs] at haction
      split_ifs at haction
    | some current =>
      cases hphase : cache.phase with
      | testing =>
        have ht : referenceTestingAction input available budget none cache current = .write stage bit := by
          simpa only [referenceCandidateAction, hparse, hh, Bool.false_eq_true, ite_false, hs, hphase] using haction
        rcases referenceTestingAction_supported input available budget none cache current with hreview | ⟨otherBit, hwrite⟩ | habandon
        · rw [hreview] at ht
          cases ht
        · have heq := (Action.write.inj (hwrite.symm.trans ht)).1
          subst current
          exact ⟨rfl, rfl, ht⟩
        · rw [habandon] at ht
          cases ht
      | written => simp [referenceCandidateAction, hparse, hh, hs, hphase] at haction
      | executed tool => simp [referenceCandidateAction, hparse, hh, hs, hphase] at haction
      | allocated tool =>
        cases hv : referenceVisibleHandle history current <;> simp [referenceCandidateAction, hparse, hh, hs, hphase, hv] at haction
      | reported =>
        cases hc : referenceReplayCorrect cache current with
        | true => simp [referenceCandidateAction, hparse, hh, hs, hphase, hc] at haction
        | false =>
          cases hr : referenceReplayRisk budget cache with
          | none => simp [referenceCandidateAction, hparse, hh, hs, hphase, hc, hr] at haction
          | some currentRisk =>
            cases hv : referenceVisibleHandle history current with
            | none => simp [referenceCandidateAction, hparse, hh, hs, hphase, hc, hr, hv] at haction
            | some handle =>
              cases ht : referenceAvailableRepairTool I available current (historyUsed cache.entryHistory) <;>
                simp [referenceCandidateAction, hparse, hh, hs, hphase, hc, hr, hv, ht] at haction

theorem referenceTestingAction_posteriorWrite_hit (input : StatisticalInput I) (available : Finset I.Tool)
    (budget p : ℚ) (cache : ReferenceReplayCache I) (stage : I.Stage) (bit : Bool)
    (htarget : referenceAvailableCacheTarget I available budget cache = some p)
    (hvalid : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize)
    (haction : referenceTestingAction input available budget none cache stage = .write stage bit) :
    (input.experiment stage).rationalWordHits p (historyObservationWord input cache.seen stage hvalid) = true ∧
      bit = (input.experiment stage).rationalWordMAP (historyObservationWord input cache.seen stage hvalid) := by
  obtain ⟨kind, current, hk, _, _, _, hb⟩ := referenceAvailableCacheTarget_some_spec I available budget p cache htarget
  cases kind with
  | infiniteRank => cases hb
  | noTool | finiteBad depth =>
    simp only [referenceTestingAction, hk, htarget, dite_eq_left hvalid] at haction
    cases hh : (input.experiment stage).rationalWordHits p (historyObservationWord input cache.seen stage hvalid) with
    | false => simp only [hh, Bool.false_eq_true, ite_false] at haction; cases haction
    | true =>
      simp only [hh, ite_true] at haction
      exact ⟨rfl, (Action.write.inj haction).2.symm⟩

private theorem cursor_of_replayStage (cache : ReferenceReplayCache I) (stage : I.Stage)
    (hstage : referenceReplayStage I cache = some stage) : historyCursor cache.seen = stage.val := by
  unfold referenceReplayStage at hstage
  split_ifs at hstage
  exact congrArg (fun i : I.Stage => i.val) (Option.some.inj hstage)

/-- Every actual finite-target ideal write occurs at exactly the selected
SPRT stopping time, and writes its actual MAP decision. The initial
available set and seed universe are unrestricted. -/
theorem prefix_referencePosteriorWrite_realization {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s)
    (hactive : s.halted = false) (stage : I.Stage) (bit : Bool)
    (haction : referenceRule input available budget none sample.1 s.history = .write stage bit)
    (history : List (VisibleEvent I)) (p : ℚ)
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history)
    (htarget : referenceAvailableEntryTarget input available budget history = some p) :
    (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 = ((s.ledger.reviews stage).toNat : ℕ∞) ∧
      bit = ((input.experiment stage).posteriorSPRT p).rule.decision () (sample.2 stage).2 := by
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hcand := (referenceRule_eq_candidate_of_prefix input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp).symm.trans haction
  obtain ⟨hphase, hstage, htest⟩ := candidate_write_testing input available budget s.history cache haligned.parsed stage bit hcand
  have hcursor := haligned.cursor.symm.trans (cursor_of_replayStage cache stage hstage)
  obtain ⟨origin, he, _, ht, hprogress⟩ := prefix_testing_origin input C hearly accounting available budget hbudget hsmall sample
    hp cache haligned hactive hphase stage hcursor
  have heq : origin = history := Option.some.inj (he.symm.trans hentry)
  rw [heq] at ht
  have hpCache : referenceAvailableCacheTarget I available budget cache = some p := ht.symm.trans htarget
  have hb := cacheTarget_bounds I available budget p cache hpCache
  have hvalid : ∀ symbol ∈ historyObservations s.history stage, symbol < (input.experiment stage).alphabetSize :=
    fun symbol hm => prefix_historyObservation_alphabet input C .uncapped accounting
      (referenceRule input available budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage symbol hm
  have hvalidCache : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize := by
    simpa only [haligned.seen] using hvalid
  obtain ⟨hhit, hbit⟩ := referenceTestingAction_posteriorWrite_hit input available budget p cache stage bit hpCache hvalidCache htest
  have hhit' : (input.experiment stage).rationalWordHits p (historyObservationWord input s.history stage hvalid) = true := by
    simpa only [haligned.seen] using hhit
  have hbit' : bit = (input.experiment stage).rationalWordMAP (historyObservationWord input s.history stage hvalid) := by
    simpa only [haligned.seen] using hbit
  have hboundary := (prefix_historyObservationWord_hits_iff input C .uncapped accounting
    (referenceRule input available budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage hvalid p hb.1 hb.2).mp hhit'
  have hle := ((input.experiment stage).posteriorThresholdStop_le_iff p (worldTapes input sample.2 stage) (s.ledger.reviews stage).toNat).mpr
    ⟨_, le_rfl, hboundary⟩
  have hfinite := prefix_reviews_natCast_toNat input C .uncapped accounting (referenceRule input available budget none)
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage
  have hw : worldTapes input sample.2 stage = (sample.2 stage).2 := by funext k; rfl
  have hge : ((s.ledger.reviews stage).toNat : ℕ∞) ≤
      (input.experiment stage).posteriorThresholdStop p (worldTapes input sample.2 stage) := by
    rw [hfinite, hw]
    exact hprogress p hpCache
  have hstop := le_antisymm hle hge
  refine ⟨by simpa only [hw] using hstop, ?_⟩
  have hmap := prefix_historyObservationWord_MAP_at_stop input C .uncapped accounting
    (referenceRule input available budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp stage hvalid p hstop
  simpa only [hw] using hbit'.trans hmap

def referenceAvailableEntryChoice (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ) :
    Unit × List (VisibleEvent I) → Option ℚ := fun sample => referenceAvailableEntryTarget input available budget sample.2

theorem measurable_referenceAvailableEntryChoice (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ) :
    Measurable (referenceAvailableEntryChoice input available budget) := measurable_of_countable _

/-- A genuine wrong write on a branch whose genuine entry chose a posterior
test. Infinite-rank blind writes are deliberately a separate structural case. -/
def referenceStagePosteriorError (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) : Set (Unit × input.World) :=
  {sample | ∃ (n : ℕ) (bit : Bool) (history : List (VisibleEvent I)) (p : ℚ),
    let state := run input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget).rule sample n
    state.halted = false ∧
    (referenceIdealPolicy input C hearly accounting available budget).rule () state.history = .write stage bit ∧
    entryHistory input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget).rule stage sample = some history ∧
    referenceAvailableEntryTarget input available budget history = some p ∧ bit ≠ (sample.2 stage).1}

theorem referenceStagePosteriorError_subset_entryPosteriorError (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    referenceStagePosteriorError input C hearly accounting available budget stage ⊆
      entryPosteriorError input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget).rule
        stage (referenceAvailableEntryChoice input available budget) := by
  rintro ⟨⟨⟩, world⟩ ⟨n, bit, history, p, hactive, hwrite, hentry, htarget, hwrong⟩
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget).rule
    (referenceIdealPolicy input C hearly accounting available budget).legal ((), world) n
  have hreal := prefix_referencePosteriorWrite_realization input C hearly accounting available budget hbudget hsmall ((), world)
    hp hactive stage bit hwrite history p hentry htarget
  refine ⟨p, ?_, ?_⟩
  · change entryGatedTarget (referenceAvailableEntryChoice input available budget)
      ((), entryHistory input C .uncapped accounting (referenceRule input available budget none) stage ((), world)) = some p
    have he : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage ((), world) = some history := hentry
    rw [he]
    exact htarget
  · change ((input.experiment stage).posteriorSPRT p).rule.decision () (world stage).2 ≠ (world stage).1
    rw [← hreal.2]
    exact hwrong

theorem referenceStagePosteriorError_measure_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (referenceStagePosteriorError input C hearly accounting available budget stage) ≤
      ∫⁻ sample, selectedTargetBound (entryGatedTarget (referenceAvailableEntryChoice input available budget))
        (entrySeedHistory input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget).rule stage sample)
          ∂input.seededWorldLaw (Measure.dirac ()) := by
  apply (measure_mono (referenceStagePosteriorError_subset_entryPosteriorError input C hearly accounting available budget hbudget hsmall stage)).trans
  exact entryPosteriorError_le input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget)
    (Measure.dirac ()) stage (referenceAvailableEntryChoice input available budget)
    (measurable_referenceAvailableEntryChoice input available budget)
    (fun _ history p hp => referenceAvailableEntryTarget_valid input available budget p history hp)

/-- A true per-entry error bound, stated by multiplication so null entry
histories are included. The joint law is the proved pre-birth product law,
not an assumed Markov property or a full-state private seed. -/
theorem referenceStagePosteriorError_on_entry_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (history : List (VisibleEvent I)) (p : ℚ)
    (htarget : referenceAvailableEntryTarget input available budget history = some p) :
    input.seededWorldLaw (Measure.dirac ())
        (referenceStagePosteriorError input C hearly accounting available budget stage ∩
          {sample | entryHistory input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget).rule
            stage sample = some history}) ≤
      ENNReal.ofReal (p : ℝ) * input.seededWorldLaw (Measure.dirac ())
        {sample | entryHistory input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget).rule
          stage sample = some history} := by
  let policy := referenceIdealPolicy input C hearly accounting available budget
  let μ := input.seededWorldLaw (Measure.dirac ())
  let record := entrySeedHistory input C .uncapped accounting policy.rule stage
  let joint := fun sample : Unit × input.World => (record sample, sample.2 stage)
  let rectangle : Set ((Unit × EntryHistory I) × input.StageSample stage) :=
    {((), some history)} ×ˢ fixedPosteriorError input stage p
  have hrecord : Measurable record := measurable_entrySeedHistory input C .uncapped accounting policy.rule policy.measurable_rule stage
  have hjoint : Measurable joint := hrecord.prodMk ((measurable_pi_apply stage).comp measurable_snd)
  have hrectangle : MeasurableSet rectangle := (measurableSet_singleton _).prod (measurableSet_fixedPosteriorError input stage p)
  have hsubset : referenceStagePosteriorError input C hearly accounting available budget stage ∩
      {sample | entryHistory input C .uncapped accounting policy.rule stage sample = some history} ⊆ joint ⁻¹' rectangle := by
    intro sample hs
    obtain ⟨q, hq, herror⟩ := referenceStagePosteriorError_subset_entryPosteriorError input C hearly accounting available budget hbudget hsmall stage hs.1
    have he : entryHistory input C .uncapped accounting policy.rule stage sample = some history := hs.2
    have hq' : referenceAvailableEntryTarget input available budget history = some q := by
      change entryGatedTarget (referenceAvailableEntryChoice input available budget)
        (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) = some q at hq
      rw [he] at hq
      exact hq
    have hqp : q = p := Option.some.inj (hq'.symm.trans htarget)
    subst q
    refine ⟨?_, herror⟩
    change (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) ∈ {((), some history)}
    rw [he]
    cases sample.1
    exact Set.mem_singleton _
  have hmass : (μ.map record) {((), some history)} = μ
      {sample | entryHistory input C .uncapped accounting policy.rule stage sample = some history} := by
    rw [Measure.map_apply hrecord (measurableSet_singleton _)]
    congr 1
    ext sample
    change (sample.1, entryHistory input C .uncapped accounting policy.rule stage sample) = ((), some history) ↔ _
    cases sample.1
    simp only [Prod.mk.injEq, true_and, Set.mem_ofPred_eq]
  have hp := referenceAvailableEntryTarget_valid input available budget p history htarget
  calc
    μ (referenceStagePosteriorError input C hearly accounting available budget stage ∩
        {sample | entryHistory input C .uncapped accounting policy.rule stage sample = some history})
      ≤ μ (joint ⁻¹' rectangle) := measure_mono hsubset
    _ = (μ.map joint) rectangle := (Measure.map_apply hjoint hrectangle).symm
    _ = ((μ.map record).prod (input.stageLaw stage)) rectangle := by
      rw [entrySeedHistory_jointLaw input C .uncapped accounting policy (Measure.dirac ()) stage]
    _ = (μ.map record) {((), some history)} * input.stageLaw stage (fixedPosteriorError input stage p) := Measure.prod_prod _ _
    _ ≤ (μ.map record) {((), some history)} * ENNReal.ofReal (p : ℝ) :=
      mul_le_mul_right (stageLaw_fixedPosteriorError_le input stage p hp.1 hp.2) _
    _ = ENNReal.ofReal (p : ℝ) * μ
        {sample | entryHistory input C .uncapped accounting policy.rule stage sample = some history} := by
      rw [hmass, mul_comm]

theorem posteriorSPRT_tape_ae_finite (E : BinaryExperiment) (p : ℚ) (hp : 0 < p) (hquarter : p ≤ 1 / 4) (truth : Bool) :
    ∀ᵐ tape ∂E.tapeLaw truth, E.posteriorThresholdStop p tape ≠ ⊤ := by
  have hprod := E.expectedSamples_finite_stop (Measure.dirac ()) (E.posteriorSPRT p) truth
    (E.posteriorSPRT_expectedSamples_finite p (BinaryExperiment.posteriorThreshold_nonneg p hp hquarter) truth)
  simp only [BinaryExperiment.conditionalLaw, BinaryExperiment.posteriorSPRT] at hprod
  have hnull : (Measure.dirac ()).prod (E.tapeLaw truth)
      {sample : Unit × E.Tape | E.posteriorThresholdStop p sample.2 = ⊤} = 0 := by
    simpa only [not_not] using (ae_iff.mp hprod)
  have hrectangle : {sample : Unit × E.Tape | E.posteriorThresholdStop p sample.2 = ⊤} =
      Set.univ ×ˢ {tape : E.Tape | E.posteriorThresholdStop p tape = ⊤} := by
    ext sample
    simp only [Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and]
  rw [hrectangle, Measure.prod_prod, measure_univ, one_mul] at hnull
  exact ae_iff.mpr (by simpa only [not_not] using hnull)

theorem stageLaw_posteriorSPRT_ae_finite (input : StatisticalInput I) (stage : I.Stage)
    (p : ℚ) (hp : 0 < p) (hquarter : p ≤ 1 / 4) :
    ∀ᵐ sample ∂input.stageLaw stage, (input.experiment stage).posteriorThresholdStop p sample.2 ≠ ⊤ := by
  have hprod (truth : Bool) : ∀ᵐ sample ∂(Measure.dirac truth).prod ((input.experiment stage).tapeLaw truth),
      (input.experiment stage).posteriorThresholdStop p sample.2 ≠ ⊤ := by
    have htape := posteriorSPRT_tape_ae_finite (input.experiment stage) p hp hquarter truth
    have hmap : ((Measure.dirac truth).prod ((input.experiment stage).tapeLaw truth)).map Prod.snd =
        (input.experiment stage).tapeLaw truth := by simp only [Measure.map_snd_prod, measure_univ, one_smul]
    rw [← hmap] at htape
    exact ae_of_ae_map measurable_snd.aemeasurable htape
  rw [StatisticalInput.stageLaw, ae_add_measure_iff]
  exact ⟨Measure.ae_smul_measure (hprod true) _, Measure.ae_smul_measure (hprod false) _⟩

/-- One common full-measure set supports every valid rational target.
This uses genuine conditional finite ET and the original stage marginal. -/
theorem seededWorld_ae_all_posteriorSPRT_finite {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (ν : Measure Seed) [IsProbabilityMeasure ν] (stage : I.Stage) :
    ∀ᵐ sample ∂input.seededWorldLaw ν, ∀ p : ℚ, 0 < p → p ≤ 1 / 4 →
      (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 ≠ ⊤ := by
  rw [ae_all_iff]
  intro p
  by_cases hv : 0 < p ∧ p ≤ 1 / 4
  · have hs := stageLaw_posteriorSPRT_ae_finite input stage p hv.1 hv.2
    rw [← input.seededWorldLaw_coordinate ν stage] at hs
    have hw := ae_of_ae_map ((measurable_pi_apply stage).comp measurable_snd).aemeasurable hs
    filter_upwards [hw] with sample hsample
    intro _ _
    exact hsample
  · exact Filter.Eventually.of_forall (fun _ hp hq => (hv ⟨hp, hq⟩).elim)

theorem prefix_referenceAvailableReview_realization {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s)
    (hactive : s.halted = false) (stage : I.Stage)
    (haction : referenceRule input available budget none sample.1 s.history = .review stage) :
    ∃ history : List (VisibleEvent I), ∃ p : ℚ,
      entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history ∧
      referenceAvailableEntryTarget input available budget history = some p ∧
      s.ledger.reviews stage < (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 := by
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  obtain ⟨next, hstep⟩ := referenceRule_uncapped_legal input C hearly accounting available budget none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n s hp hactive
  have hnextPrefix := Prefix.next hp hstep
  obtain ⟨nextCache, hnextAligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hnextPrefix
  rw [haction] at hstep
  cases hstep with
  | review stage live port resources =>
    have hsingle := replay_single_after input available budget s.history cache nextCache
      (.observation stage ((worldTapes input sample.2) stage (s.ledger.reviews stage).toNat).val)
      haligned.parsed hnextAligned.parsed
    have hphase := (replay_event_shape input available budget cache nextCache _ hsingle).1
    obtain ⟨history, hentry, _, htarget, hprogress⟩ := prefix_testing_origin input C hearly accounting available budget hbudget hsmall
      sample hp cache haligned hactive hphase stage live.2
    have ht := referenceRule_testing_eq_of_aligned input C accounting available budget none sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) hp hactive cache haligned hphase stage live.2
    obtain ⟨p, hpTarget, _⟩ := referenceTestingAction_review_nonhit input available budget none cache stage (ht.symm.trans haction)
    refine ⟨history, p, hentry, htarget.trans hpTarget, ?_⟩
    have hs := review_stop_strict input C accounting available budget sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
      hp cache haligned hphase hactive stage live.2 p hpTarget haction (hprogress p hpTarget)
    have hw : worldTapes input sample.2 stage = (sample.2 stage).2 := by funext k; rfl
    simpa only [hw] using hs

/-- The actual interpreter requests reviews on this stage with unbounded
sample count. All witnesses are genuine active returned-action states. -/
def referenceStageInfiniteReviews (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (stage : I.Stage) : Set (Unit × input.World) :=
  {sample | ∀ threshold : ℕ,
    sample ∈ referenceStageOverflow input C hearly accounting available budget (fun _ => threshold) stage}

theorem referenceStageInfiniteReviews_realization (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage)
    (sample : Unit × input.World) (hinfinite : sample ∈ referenceStageInfiniteReviews input C hearly accounting available budget stage) :
    ∃ history : List (VisibleEvent I), ∃ p : ℚ,
      entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history ∧
      referenceAvailableEntryTarget input available budget history = some p ∧
      (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 = ⊤ := by
  rcases sample with ⟨⟨⟩, world⟩
  obtain ⟨n, hactive, hreview, _⟩ := hinfinite 0
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget).rule
    (referenceIdealPolicy input C hearly accounting available budget).legal ((), world) n
  obtain ⟨history, p, hentry, htarget, _⟩ := prefix_referenceAvailableReview_realization input C hearly accounting available budget hbudget hsmall
    ((), world) hp hactive stage hreview
  refine ⟨history, p, hentry, htarget, ?_⟩
  by_contra hfinite
  let T := (input.experiment stage).posteriorThresholdStop p (world stage).2
  have hcast : (T.toNat : ℕ∞) = T := ENat.natCast_toNat hfinite
  obtain ⟨m, hactive', hreview', hcount⟩ := hinfinite T.toNat
  obtain ⟨_, _, hp'⟩ := run_has_prefix input C .uncapped accounting (referenceIdealPolicy input C hearly accounting available budget).rule
    (referenceIdealPolicy input C hearly accounting available budget).legal ((), world) m
  obtain ⟨otherHistory, q, hentry', htarget', hstrict⟩ := prefix_referenceAvailableReview_realization input C hearly accounting available budget hbudget hsmall
    ((), world) hp' hactive' stage hreview'
  have heq : otherHistory = history := Option.some.inj (hentry'.symm.trans hentry)
  rw [heq] at htarget'
  have hqp : q = p := Option.some.inj (htarget'.symm.trans htarget)
  subst q
  have hlt : (T.toNat : ℕ∞) < T := hcount.trans_lt hstrict
  rw [hcast] at hlt
  exact (lt_irrefl T) hlt

/-- Genuine local infinite-review paths are null. Finite ET, the exact
stage marginal, and countably many rational entry targets establish this;
no native quota horizon is applied to the uncapped reference. -/
theorem referenceStageInfiniteReviews_measure_zero (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (referenceStageInfiniteReviews input C hearly accounting available budget stage) = 0 := by
  have hfinite := seededWorld_ae_all_posteriorSPRT_finite input (Measure.dirac ()) stage
  apply measure_mono_null ?_ (ae_iff.mp hfinite)
  intro sample hinfinite hall
  obtain ⟨history, p, _, htarget, hstop⟩ := referenceStageInfiniteReviews_realization input C hearly accounting available budget hbudget hsmall
    stage sample hinfinite
  have hp := referenceAvailableEntryTarget_valid input available budget p history htarget
  exact hall p hp.1 hp.2 hstop

end PaperProofs.Common.Native
