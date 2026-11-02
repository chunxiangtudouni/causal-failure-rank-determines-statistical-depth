module

public import PaperProofs.Common.ReferenceCertification
public import PaperProofs.Common.ReferenceControllerPreservation

/-!
The actual ideal controller's exhausted-review event is identified with the
potential posterior first-exit overflow selected at genuine entry history.
All reasoning is pathwise. The controller still reads only its finite
visible history; truth and tapes occur only in the analysis.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

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

/-- Reading another symbol leaves the entry snapshot and target unchanged. -/
theorem referenceCacheTarget_observation (I : Instance) (available : Finset I.Tool) (budget : ℚ)
    (cache : ReferenceReplayCache I) (stage : I.Stage) (symbol : ℕ) :
    referenceAvailableCacheTarget I available budget {cache with seen := cache.seen ++ [.observation stage symbol]} =
      referenceAvailableCacheTarget I available budget cache := by
  simp [referenceAvailableCacheTarget, referenceAvailableKind, referenceReplayStage, referenceReplayRisk, historyCursor,
    List.filterMap_append, List.filterMap_cons, eventAdvance]
  rfl

/-- A testing review implies an actual target and a non-hit, even at time
zero. This is a property of the executable rule, not a test-class premise. -/
theorem referenceTestingAction_review_nonhit (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (limit : ReferenceObservationLimit I) (cache : ReferenceReplayCache I) (stage : I.Stage)
    (haction : referenceTestingAction input available budget limit cache stage = .review stage) :
    ∃ p : ℚ, referenceAvailableCacheTarget I available budget cache = some p ∧
      ∀ hvalid : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize,
        (input.experiment stage).rationalWordHits p (historyObservationWord input cache.seen stage hvalid) = false := by
  cases hk : referenceAvailableKind I available cache with
  | none => simp [referenceTestingAction, hk] at haction
  | some kind =>
    cases kind with
    | infiniteRank => simp [referenceTestingAction, hk] at haction
    | noTool | finiteBad depth =>
      cases ht : referenceAvailableCacheTarget I available budget cache with
      | none => simp [referenceTestingAction, hk, ht] at haction
      | some p =>
        refine ⟨p, rfl, ?_⟩
        intro hvalid
        simp only [referenceTestingAction, hk, ht, dite_eq_left hvalid] at haction
        cases hh : (input.experiment stage).rationalWordHits p (historyObservationWord input cache.seen stage hvalid) with
        | false => rfl
        | true => simp only [hh, ite_true] at haction; cases haction

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

private theorem cacheTarget_bounds (I : Instance) (budget p : ℚ) (cache : ReferenceReplayCache I)
    (ht : referenceAvailableCacheTarget I I.tools budget cache = some p) : 0 < p ∧ p < 1 := by
  have ht' : referenceCacheTarget I budget cache = some p := by simpa only [Instance.tools, referenceAvailableCacheTarget_univ] using ht
  obtain ⟨kind, current, _, _, hv, _, htarget⟩ := referenceCacheTarget_some_spec I budget p cache ht'
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
    (accounting : NormalAccounting I) (budget : ℚ) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input I.tools budget none) seed truth tapes n s)
    (cache : ReferenceReplayCache I) (haligned : ReferenceStateAligned input I.tools budget cache s)
    (hphase : cache.phase = .testing) (hactive : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (p : ℚ) (htarget : referenceAvailableCacheTarget I I.tools budget cache = some p)
    (haction : referenceRule input I.tools budget none seed s.history = .review stage)
    (hbefore : s.ledger.reviews stage ≤ (input.experiment stage).posteriorThresholdStop p (tapes stage)) :
    s.ledger.reviews stage < (input.experiment stage).posteriorThresholdStop p (tapes stage) := by
  have htesting := referenceRule_testing_eq_of_aligned input C accounting I.tools budget none seed truth tapes
    hp hactive cache haligned hphase stage hcursor
  have htest : referenceTestingAction input I.tools budget none cache stage = .review stage := htesting.symm.trans haction
  obtain ⟨q, hq, hnonhit⟩ := referenceTestingAction_review_nonhit input I.tools budget none cache stage htest
  have heq : q = p := Option.some.inj (hq.symm.trans htarget)
  subst q
  have hvalid : ∀ symbol ∈ historyObservations s.history stage, symbol < (input.experiment stage).alphabetSize :=
    fun symbol hm => prefix_historyObservation_alphabet input C .uncapped accounting
      (referenceRule input I.tools budget none) seed truth tapes hp stage symbol hm
  have hvalidCache : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize := by
    simpa only [haligned.seen] using hvalid
  have hfalse : (input.experiment stage).rationalWordHits p (historyObservationWord input s.history stage hvalid) = false := by
    simpa only [haligned.seen] using hnonhit hvalidCache
  have hb := cacheTarget_bounds I budget p cache htarget
  have hiff := prefix_historyObservationWord_hits_iff input C .uncapped accounting
    (referenceRule input I.tools budget none) seed truth tapes hp stage hvalid p hb.1 hb.2
  apply lt_of_le_of_ne hbefore
  intro he
  have hfinite := prefix_reviews_natCast_toNat input C .uncapped accounting
    (referenceRule input I.tools budget none) seed truth tapes hp stage
  have ht : (input.experiment stage).posteriorThresholdStop p (tapes stage) = ((s.ledger.reviews stage).toNat : ℕ∞) :=
    he.symm.trans hfinite.symm
  have hh := hiff.mpr ((input.experiment stage).posteriorThresholdStop_hits p (tapes stage) _ ht)
  rw [hfalse] at hh
  cases hh

private def TestingOrigin {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (sample : Seed × input.World)
    (cache : ReferenceReplayCache I) (s : State I) (stage : I.Stage) : Prop :=
  ∃ history : List (VisibleEvent I),
    entryHistory input C .uncapped accounting (referenceRule input I.tools budget none) stage sample = some history ∧
    cache.entryHistory = history ∧
    referenceAvailableEntryTarget input I.tools budget history = referenceAvailableCacheTarget I I.tools budget cache ∧
    ∀ p : ℚ, referenceAvailableCacheTarget I I.tools budget cache = some p →
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
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input I.tools budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s) :
    ∀ cache : ReferenceReplayCache I, ReferenceStateAligned input I.tools budget cache s →
      s.halted = false → cache.phase = .testing →
      ∀ stage : I.Stage, s.cursor = stage.val → TestingOrigin input C accounting budget sample cache s stage := by
  induction hp with
  | initial =>
    intro cache haligned _ _ stage hcursor
    have hi := referenceAvailableReplay_initial input I.tools budget hbudget hsmall
    have he : cache = referenceReplayInitial I := Option.some.inj (haligned.parsed.symm.trans hi)
    subst cache
    refine ⟨[], entryHistory_stageZero input C .uncapped accounting
      (referenceRule input I.tools budget none) stage hcursor.symm sample, rfl, ?_, ?_⟩
    · simp only [referenceAvailableEntryTarget, hi, Option.bind_eq_bind, Option.bind_some]
    · intro _ _
      exact bot_le
  | @next n s result earlier step ih =>
    intro cache haligned hactive hphase stage hcursor
    obtain ⟨oldCache, holdAligned⟩ := prefix_referenceStateAligned input C hearly accounting I.tools budget hbudget hsmall none
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier
    have hrunOld := prefix_eq_run_sample input C accounting (referenceRule input I.tools budget none) sample earlier
    have hrunNext := prefix_eq_run_sample input C accounting (referenceRule input I.tools budget none) sample (.next earlier step)
    generalize haction : referenceRule input I.tools budget none sample.1 s.history = action at step
    cases step with
    | review current live port resources =>
      change s.cursor = stage.val at hcursor
      have heq : current = stage := Fin.ext (live.2.symm.trans hcursor)
      subst current
      have hsingle := replay_single_after input I.tools budget s.history oldCache cache
        (.observation stage ((worldTapes input sample.2) stage (s.ledger.reviews stage).toNat).val)
        holdAligned.parsed haligned.parsed
      obtain ⟨holdPhase, hcache⟩ := replay_event_shape input I.tools budget oldCache cache _ hsingle
      subst cache
      obtain ⟨history, hentry, hsnapshot, htarget, hprogress⟩ := ih oldCache holdAligned live.1 holdPhase stage live.2
      have hframe := referenceCacheTarget_observation I I.tools budget oldCache stage
        ((worldTapes input sample.2) stage (s.ledger.reviews stage).toNat).val
      refine ⟨history, hentry, hsnapshot, htarget.trans hframe.symm, ?_⟩
      intro p hp
      have hpOld : referenceAvailableCacheTarget I I.tools budget oldCache = some p := hframe.symm.trans hp
      have hstrict := review_stop_strict input C accounting budget sample.1 (input.truthAt sample.2)
        (worldTapes input sample.2) earlier oldCache holdAligned holdPhase live.1 stage live.2 p hpOld haction
        (hprogress p hpOld)
      have hfinite := prefix_reviews_natCast_toNat input C .uncapped accounting
        (referenceRule input I.tools budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier stage
      have hstrict' : ((s.ledger.reviews stage).toNat : ℕ∞) <
          (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 := by
        have hw : worldTapes input sample.2 stage = (sample.2 stage).2 := by funext k; rfl
        simpa only [hfinite, hw] using hstrict
      have hsucc := natCast_succ_le_of_lt _ _ hstrict'
      simpa only [record, reviewLedger, Function.update_self, Nat.cast_add, Nat.cast_one, hfinite] using hsucc
    | advance current live written resources =>
      have hsingle := replay_single_after input I.tools budget s.history oldCache cache (.advanced current)
        holdAligned.parsed haligned.parsed
      have hcache := replay_event_shape input I.tools budget oldCache cache _ hsingle
      change cache = {oldCache with
        seen := oldCache.seen ++ [.advanced current]
        entryHistory := oldCache.seen ++ [.advanced current]
        phase := .testing} at hcache
      subst cache
      have hfuture : s.cursor < stage.val := by
        change s.cursor + 1 = stage.val at hcursor
        omega
      have hentry := entryHistory_at_increment input C accounting (referenceRule input I.tools budget none)
        (referenceRule_uncapped_legal input C hearly accounting I.tools budget none) sample n s _ stage hrunOld hrunNext hfuture hcursor
      refine ⟨(record accounting s (.advance current) [.advanced current] (advanceLedger s current) (s.cursor + 1) false).history,
        hentry, haligned.seen, ?_, ?_⟩
      · simp only [referenceAvailableEntryTarget, haligned.parsed, Option.bind_eq_bind, Option.bind_some]
      · intro p _
        have hzero := (prefix_cursorInvariant input C .uncapped accounting (referenceRule input I.tools budget none)
          sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier).future_reviews stage hfuture
        change s.ledger.reviews stage ≤ _
        rw [hzero]
        exact zero_le
    | write current bit live port resources =>
      have hpacket := replay_packet_after input I.tools budget s.history (writeResponses C s current bit) oldCache cache
        holdAligned.parsed haligned.parsed
      have hpacket' : [VisibleEvent.wrote current bit s.clock, VisibleEvent.report current (s.ledger.truth current) s.clock].foldlM
          (referenceAvailableStep input I.tools budget) oldCache = some cache := by
        simpa only [writeResponses, hearly, ite_true, writeLedger, List.singleton_append] using hpacket
      cases hw : referenceAvailableStep input I.tools budget oldCache (.wrote current bit s.clock) with
      | none => simp [hw] at hpacket'
      | some writtenCache =>
        have hr : referenceAvailableStep input I.tools budget writtenCache
            (.report current (s.ledger.truth current) s.clock) = some cache := by simpa [hw] using hpacket'
        have hc : cache.phase = .reported := replay_event_shape input I.tools budget writtenCache cache _ hr
        rw [hphase] at hc
        cases hc
    | allocate handle tool active valid compatible unused unallocated window resources =>
      have hsingle := replay_single_after input I.tools budget s.history oldCache cache (.committed handle tool)
        holdAligned.parsed haligned.parsed
      have hc : cache.phase = .allocated tool := replay_event_shape input I.tools budget oldCache cache _ hsingle
      rw [hphase] at hc
      cases hc
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      have hsingle := replay_single_after input I.tools budget s.history oldCache cache (.executed handle tool)
        holdAligned.parsed haligned.parsed
      have hc : cache.phase = .executed tool := replay_event_shape input I.tools budget oldCache cache _ hsingle
      rw [hphase] at hc
      cases hc
    | stop | abandon => cases hactive

/-- At every genuine active testing Prefix, entryHistory is the cache's
unchanged entry snapshot and selects the present target. The additional
first-exit bound remembers all earlier non-hits, rather than only the
current likelihood ratio. -/
theorem prefix_referenceTesting_origin {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input I.tools budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s)
    (cache : ReferenceReplayCache I) (haligned : ReferenceStateAligned input I.tools budget cache s)
    (hactive : s.halted = false) (hphase : cache.phase = .testing) (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    ∃ history : List (VisibleEvent I),
      entryHistory input C .uncapped accounting (referenceRule input I.tools budget none) stage sample = some history ∧
      cache.entryHistory = history ∧
      referenceEntryTarget input budget history = referenceAvailableCacheTarget I I.tools budget cache ∧
      ∀ p : ℚ, referenceAvailableCacheTarget I I.tools budget cache = some p →
        s.ledger.reviews stage ≤ (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 := by
  obtain ⟨history, hentry, hsnapshot, htarget, hprogress⟩ :=
    prefix_testing_origin input C hearly accounting budget hbudget hsmall sample hp cache haligned hactive hphase stage hcursor
  refine ⟨history, hentry, hsnapshot, ?_, hprogress⟩
  simpa only [Instance.tools, referenceAvailableEntryTarget_univ] using htarget

/-- A real ideal review occurs strictly before the first exit of the target
chosen at that stage's genuine entry, with no future-success restriction. -/
theorem prefix_referenceReview_realization {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input I.tools budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s)
    (hactive : s.halted = false) (stage : I.Stage)
    (haction : referenceRule input I.tools budget none sample.1 s.history = .review stage) :
    ∃ history : List (VisibleEvent I), ∃ p : ℚ,
      entryHistory input C .uncapped accounting (referenceRule input I.tools budget none) stage sample = some history ∧
      referenceEntryTarget input budget history = some p ∧
      s.ledger.reviews stage < (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 := by
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting I.tools budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  obtain ⟨next, hstep⟩ := referenceRule_uncapped_legal input C hearly accounting I.tools budget none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n s hp hactive
  have hnextPrefix := Prefix.next hp hstep
  obtain ⟨nextCache, hnextAligned⟩ := prefix_referenceStateAligned input C hearly accounting I.tools budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hnextPrefix
  rw [haction] at hstep
  cases hstep with
  | review stage live port resources =>
    have hsingle := replay_single_after input I.tools budget s.history cache nextCache
      (.observation stage ((worldTapes input sample.2) stage (s.ledger.reviews stage).toNat).val)
      haligned.parsed hnextAligned.parsed
    have hphase := (replay_event_shape input I.tools budget cache nextCache _ hsingle).1
    obtain ⟨history, hentry, _, htarget, hprogress⟩ := prefix_referenceTesting_origin input C hearly accounting budget hbudget hsmall
      sample hp cache haligned hactive hphase stage live.2
    have ht := referenceRule_testing_eq_of_aligned input C accounting I.tools budget none sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) hp hactive cache haligned hphase stage live.2
    obtain ⟨p, hpTarget, _⟩ := referenceTestingAction_review_nonhit input I.tools budget none cache stage (ht.symm.trans haction)
    refine ⟨history, p, hentry, htarget.trans hpTarget, ?_⟩
    have hs := review_stop_strict input C accounting budget sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
      hp cache haligned hphase hactive stage live.2 p hpTarget haction (hprogress p hpTarget)
    have hw : worldTapes input sample.2 stage = (sample.2 stage).2 := by funext k; rfl
    simpa only [hw] using hs

/-- Actual exhausted-review overflow is a subset of the potential-entry
SPRT overflow for every quota, including zero. Inclusive first exit means
T=Q cannot generate the exhausted review in the source event. -/
theorem referenceStageOverflow_subset_entryPosteriorOverflow (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (quota : I.Stage → ℕ) (stage : I.Stage) :
    referenceStageOverflow input C hearly accounting I.tools budget quota stage ⊆
      entryPosteriorOverflow input C .uncapped accounting
        (referenceIdealPolicy input C hearly accounting I.tools budget).rule stage
        (referenceEntryChoice input budget) (quota stage) := by
  rintro ⟨⟨⟩, world⟩ ⟨n, hactive, hreview, hquota⟩
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting
    (referenceIdealPolicy input C hearly accounting I.tools budget).rule
    (referenceIdealPolicy input C hearly accounting I.tools budget).legal ((), world) n
  obtain ⟨history, p, hentry, htarget, hstrict⟩ := prefix_referenceReview_realization input C hearly accounting budget hbudget hsmall
    ((), world) hp hactive stage hreview
  refine ⟨p, ?_, ?_⟩
  · change entryGatedTarget (referenceEntryChoice input budget)
      ((), entryHistory input C .uncapped accounting (referenceRule input I.tools budget none) stage ((), world)) = some p
    rw [hentry]
    exact htarget
  · exact hquota.trans_lt hstrict

/-- The original path-to-potential-test target, with all its original
contract/accounting/budget/exponent quantifiers, is now a theorem. -/
theorem referenceOverflowIdentification (input : StatisticalInput I) : ReferenceOverflowIdentification input := by
  intro C hearly accounting budget exponent hbudget hsmall stage
  exact referenceStageOverflow_subset_entryPosteriorOverflow input C hearly accounting budget hbudget hsmall
    (referenceQuota input exponent) stage

/-- The original all-task overflow bound now follows from actual event
identification and the already-proved entry kernel and finite union bound.
The stronger per-entry/per-truth conditional target remains separate. -/
theorem referenceOverflowGuarantee (input : StatisticalInput I) : ReferenceOverflowGuarantee input :=
  referenceOverflowGuarantee_of_identification input (referenceOverflowIdentification input)

end PaperProofs.Common.Native
