module

public import Common.PSTR_ST_TableAlignment_003

/-! First-exit realization for the actual table tie and every initial tool set.
Genuine entry histories and unchanged entry-selected targets are tracked along
all real reviews; target validity and finite tests are conclusions of replay. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.TableOrigin

open PaperProofs.Statistics PaperProofs.Structure CompactPrice TableAlignment
open PaperProofs.Structure.LaminarTree

variable {I : Instance}

def tableEntryTarget (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) : Option ℚ := do
  let cache ← tableReplay input available budget history
  tableTarget I available budget cache

theorem measurable_tableEntryTarget (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ) :
    Measurable (tableEntryTarget input available budget) := measurable_of_countable _

theorem tableEntryTarget_bounds (input : StatisticalInput I) (available : Finset I.Tool)
    (budget p : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (history : List (VisibleEvent I))
    (htarget : tableEntryTarget input available budget history = some p) :
    0 < p ∧ p ≤ 1 / 4 ∧ budget / referenceQuotaConstant I.stageCount ≤ p := by
  obtain ⟨cache, _, ht⟩ := Option.bind_eq_some_iff.mp htarget
  exact tableTarget_bounds I available budget p hbudget hsmall cache ht

theorem prefix_tableRisk_floor (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Unit) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget limit) seed truth tapes n s) :
    ∃ cache, TableStateAligned input available budget cache s ∧
      ∀ current : ℚ, referenceReplayRisk budget cache = some current →
        ReferenceBudgetValid current ∧ budget / (2 : ℚ) ^ (I.stageCount + 1) ≤ current := by
  obtain ⟨cache, aligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget
    hbudget hsmall limit seed truth tapes hp
  exact ⟨cache, aligned, fun current hcurrent => tableReplay_risk_bounds input available budget current
    s.history cache aligned.parsed hcurrent⟩

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
    (hstep : tableStep input available budget cache event = some next) :
    ReplayEventShape cache next event := by
  cases hh : cache.halted with
  | true => simp only [tableStep, hh, ite_true] at hstep; cases hstep
  | false =>
    cases event with
    | observation stage symbol =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      exact ⟨hg.2.2.1, by simpa only [hh] using he⟩
    | wrote stage bit serial =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl
    | report stage truth serial =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl
    | committed handle tool =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl
    | executed handle tool =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl
    | advanced stage =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      simpa only [ReplayEventShape, hh] using he
    | stopped | abandoned =>
      simp only [tableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      rw [he]
      rfl

private theorem replay_packet_after (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history packet : List (VisibleEvent I)) (cache next : ReferenceReplayCache I)
    (hparse : tableReplay input available budget history = some cache)
    (hnext : tableReplay input available budget (history ++ packet) = some next) :
    packet.foldlM (tableStep input available budget) cache = some next := by
  have hs := tableReplay_some_spec input available budget history cache hparse
  have hs' := tableReplay_some_spec input available budget (history ++ packet) next hnext
  rw [List.foldlM_append, hs.2.1] at hs'
  simpa using hs'.2.1

private theorem replay_single_after (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hparse : tableReplay input available budget history = some cache)
    (hnext : tableReplay input available budget (history ++ [event]) = some next) :
    tableStep input available budget cache event = some next := by
  simpa using replay_packet_after input available budget history [event] cache next hparse hnext

/-- Reading another symbol leaves the entry snapshot and target unchanged. -/
theorem tableCacheTarget_observation (I : Instance) (available : Finset I.Tool) (budget : ℚ)
    (cache : ReferenceReplayCache I) (stage : I.Stage) (symbol : ℕ) :
    tableTarget I available budget {cache with seen := cache.seen ++ [.observation stage symbol]} =
      tableTarget I available budget cache := by
  simp [tableTarget, tableKind, referenceReplayStage, referenceReplayRisk, historyCursor,
    List.filterMap_append, List.filterMap_cons, eventAdvance]
  rfl

/-- A testing review implies an actual target and a non-hit, even at time
zero. This is a property of the executable rule, not a test-class premise. -/
theorem tableTestingAction_review_nonhit (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (limit : ReferenceObservationLimit I) (cache : ReferenceReplayCache I) (stage : I.Stage)
    (haction : tableTestingAction input available budget limit cache stage = .review stage) :
    ∃ p : ℚ, tableTarget I available budget cache = some p ∧
      ∀ hvalid : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize,
        (input.experiment stage).rationalWordHits p (historyObservationWord input cache.seen stage hvalid) = false := by
  cases hk : tableKind I available cache with
  | none => simp [tableTestingAction, hk] at haction
  | some kind =>
    cases kind with
    | infiniteRank => simp [tableTestingAction, hk] at haction
    | noTool | finiteBad depth =>
      cases ht : tableTarget I available budget cache with
      | none => simp [tableTestingAction, hk, ht] at haction
      | some p =>
        refine ⟨p, rfl, ?_⟩
        intro hvalid
        simp only [tableTestingAction, hk, ht, dite_eq_left hvalid] at haction
        cases hh : (input.experiment stage).rationalWordHits p (historyObservationWord input cache.seen stage hvalid) with
        | false => rfl
        | true => simp only [hh, ite_true] at haction; cases haction

private theorem prefix_eq_run_sample  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Unit) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) n s) : run input C .uncapped accounting rule sample n = s := by
  have he := prefix_eq_run input C .uncapped accounting rule sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hw : replayWorld input (input.truthAt sample.2) (worldTapes input sample.2) = sample.2 := by
    funext stage
    exact Prod.eta _
  simpa only [hw] using he

private theorem cacheTarget_bounds (I : Instance) (available : Finset I.Tool)
    (budget p : ℚ) (cache : ReferenceReplayCache I)
    (ht : tableTarget I available budget cache = some p) : 0 < p ∧ p < 1 := by
  obtain ⟨kind, current, _, _, hv, _, htarget⟩ := tableTarget_some_spec I available budget p cache ht
  have hb := referenceBudgetTarget_valid_floor kind current p hv htarget
  exact ⟨hb.1, lt_of_le_of_lt hb.2.1 (by norm_num)⟩

private theorem natCast_succ_le_of_lt (r : ℕ) (T : ℕ∞) (h : (r : ℕ∞) < T) : ((r + 1 : ℕ) : ℕ∞) ≤ T := by
  cases T using ENat.recTopCoe with
  | top => exact le_top
  | coe t => exact ENat.natCast_le_natCast.mpr (Nat.succ_le_of_lt (ENat.natCast_lt_natCast.mp h))

/-- The induction's first-exit lower bound becomes strict when the actual
ideal controller requests another review. The lower bound is propagated
from birth and previous real reviews below, not postulated globally. -/
private theorem review_stop_strict  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (seed : Unit) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) seed truth tapes n s)
    (cache : ReferenceReplayCache I) (haligned : TableStateAligned input available budget cache s)
    (hphase : cache.phase = .testing) (hactive : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val)
    (p : ℚ) (htarget : tableTarget I available budget cache = some p)
    (haction : tableRule input available budget none seed s.history = .review stage)
    (hbefore : s.ledger.reviews stage ≤ (input.experiment stage).posteriorThresholdStop p (tapes stage)) :
    s.ledger.reviews stage < (input.experiment stage).posteriorThresholdStop p (tapes stage) := by
  have htesting := tableRule_testing_eq_of_aligned input C accounting available budget none seed truth tapes
    hp hactive cache haligned hphase stage hcursor
  have htest : tableTestingAction input available budget none cache stage = .review stage := htesting.symm.trans haction
  obtain ⟨q, hq, hnonhit⟩ := tableTestingAction_review_nonhit input available budget none cache stage htest
  have heq : q = p := Option.some.inj (hq.symm.trans htarget)
  subst q
  have hvalid : ∀ symbol ∈ historyObservations s.history stage, symbol < (input.experiment stage).alphabetSize :=
    fun symbol hm => prefix_historyObservation_alphabet input C .uncapped accounting
      (tableRule input available budget none) seed truth tapes hp stage symbol hm
  have hvalidCache : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize := by
    simpa only [haligned.seen] using hvalid
  have hfalse : (input.experiment stage).rationalWordHits p (historyObservationWord input s.history stage hvalid) = false := by
    simpa only [haligned.seen] using hnonhit hvalidCache
  have hb := cacheTarget_bounds I available budget p cache htarget
  have hiff := prefix_historyObservationWord_hits_iff input C .uncapped accounting
    (tableRule input available budget none) seed truth tapes hp stage hvalid p hb.1 hb.2
  apply lt_of_le_of_ne hbefore
  intro he
  have hfinite := prefix_reviews_natCast_toNat input C .uncapped accounting
    (tableRule input available budget none) seed truth tapes hp stage
  have ht : (input.experiment stage).posteriorThresholdStop p (tapes stage) = ((s.ledger.reviews stage).toNat : ℕ∞) :=
    he.symm.trans hfinite.symm
  have hh := hiff.mpr ((input.experiment stage).posteriorThresholdStop_hits p (tapes stage) _ ht)
  rw [hfalse] at hh
  cases hh

private def TestingOrigin  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ) (sample : Unit × input.World)
    (cache : ReferenceReplayCache I) (s : State I) (stage : I.Stage) : Prop :=
  ∃ history : List (VisibleEvent I),
    entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history ∧
    cache.entryHistory = history ∧
    tableEntryTarget input available budget history = tableTarget I available budget cache ∧
    ∀ p : ℚ, tableTarget I available budget cache = some p →
      s.ledger.reviews stage ≤ (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2

private theorem entryHistory_at_increment  (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (rule : PolicyRule I Unit)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Unit × input.World)
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
private theorem prefix_testing_origin  (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s) :
    ∀ cache : ReferenceReplayCache I, TableStateAligned input available budget cache s →
      s.halted = false → cache.phase = .testing →
      ∀ stage : I.Stage, s.cursor = stage.val → TestingOrigin input C accounting available budget sample cache s stage := by
  induction hp with
  | initial =>
    intro cache haligned _ _ stage hcursor
    have hi := tableReplay_initial input available budget hbudget hsmall
    have he : cache = referenceReplayInitial I := Option.some.inj (haligned.parsed.symm.trans hi)
    subst cache
    refine ⟨[], entryHistory_stageZero input C .uncapped accounting
      (tableRule input available budget none) stage hcursor.symm sample, rfl, ?_, ?_⟩
    · simp only [tableEntryTarget, hi, Option.bind_eq_bind, Option.bind_some]
    · intro _ _
      exact bot_le
  | @next n s result earlier step ih =>
    intro cache haligned hactive hphase stage hcursor
    obtain ⟨oldCache, holdAligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget hbudget hsmall none
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier
    have hrunOld := prefix_eq_run_sample input C accounting (tableRule input available budget none) sample earlier
    have hrunNext := prefix_eq_run_sample input C accounting (tableRule input available budget none) sample (.next earlier step)
    generalize haction : tableRule input available budget none sample.1 s.history = action at step
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
      have hframe := tableCacheTarget_observation I available budget oldCache stage
        ((worldTapes input sample.2) stage (s.ledger.reviews stage).toNat).val
      refine ⟨history, hentry, hsnapshot, htarget.trans hframe.symm, ?_⟩
      intro p hp
      have hpOld : tableTarget I available budget oldCache = some p := hframe.symm.trans hp
      have hstrict := review_stop_strict input C accounting available budget sample.1 (input.truthAt sample.2)
        (worldTapes input sample.2) earlier oldCache holdAligned holdPhase live.1 stage live.2 p hpOld haction
        (hprogress p hpOld)
      have hfinite := prefix_reviews_natCast_toNat input C .uncapped accounting
        (tableRule input available budget none) sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier stage
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
      have hentry := entryHistory_at_increment input C accounting (tableRule input available budget none)
        (tableRule_uncapped_legal input C hearly accounting available budget none) sample n s _ stage hrunOld hrunNext hfuture hcursor
      refine ⟨(record accounting s (.advance current) [.advanced current] (advanceLedger s current) (s.cursor + 1) false).history,
        hentry, haligned.seen, ?_, ?_⟩
      · simp only [tableEntryTarget, haligned.parsed, Option.bind_eq_bind, Option.bind_some]
      · intro p _
        have hzero := (prefix_cursorInvariant input C .uncapped accounting (tableRule input available budget none)
          sample.1 (input.truthAt sample.2) (worldTapes input sample.2) earlier).future_reviews stage hfuture
        change s.ledger.reviews stage ≤ _
        rw [hzero]
        exact zero_le
    | write current bit live port resources =>
      have hpacket := replay_packet_after input available budget s.history (writeResponses C s current bit) oldCache cache
        holdAligned.parsed haligned.parsed
      have hpacket' : [VisibleEvent.wrote current bit s.clock, VisibleEvent.report current (s.ledger.truth current) s.clock].foldlM
          (tableStep input available budget) oldCache = some cache := by
        simpa only [writeResponses, hearly, ite_true, writeLedger, List.singleton_append] using hpacket
      cases hw : tableStep input available budget oldCache (.wrote current bit s.clock) with
      | none => simp [hw] at hpacket'
      | some writtenCache =>
        have hr : tableStep input available budget writtenCache
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

/-- At every genuine active testing Prefix, entryHistory is the cache's
unchanged entry snapshot and selects the present target. The additional
first-exit bound remembers all earlier non-hits, rather than only the
current likelihood ratio. -/
theorem prefix_tableTesting_origin  (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s)
    (cache : ReferenceReplayCache I) (haligned : TableStateAligned input available budget cache s)
    (hactive : s.halted = false) (hphase : cache.phase = .testing) (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    ∃ history : List (VisibleEvent I),
      entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history ∧
      cache.entryHistory = history ∧
      tableEntryTarget input available budget history = tableTarget I available budget cache ∧
      ∀ p : ℚ, tableTarget I available budget cache = some p →
        s.ledger.reviews stage ≤ (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 := by
  exact prefix_testing_origin input hlaminar C hearly accounting available budget hbudget hsmall
    sample hp cache haligned hactive hphase stage hcursor

/-- A real ideal review occurs strictly before the first exit of the target
chosen at that stage's genuine entry, with no future-success restriction. -/
theorem prefix_tableReview_realization  (input : StatisticalInput I) (hlaminar : LaminarSchedule I.compatibility) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (tableRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) n s)
    (hactive : s.halted = false) (stage : I.Stage)
    (haction : tableRule input available budget none sample.1 s.history = .review stage) :
    ∃ history : List (VisibleEvent I), ∃ p : ℚ,
      entryHistory input C .uncapped accounting (tableRule input available budget none) stage sample = some history ∧
      tableEntryTarget input available budget history = some p ∧
      s.ledger.reviews stage < (input.experiment stage).posteriorThresholdStop p (sample.2 stage).2 := by
  obtain ⟨cache, haligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  obtain ⟨next, hstep⟩ := tableRule_uncapped_legal input C hearly accounting available budget none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n s hp hactive
  have hnextPrefix := Prefix.next hp hstep
  obtain ⟨nextCache, hnextAligned⟩ := prefix_tableStateAligned hlaminar input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hnextPrefix
  rw [haction] at hstep
  cases hstep with
  | review stage live port resources =>
    have hsingle := replay_single_after input available budget s.history cache nextCache
      (.observation stage ((worldTapes input sample.2) stage (s.ledger.reviews stage).toNat).val)
      haligned.parsed hnextAligned.parsed
    have hphase := (replay_event_shape input available budget cache nextCache _ hsingle).1
    obtain ⟨history, hentry, _, htarget, hprogress⟩ := prefix_tableTesting_origin input hlaminar C hearly accounting available budget hbudget hsmall
      sample hp cache haligned hactive hphase stage live.2
    have ht := tableRule_testing_eq_of_aligned input C accounting available budget none sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) hp hactive cache haligned hphase stage live.2
    obtain ⟨p, hpTarget, _⟩ := tableTestingAction_review_nonhit input available budget none cache stage (ht.symm.trans haction)
    refine ⟨history, p, hentry, htarget.trans hpTarget, ?_⟩
    have hs := review_stop_strict input C accounting available budget sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
      hp cache haligned hphase hactive stage live.2 p hpTarget haction (hprogress p hpTarget)
    have hw : worldTapes input sample.2 stage = (sample.2 stage).2 := by funext k; rfl
    simpa only [hw] using hs


end PaperProofs.Common.Native.PSTRStatistics.TableOrigin
