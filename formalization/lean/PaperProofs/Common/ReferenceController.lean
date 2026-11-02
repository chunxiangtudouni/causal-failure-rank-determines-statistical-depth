module

public import PaperProofs.Common.ReferenceReplayAvailable
public import PaperProofs.Common.NativeCapTransfer
public import PaperProofs.Common.AvailableValue

/-!
A genuine seed/history action rule with finite visible permission guards.
Testing checks inclusive rational first exit before the original quota.
The initial-available-set replay uses the same cache and original ledger.
Uncapped legality is a theorem of actual Prefix permissions, not a Policy
performance field. Correct reference paths still require a proof that the
guards do not add abandonment; parser alignment and risk remain separate.

Initial, review, full early write/report, and abandonment alignment are
proved below. Allocation, execution, and advance preservation, and the
resulting OwnPrefix invariant and nonbinding guards, remain unproved.
ReferenceControllerAlignment, ReferenceInfiniteRankZeroReviews, and
ReferenceRiskGuarantee state those original targets as Prop definitions;
none is an axiom, a Policy field, or an input to the legality theorem.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}
/-- none is the ideal reference; some Q is the original per-stage truncation. -/
abbrev ReferenceObservationLimit (I : Instance) := Option (I.Stage → ℕ)

def referenceTestingAction (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (stage : I.Stage) : Action I :=
  match referenceAvailableKind I initialAvailable cache with
  | none => .abandon
  | some .infiniteRank => .write stage false
  | some (.noTool) | some (.finiteBad _) =>
    match referenceAvailableCacheTarget I initialAvailable risk cache with
    | none => .abandon
    | some target =>
      if hvalid : ∀ symbol ∈ historyObservations cache.seen stage,
          symbol < (input.experiment stage).alphabetSize then
        let word := historyObservationWord input cache.seen stage hvalid
        if (input.experiment stage).rationalWordHits target word then
          .write stage ((input.experiment stage).rationalWordMAP word)
        else match limit with
          | none => .review stage
          | some quota => if (historyObservations cache.seen stage).length < quota stage then .review stage else .abandon
      else .abandon

theorem referenceTestingAction_hit (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (cache : ReferenceReplayCache I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (hkind : referenceAvailableKind I initialAvailable cache = some kind)
    (hfinite : kind ≠ .infiniteRank) (target : ℚ)
    (htarget : referenceAvailableCacheTarget I initialAvailable risk cache = some target)
    (hvalid : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize)
    (hhit : (input.experiment stage).rationalWordHits target (historyObservationWord input cache.seen stage hvalid) = true) :
    referenceTestingAction input initialAvailable risk limit cache stage =
      .write stage ((input.experiment stage).rationalWordMAP (historyObservationWord input cache.seen stage hvalid)) := by
  cases kind with
  | infiniteRank => exact (hfinite rfl).elim
  | noTool | finiteBad depth =>
    simp only [referenceTestingAction, hkind, htarget]
    rw [dite_eq_left hvalid]
    simp only [hhit, ite_true]

theorem referenceTestingAction_ideal_review (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (hkind : referenceAvailableKind I initialAvailable cache = some kind)
    (hfinite : kind ≠ .infiniteRank) (target : ℚ)
    (htarget : referenceAvailableCacheTarget I initialAvailable risk cache = some target)
    (hvalid : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize)
    (hhit : (input.experiment stage).rationalWordHits target (historyObservationWord input cache.seen stage hvalid) = false) :
    referenceTestingAction input initialAvailable risk none cache stage = .review stage := by
  cases kind with
  | infiniteRank => exact (hfinite rfl).elim
  | noTool | finiteBad depth =>
    simp only [referenceTestingAction, hkind, htarget]
    rw [dite_eq_left hvalid]
    simp only [hhit, Bool.false_eq_true, ite_false]

theorem referenceTestingAction_exhausted (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (quota : I.Stage → ℕ) (cache : ReferenceReplayCache I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (hkind : referenceAvailableKind I initialAvailable cache = some kind)
    (hfinite : kind ≠ .infiniteRank) (target : ℚ)
    (htarget : referenceAvailableCacheTarget I initialAvailable risk cache = some target)
    (hvalid : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize)
    (hhit : (input.experiment stage).rationalWordHits target (historyObservationWord input cache.seen stage hvalid) = false)
    (hquota : quota stage ≤ (historyObservations cache.seen stage).length) :
    referenceTestingAction input initialAvailable risk (some quota) cache stage = .abandon := by
  cases kind with
  | infiniteRank => exact (hfinite rfl).elim
  | noTool | finiteBad depth =>
    simp only [referenceTestingAction, hkind, htarget]
    rw [dite_eq_left hvalid]
    simp only [hhit, Bool.false_eq_true, ite_false, not_lt_of_ge hquota]

theorem referenceTestingAction_ne_allocate (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (cache : ReferenceReplayCache I) (stage : I.Stage)
    (handle : MismatchHandle I) (tool : I.Tool) :
    referenceTestingAction input initialAvailable risk limit cache stage ≠ .allocate handle tool := by
  unfold referenceTestingAction
  split <;> try simp
  all_goals split <;> try simp
  all_goals split_ifs <;> try simp
  all_goals
    cases limit with
    | none => simp
    | some quota => dsimp only; split_ifs <;> simp

theorem referenceTestingAction_supported (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (cache : ReferenceReplayCache I) (stage : I.Stage) :
    referenceTestingAction input initialAvailable risk limit cache stage = .review stage ∨
      (∃ bit, referenceTestingAction input initialAvailable risk limit cache stage = .write stage bit) ∨
      referenceTestingAction input initialAvailable risk limit cache stage = .abandon := by
  cases hk : referenceAvailableKind I initialAvailable cache with
  | none =>
    simp only [referenceTestingAction, hk]
    exact Or.inr (Or.inr trivial)
  | some kind =>
    cases kind with
    | infiniteRank =>
      simp only [referenceTestingAction, hk]
      exact Or.inr (Or.inl ⟨false, rfl⟩)
    | noTool | finiteBad depth =>
      cases ht : referenceAvailableCacheTarget I initialAvailable risk cache with
      | none =>
        simp only [referenceTestingAction, hk, ht]
        exact Or.inr (Or.inr trivial)
      | some target =>
        by_cases hv : ∀ symbol ∈ historyObservations cache.seen stage,
            symbol < (input.experiment stage).alphabetSize
        · simp only [referenceTestingAction, hk, ht, dite_eq_left hv]
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
        · simp only [referenceTestingAction, hk, ht, dite_eq_right hv]
          exact Or.inr (Or.inr trivial)

def referenceVisibleHandle (history : List (VisibleEvent I)) (stage : I.Stage) : Option (MismatchHandle I) := do
  let written ← historyWrite history stage
  some ⟨stage, written.2⟩

def referenceCandidateAction (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ) (limit : ReferenceObservationLimit I)
    (history : List (VisibleEvent I)) : Action I :=
  match referenceAvailableReplay input initialAvailable risk history with
  | none => .abandon
  | some cache =>
    if cache.halted then .stop else
    match referenceReplayStage I cache with
    | none => if historyCursor history = I.stageCount then .stop else .abandon
    | some stage =>
      match cache.phase with
      | .testing => referenceTestingAction input initialAvailable risk limit cache stage
      | .written => .abandon
      | .reported =>
        if referenceReplayCorrect cache stage then .advance stage else
        match referenceReplayRisk risk cache, referenceVisibleHandle history stage,
            referenceAvailableRepairTool I initialAvailable stage (historyUsed cache.entryHistory) with
        | some _, some handle, some tool => .allocate handle tool
        | _, _, _ => .abandon
      | .allocated tool =>
        match referenceVisibleHandle history stage with
        | none => .abandon
        | some handle => .execute handle tool
      | .executed _ => .advance stage

theorem referenceCandidateAction_allocate_mem (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool)
    (haction : referenceCandidateAction input initialAvailable risk limit history = .allocate handle tool) :
    tool ∈ initialAvailable := by
  cases hp : referenceAvailableReplay input initialAvailable risk history with
  | none => simp only [referenceCandidateAction, hp] at haction; cases haction
  | some cache =>
    cases hh : cache.halted with
    | true => simp only [referenceCandidateAction, hp, hh, ite_true] at haction; cases haction
    | false =>
      simp only [referenceCandidateAction, hp, hh, Bool.false_eq_true, ite_false] at haction
      cases hs : referenceReplayStage I cache with
      | none =>
        rw [hs] at haction
        split_ifs at haction
      | some stage =>
        rw [hs] at haction
        cases hphase : cache.phase with
        | testing =>
          simp only [hphase] at haction
          exact (referenceTestingAction_ne_allocate input initialAvailable risk limit cache stage handle tool haction).elim
        | written => simp only [hphase] at haction; cases haction
        | executed old => simp only [hphase] at haction; cases haction
        | allocated old =>
          simp only [hphase] at haction
          cases hv : referenceVisibleHandle history stage <;> simp only [hv] at haction <;> cases haction
        | reported =>
          simp only [hphase] at haction
          cases hc : referenceReplayCorrect cache stage with
          | true => simp only [hc, ite_true] at haction; cases haction
          | false =>
            simp only [hc, Bool.false_eq_true, ite_false] at haction
            cases hr : referenceReplayRisk risk cache <;> simp only [hr] at haction
            · cases haction
            · cases hv : referenceVisibleHandle history stage <;> simp only [hv] at haction
              · cases haction
              · cases ht : referenceAvailableRepairTool I initialAvailable stage (historyUsed cache.entryHistory) with
                | none => simp only [ht] at haction; cases haction
                | some selected =>
                  simp only [ht] at haction
                  have heq := Action.allocate.inj haction
                  have hmem := (referenceAvailableRepairTool_spec I initialAvailable stage
                    (historyUsed cache.entryHistory) selected ht).1
                  exact heq.2 ▸ (Finset.mem_sdiff.mp (Finset.mem_inter.mp hmem).2).1

/-- This finite public predicate checks only actual event content. -/
def historyValidHandle (history : List (VisibleEvent I)) (handle : MismatchHandle I) : Prop :=
  match historyReport history handle.stage with
  | none => False
  | some (truth, serial) => historyWritten history handle.stage = some (!truth) ∧
      handle.writeSerial = serial ∧ historyWriteSerial history handle.stage = handle.writeSerial

instance historyValidHandle_decidable (history : List (VisibleEvent I)) (handle : MismatchHandle I) :
    Decidable (historyValidHandle history handle) := by
  unfold historyValidHandle
  cases historyReport history handle.stage <;> infer_instance

/-- Guards are derived from observable native permissions, not a Policy field
assuming the intended controller's correctness. Caps are treated separately. -/
def historyAllowsAction (history : List (VisibleEvent I)) : Action I → Prop
  | .review stage | .write stage _ => historyCursor history = stage.val ∧ historyWritten history stage = none
  | .advance stage => historyCursor history = stage.val ∧ historyWritten history stage ≠ none
  | .allocate handle tool => historyCursor history = handle.stage.val ∧ historyValidHandle history handle ∧
      tool ∈ I.eligible handle.stage ∧ tool ∉ historyUsed history ∧
      ∀ pair ∈ historyCommitments history, pair.1.stage ≠ handle.stage
  | .execute handle tool => historyCursor history = handle.stage.val ∧ historyValidHandle history handle ∧
      tool ∈ I.eligible handle.stage ∧ (handle, tool) ∈ historyCommitments history ∧
      (∀ pair ∈ historyExecutions history, pair.2 ≠ tool) ∧
      (∀ pair ∈ historyExecutions history, pair.1.stage ≠ handle.stage)
  | .stop | .abandon => True

instance historyAllowsAction_decidable (history : List (VisibleEvent I)) (action : Action I) :
    Decidable (historyAllowsAction history action) := by
  cases action <;> dsimp only [historyAllowsAction] <;> infer_instance

def referenceRule {Seed : Type*} (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ) (limit : ReferenceObservationLimit I) :
    PolicyRule I Seed := fun _seed history =>
  let action := referenceCandidateAction input initialAvailable risk limit history
  if historyAllowsAction history action then action else .abandon

theorem measurable_referenceRule {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ) (limit : ReferenceObservationLimit I) :
    MeasurableRule (referenceRule (Seed := Seed) input initialAvailable risk limit) :=
  (measurable_of_countable (fun history => referenceRule (Seed := Unit) input initialAvailable risk limit () history)).comp measurable_snd

theorem referenceRule_malformed {Seed : Type*} (input : StatisticalInput I) (initialAvailable : Finset I.Tool) (risk : ℚ)
    (limit : ReferenceObservationLimit I) (seed : Seed) (history : List (VisibleEvent I))
    (hbad : referenceAvailableReplay input initialAvailable risk history = none) :
    referenceRule input initialAvailable risk limit seed history = .abandon := by
  simp [referenceRule, referenceCandidateAction, hbad, historyAllowsAction]

theorem historyValidHandle_sound (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (mode : ResourceMode) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (handle : MismatchHandle I) (hhandle : historyValidHandle s.history handle) : validHandle s handle := by
  unfold historyValidHandle at hhandle
  rw [prefix_historyReport_early input C hearly mode accounting policy seed truth tapes hp handle.stage] at hhandle
  cases ht : s.ledger.reportTime handle.stage with
  | none => simp only [ht, Option.map_none] at hhandle
  | some time =>
    simp only [ht, Option.map_some] at hhandle
    rw [prefix_historyWritten input C mode accounting policy seed truth tapes hp handle.stage,
      prefix_historyWriteSerial input C mode accounting policy seed truth tapes hp handle.stage] at hhandle
    exact ⟨hhandle.1, hhandle.2.1, ⟨time, ht⟩⟩

theorem historyAllowsAction_sound (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (hactive : s.halted = false) (action : Action I) (hallow : historyAllowsAction s.history action) :
    ∃ next, Step input C .uncapped accounting tapes s action next := by
  cases action with
  | review stage =>
    change historyCursor s.history = stage.val ∧ historyWritten s.history stage = none at hallow
    rw [prefix_historyCursor input C .uncapped accounting policy seed truth tapes hp,
      prefix_historyWritten input C .uncapped accounting policy seed truth tapes hp stage] at hallow
    exact ⟨_, .review s stage ⟨hactive, hallow.1⟩ hallow.2 (.inl rfl)⟩
  | write stage bit =>
    change historyCursor s.history = stage.val ∧ historyWritten s.history stage = none at hallow
    rw [prefix_historyCursor input C .uncapped accounting policy seed truth tapes hp,
      prefix_historyWritten input C .uncapped accounting policy seed truth tapes hp stage] at hallow
    exact ⟨_, .write s stage bit ⟨hactive, hallow.1⟩ hallow.2 (.inl rfl)⟩
  | advance stage =>
    change historyCursor s.history = stage.val ∧ historyWritten s.history stage ≠ none at hallow
    rw [prefix_historyCursor input C .uncapped accounting policy seed truth tapes hp,
      prefix_historyWritten input C .uncapped accounting policy seed truth tapes hp stage] at hallow
    exact ⟨_, .advance s stage ⟨hactive, hallow.1⟩ hallow.2 (.inl rfl)⟩
  | allocate handle tool =>
    change historyCursor s.history = handle.stage.val ∧ historyValidHandle s.history handle ∧
      tool ∈ I.eligible handle.stage ∧ tool ∉ historyUsed s.history ∧
      (∀ pair ∈ historyCommitments s.history, pair.1.stage ≠ handle.stage) at hallow
    have hcursor : s.cursor = handle.stage.val := by
      simpa only [prefix_historyCursor input C .uncapped accounting policy seed truth tapes hp] using hallow.1
    have hhandle := historyValidHandle_sound input C hearly .uncapped accounting policy seed truth tapes hp handle hallow.2.1
    have hunused := (prefix_historyUnused_iff input C .uncapped accounting policy seed truth tapes hp tool).mp hallow.2.2.2.1
    have hstage : ∀ a ∈ s.ledger.commitments, a.handle.stage ≠ handle.stage := by
      intro a ha
      apply hallow.2.2.2.2 (a.handle, a.tool)
      rw [prefix_historyCommitments input C .uncapped accounting policy seed truth tapes hp]
      exact List.mem_map.mpr ⟨a, ha, rfl⟩
    exact ⟨_, .allocate s handle tool hactive hhandle hallow.2.2.1 hunused hstage (fun _ => hcursor) (.inl rfl)⟩
  | execute handle tool =>
    change historyCursor s.history = handle.stage.val ∧ historyValidHandle s.history handle ∧
      tool ∈ I.eligible handle.stage ∧ (handle, tool) ∈ historyCommitments s.history ∧
      (∀ pair ∈ historyExecutions s.history, pair.2 ≠ tool) ∧
      (∀ pair ∈ historyExecutions s.history, pair.1.stage ≠ handle.stage) at hallow
    have hcursor : s.cursor = handle.stage.val := by
      simpa only [prefix_historyCursor input C .uncapped accounting policy seed truth tapes hp] using hallow.1
    have hhandle := historyValidHandle_sound input C hearly .uncapped accounting policy seed truth tapes hp handle hallow.2.1
    have hcommitted : ∃ a ∈ s.ledger.commitments, a.handle = handle ∧ a.tool = tool := by
      have hm := hallow.2.2.2.1
      rw [prefix_historyCommitments input C .uncapped accounting policy seed truth tapes hp] at hm
      obtain ⟨a, ha, hpair⟩ := List.mem_map.mp hm
      exact ⟨a, ha, congrArg Prod.fst hpair, congrArg Prod.snd hpair⟩
    have hunused : ∀ e ∈ s.ledger.executions, e.tool ≠ tool := by
      intro e he
      apply hallow.2.2.2.2.1 (e.handle, e.tool)
      rw [prefix_historyExecutions input C .uncapped accounting policy seed truth tapes hp]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    have hstage : ∀ e ∈ s.ledger.executions, e.handle.stage ≠ handle.stage := by
      intro e he
      apply hallow.2.2.2.2.2 (e.handle, e.tool)
      rw [prefix_historyExecutions input C .uncapped accounting policy seed truth tapes hp]
      exact List.mem_map.mpr ⟨e, he, rfl⟩
    exact ⟨_, .execute s handle tool hactive hhandle hallow.2.2.1 hcommitted hunused hstage (fun _ => hcursor) (.inl rfl)⟩
  | stop => exact ⟨_, .stop s hactive⟩
  | abandon => exact ⟨_, .abandon s hactive⟩

theorem referenceRule_uncapped_legal {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) :
    LegalRule input C .uncapped accounting (referenceRule (Seed := Seed) input initialAvailable risk limit) := by
  intro seed truth tapes n s hp hactive
  let action := referenceCandidateAction input initialAvailable risk limit s.history
  by_cases hallow : historyAllowsAction s.history action
  · have hnext := historyAllowsAction_sound input C hearly accounting
      (referenceRule (Seed := Seed) input initialAvailable risk limit) seed truth tapes hp hactive action hallow
    simpa only [referenceRule, action, ite_eq_left hallow] using hnext
  · have hnext : Step input C .uncapped accounting tapes s .abandon (stopState s true) := .abandon s hactive
    exact ⟨_, by simpa only [referenceRule, action, ite_eq_right hallow] using hnext⟩

def referenceUncappedPolicy {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) : Policy input C .uncapped accounting Seed where
  rule := referenceRule input initialAvailable risk limit
  measurable_rule := measurable_referenceRule input initialAvailable risk limit
  legal := referenceRule_uncapped_legal input C hearly accounting initialAvailable risk limit

theorem referenceRule_allocate_mem {Seed : Type*} (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) (seed : Seed) (history : List (VisibleEvent I))
    (handle : MismatchHandle I) (tool : I.Tool)
    (haction : referenceRule input initialAvailable risk limit seed history = .allocate handle tool) :
    tool ∈ initialAvailable := by
  let action := referenceCandidateAction input initialAvailable risk limit history
  change (if historyAllowsAction history action then action else .abandon) = .allocate handle tool at haction
  by_cases hallow : historyAllowsAction history action
  · rw [ite_eq_left hallow] at haction
    exact referenceCandidateAction_allocate_mem input initialAvailable risk limit history handle tool haction
  · rw [ite_eq_right hallow] at haction
    cases haction

theorem referenceRule_usesOnly {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (initialAvailable : Finset I.Tool) (risk : ℚ) (limit : ReferenceObservationLimit I) :
    UsesOnly input C accounting (referenceRule (Seed := Seed) input initialAvailable risk limit) initialAvailable := by
  intro seed _ _ _ s _ _ handle tool haction
  exact referenceRule_allocate_mem input initialAvailable risk limit seed s.history handle tool haction

def referenceAvailableUncappedPolicy {Seed : Type*} [MeasurableSpace Seed] (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (limit : ReferenceObservationLimit I) : AvailablePolicy input C accounting initialAvailable Seed :=
  ⟨referenceUncappedPolicy input C hearly accounting initialAvailable risk limit,
    referenceRule_usesOnly input C accounting initialAvailable risk limit⟩

theorem referenceAvailableReplay_some_spec (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : referenceAvailableReplay input initialAvailable risk history = some cache) :
    (0 < risk ∧ risk ≤ 1 / 2) ∧
      history.foldlM (referenceAvailableStep input initialAvailable risk) (referenceReplayInitial I) = some cache ∧
      cache.phase ≠ .written ∧ cache.events.length ≤ I.stageCount ∧
      historyCursor cache.seen ≤ I.stageCount ∧ cache.seen = history := by
  by_cases hr : 0 < risk ∧ risk ≤ 1 / 2
  · simp only [referenceAvailableReplay, hr] at hparse
    obtain ⟨result, hfold, hlast⟩ := Option.bind_eq_some_iff.mp hparse
    by_cases hg : result.phase ≠ .written ∧ result.events.length ≤ I.stageCount ∧
        historyCursor result.seen ≤ I.stageCount ∧ result.seen = history
    · rw [ite_eq_left hg] at hlast
      have heq := Option.some.inj hlast
      subst result
      exact ⟨hr, hfold, hg⟩
    · rw [ite_eq_right hg] at hlast
      cases hlast
  · simp only [referenceAvailableReplay, hr, ite_false] at hparse
    cases hparse

theorem referenceAvailableReplay_initial (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (hrisk : 0 < risk) (hsmall : risk ≤ 1 / 2) :
    referenceAvailableReplay input initialAvailable risk [] = some (referenceReplayInitial I) := by
  have hr : 0 < risk ∧ risk ≤ 1 / 2 := ⟨hrisk, hsmall⟩
  simp only [referenceAvailableReplay, hr]
  simp [referenceReplayInitial, historyCursor]

private theorem historyCursor_append_write (history : List (VisibleEvent I))
    (stage : I.Stage) (bit : Bool) (serial : ℕ) :
    historyCursor (history ++ [.wrote stage bit serial]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance]

private theorem historyCursor_append_write_report (history : List (VisibleEvent I))
    (stage : I.Stage) (bit truth : Bool) (serial : ℕ) :
    historyCursor (history ++ [.wrote stage bit serial, .report stage truth serial]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance]

private theorem availableKind_written (I : Instance) (initialAvailable : Finset I.Tool)
    (cache : ReferenceReplayCache I) (stage : I.Stage) (bit : Bool) (serial : ℕ) :
    referenceAvailableKind I initialAvailable
      { cache with seen := cache.seen ++ [.wrote stage bit serial], phase := .written } =
        referenceAvailableKind I initialAvailable cache := by
  simp only [referenceAvailableKind, referenceReplayStage, historyCursor_append_write]

/-- The complete early packet is replayed as one actual Native write response.
The .written intermediate cache is not asserted to be a Native state. -/
theorem referenceAvailableReplay_write_packet (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : referenceAvailableReplay input initialAvailable risk history = some cache)
    (hhalt : cache.halted = false) (hphase : cache.phase = .testing) (stage : I.Stage)
    (hstage : referenceReplayStage I cache = some stage) (kind : ReferenceBudgetCase)
    (hkind : referenceAvailableKind I initialAvailable cache = some kind) (current : ℚ)
    (hcurrent : referenceReplayRisk risk cache = some current) (hlen : cache.events.length < I.stageCount)
    (bit truth : Bool) (serial : ℕ) (hserial : serial = (historyActions cache.seen).length) :
    referenceAvailableReplay input initialAvailable risk (history ++ [.wrote stage bit serial, .report stage truth serial]) =
      some { cache with
        seen := cache.seen ++ [.wrote stage bit serial, .report stage truth serial]
        events := cache.events ++ [(kind, decide (bit ≠ truth))]
        phase := .reported } := by
  let written : ReferenceReplayCache I :=
    { cache with seen := cache.seen ++ [.wrote stage bit serial], phase := .written }
  let reported : ReferenceReplayCache I :=
    { cache with
      seen := cache.seen ++ [.wrote stage bit serial, .report stage truth serial]
      events := cache.events ++ [(kind, decide (bit ≠ truth))]
      phase := .reported }
  have hw : referenceAvailableStep input initialAvailable risk cache (.wrote stage bit serial) = some written := by
    simp [referenceAvailableStep, hhalt, hstage, hkind, hcurrent, hphase, hserial, written]
  have hstage' : referenceReplayStage I written = some stage := by
    simpa only [written, referenceReplayStage, historyCursor_append_write] using hstage
  have hkind' : referenceAvailableKind I initialAvailable written = some kind := by
    simpa only [written, availableKind_written] using hkind
  have hwrite : historyWrite written.seen stage = some (bit, serial) := by
    simp [written, historyWrite, List.filterMap_append, eventWrite]
  have hr : referenceAvailableStep input initialAvailable risk written (.report stage truth serial) = some reported := by
    have hhalt' : written.halted = false := hhalt
    have hcurrent' : referenceReplayRisk risk written = some current := hcurrent
    simp only [referenceAvailableStep, hhalt', Bool.false_eq_true, ite_false]
    simp only [hstage', Option.bind_eq_bind, Option.bind_some, hwrite, hkind', hcurrent']
    rw [ite_eq_left (show True ∧ True ∧ written.phase = .written ∧
      written.events.length < I.stageCount from ⟨trivial, trivial, rfl, hlen⟩)]
    simp only [written, reported, hhalt, List.append_assoc, List.singleton_append]
  have hs := referenceAvailableReplay_some_spec input initialAvailable risk history cache hparse
  have hfold : (history ++ [VisibleEvent.wrote stage bit serial, VisibleEvent.report stage truth serial]).foldlM
      (referenceAvailableStep input initialAvailable risk) (referenceReplayInitial I) = some reported := by
    rw [List.foldlM_append, hs.2.1]
    simp [hw, hr]
  have hg : reported.phase ≠ .written ∧ reported.events.length ≤ I.stageCount ∧
      historyCursor reported.seen ≤ I.stageCount ∧
      reported.seen = history ++ [.wrote stage bit serial, .report stage truth serial] := by
    refine ⟨by simp [reported], ?_, ?_, ?_⟩
    · simpa only [reported, List.length_append, List.length_singleton] using Nat.succ_le_of_lt hlen
    · simpa only [reported, historyCursor_append_write_report] using hs.2.2.2.2.1
    · simpa only [reported] using congrArg (fun seen => seen ++ [.wrote stage bit serial, .report stage truth serial]) hs.2.2.2.2.2
  simp only [referenceAvailableReplay, hs.1]
  rw [hfold]
  exact ite_eq_left hg

def referencePhaseReportCount : ReferenceReplayPhase I → ℕ
  | .testing | .written => 0
  | .reported | .allocated _ | .executed _ => 1

def referenceCurrentLedgerFits (phase : ReferenceReplayPhase I) (s : State I) (stage : I.Stage) : Prop :=
  match phase with
  | .testing => s.ledger.written stage = none ∧ s.ledger.reportTime stage = none ∧
      (∀ a ∈ s.ledger.commitments, a.handle.stage ≠ stage) ∧
      (∀ e ∈ s.ledger.executions, e.handle.stage ≠ stage)
  | .written => False
  | .reported => s.ledger.written stage ≠ none ∧ s.ledger.reportTime stage ≠ none ∧
      (∀ a ∈ s.ledger.commitments, a.handle.stage ≠ stage) ∧
      (∀ e ∈ s.ledger.executions, e.handle.stage ≠ stage)
  | .allocated tool => ∃ handle : MismatchHandle I,
      handle.stage = stage ∧ validHandle s handle ∧ tool ∈ I.eligible stage ∧
      (∃ a ∈ s.ledger.commitments, a.handle = handle ∧ a.tool = tool) ∧
      (∀ e ∈ s.ledger.executions, e.tool ≠ tool) ∧
      (∀ e ∈ s.ledger.executions, e.handle.stage ≠ stage)
  | .executed tool => s.ledger.written stage ≠ none ∧
      ∃ e ∈ s.ledger.executions, e.handle.stage = stage ∧ e.tool = tool

def referenceEntryToolsFit (cache : ReferenceReplayCache I) : Prop :=
  match cache.phase with
  | .testing | .written | .reported => historyUsed cache.entryHistory = historyUsed cache.seen
  | .allocated tool | .executed tool =>
      insert tool (historyUsed cache.entryHistory) = historyUsed cache.seen ∧ tool ∉ historyUsed cache.entryHistory

/-- A pathwise induction invariant to be derived from the actual controller's
Prefix. It is not a field of the executable cache or Policy. The global
preservation theorem is still an outstanding proof, not an assumed input. -/
structure ReferenceStateAligned (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I) : Prop where
  parsed : referenceAvailableReplay input initialAvailable risk s.history = some cache
  seen : cache.seen = s.history
  halted : cache.halted = s.halted
  cursor : historyCursor cache.seen = s.cursor
  trace_count : cache.events.length = s.cursor + referencePhaseReportCount cache.phase
  testing_risk : cache.phase = .testing → ∃ current, referenceReplayRisk risk cache = some current
  current_fields : ∀ stage : I.Stage, s.cursor = stage.val → referenceCurrentLedgerFits cache.phase s stage
  entry_tools : referenceEntryToolsFit cache
  reported_update : referencePhaseReportCount cache.phase = 1 →
    ∀ stage : I.Stage, s.cursor = stage.val →
      ∃ kind entryRisk, referenceAvailableKind I initialAvailable cache = some kind ∧
        ReferenceBudgetValid entryRisk ∧ referenceReplayRisk risk cache =
          referenceBudgetStep kind (!(referenceReplayCorrect cache stage)) entryRisk
  correction_risk : ∀ tool, cache.phase = .allocated tool ∨ cache.phase = .executed tool →
    ∃ current, referenceReplayRisk risk cache = some current

/-- Original alignment target, currently only stated. It is not a cache/Policy
field and is not an input to the already-proved uncapped legality theorem. -/
def ReferenceControllerAlignment (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (Seed : Type*) [MeasurableSpace Seed] : Prop :=
  ∀ (initialAvailable : Finset I.Tool) (budget : ℚ), 0 < budget → budget ≤ 1 / 2 →
    ∀ (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
        (tapes : ReviewTapes input) (n : ℕ) (s : State I),
        Prefix input C .uncapped accounting
          (referenceUncappedPolicy (Seed := Seed) input C hearly accounting initialAvailable budget limit).rule
          seed truth tapes n s → s.halted = false →
        ∃ cache, referenceAvailableReplay input initialAvailable budget s.history = some cache ∧
          ReferenceStateAligned input initialAvailable budget cache s ∧
          decide (historyAllowsAction s.history (referenceCandidateAction input initialAvailable budget limit s.history)) = true

/-- Original infinite-rank no-observation target, currently only stated.
Every actual finite prefix is included, without an eventual-success condition. -/
def ReferenceInfiniteRankZeroReviews (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (Seed : Type*) [MeasurableSpace Seed] : Prop :=
  ∀ (initialAvailable : Finset I.Tool) (budget : ℚ), 0 < budget → budget ≤ 1 / 2 →
    PaperProofs.Structure.errorRank I.compatibility initialAvailable = ⊤ →
    ∀ (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
        (tapes : ReviewTapes input) (n : ℕ) (s : State I),
        Prefix input C .uncapped accounting
          (referenceUncappedPolicy (Seed := Seed) input C hearly accounting initialAvailable budget limit).rule
          seed truth tapes n s → ∀ stage : I.Stage, s.ledger.reviews stage = 0

/-- Original ideal-reference risk target, proved in ReferenceMassFlow. The
parser starts with budget/2, so the required risk cap is exactly budget/2. -/
def ReferenceRiskGuarantee (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) : Prop :=
  ∀ (hcurrent : C.IsCurrentAllocation) (initialAvailable : Finset I.Tool) (budget : ℚ),
    0 < budget → budget ≤ 1 / 2 →
      risk input C .uncapped accounting
        (referenceUncappedPolicy (Seed := Unit) input C hcurrent.1 accounting initialAvailable budget none).rule
        (Measure.dirac ()) ≤ ENNReal.ofReal ((budget : ℝ) / 2)

theorem referenceStateAligned_initial (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (hrisk : 0 < risk) (hsmall : risk ≤ 1 / 2) (truth : I.Stage → Bool) :
    ReferenceStateAligned input initialAvailable risk (referenceReplayInitial I) (initial truth) := by
  constructor
  · exact referenceAvailableReplay_initial input initialAvailable risk hrisk hsmall
  · rfl
  · rfl
  · rfl
  · rfl
  · intro _
    exact ⟨risk / 2, rfl⟩
  · intro stage _
    simp [referenceReplayInitial, referenceCurrentLedgerFits, initial]
  · simp [referenceEntryToolsFit, referenceReplayInitial, historyUsed, historyCommitments]
  · intro hcount
    norm_num [referenceReplayInitial, referencePhaseReportCount] at hcount
  · intro tool hphase
    rcases hphase with hphase | hphase <;> cases hphase

theorem referenceStateAligned_stage (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : ReferenceStateAligned input initialAvailable risk cache s) (stage : I.Stage)
    (hcursor : s.cursor = stage.val) : referenceReplayStage I cache = some stage := by
  have hc : historyCursor cache.seen = stage.val := haligned.cursor.trans hcursor
  have hs : stage.val < I.stageCount := stage.isLt
  simp [referenceReplayStage, hc, hs]

theorem referenceTestingAction_allowed_of_aligned (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) {Seed : Type*} (policy : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (risk : ℚ) (limit : ReferenceObservationLimit I)
    (cache : ReferenceReplayCache I) (haligned : ReferenceStateAligned input initialAvailable risk cache s)
    (hphase : cache.phase = .testing) (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    historyAllowsAction s.history (referenceTestingAction input initialAvailable risk limit cache stage) := by
  have hfields := haligned.current_fields stage hcursor
  simp only [hphase, referenceCurrentLedgerFits] at hfields
  have hw : historyWritten s.history stage = none := by
    rw [prefix_historyWritten input C .uncapped accounting policy seed truth tapes hp stage]
    exact hfields.1
  have hc : historyCursor s.history = stage.val :=
    (prefix_historyCursor input C .uncapped accounting policy seed truth tapes hp).trans hcursor
  rcases referenceTestingAction_supported input initialAvailable risk limit cache stage with hreview | ⟨bit, hwrite⟩ | habandon
  · rw [hreview]
    exact ⟨hc, hw⟩
  · rw [hwrite]
    exact ⟨hc, hw⟩
  · rw [habandon]
    trivial

/-- The finite Native permission guard is nonbinding in an aligned testing
state. The all-prefix alignment induction is not assumed to be complete. -/
theorem referenceRule_testing_eq_of_aligned {Seed : Type*} (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (initialAvailable : Finset I.Tool) (risk : ℚ)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input initialAvailable risk limit) seed truth tapes n s)
    (hactive : s.halted = false) (cache : ReferenceReplayCache I)
    (haligned : ReferenceStateAligned input initialAvailable risk cache s)
    (hphase : cache.phase = .testing) (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    referenceRule input initialAvailable risk limit seed s.history =
      referenceTestingAction input initialAvailable risk limit cache stage := by
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hs := referenceStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  have hc : referenceCandidateAction input initialAvailable risk limit s.history =
      referenceTestingAction input initialAvailable risk limit cache stage := by
    simp only [referenceCandidateAction, haligned.parsed, hh, Bool.false_eq_true, ite_false, hs, hphase]
  have hallow := referenceTestingAction_allowed_of_aligned input C accounting
    (referenceRule input initialAvailable risk limit) seed truth tapes hp initialAvailable risk limit cache haligned hphase stage hcursor
  simp only [referenceRule, hc, ite_eq_left hallow]

theorem referenceStateAligned_testing_ready (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : ReferenceStateAligned input initialAvailable risk cache s) (hphase : cache.phase = .testing)
    (stage : I.Stage) (hcursor : s.cursor = stage.val) :
    ∃ kind current, referenceAvailableKind I initialAvailable cache = some kind ∧
      referenceReplayRisk risk cache = some current ∧ ReferenceBudgetValid current ∧ cache.events.length < I.stageCount := by
  have hstage := referenceStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  obtain ⟨kind, hk⟩ := referenceAvailableRankCase_exists I initialAvailable stage (historyUsed cache.entryHistory)
  have hkind : referenceAvailableKind I initialAvailable cache = some kind := by
    simp [referenceAvailableKind, hstage, hk]
  obtain ⟨current, hcurrent⟩ := haligned.testing_risk hphase
  have hs := referenceAvailableReplay_some_spec input initialAvailable risk s.history cache haligned.parsed
  have hstart : ReferenceBudgetValid (risk / 2) := ⟨by linarith [hs.1.1], by linarith [hs.1.2]⟩
  have hvalid := (referenceBudgetPath_valid_floor cache.events (risk / 2) current hstart hcurrent).1
  have hcount : cache.events.length = s.cursor := by
    simpa only [hphase, referencePhaseReportCount, Nat.add_zero] using haligned.trace_count
  have hbound : s.cursor < I.stageCount := hcursor ▸ stage.isLt
  exact ⟨kind, current, hkind, hcurrent, hvalid, hcount.trans_lt hbound⟩

/-- An aligned testing state has a real lawful write successor, and its full
early response packet is accepted by the same availability-aware replay.
This closes that parser branch, without assuming a performance guarantee. -/
theorem referenceStateAligned_write_replay (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (risk : ℚ) (cache : ReferenceReplayCache I)
    (haligned : ReferenceStateAligned input initialAvailable risk cache s) (hphase : cache.phase = .testing)
    (hactive : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val) (bit : Bool) :
    ∃ kind nextCache,
      Step input C .uncapped accounting tapes s (.write stage bit)
        (record accounting s (.write stage bit) (writeResponses C s stage bit)
          (reportedWriteLedger C s stage bit) s.cursor false) ∧
      referenceAvailableReplay input initialAvailable risk
        (record accounting s (.write stage bit) (writeResponses C s stage bit)
          (reportedWriteLedger C s stage bit) s.cursor false).history = some nextCache ∧
      nextCache.phase = .reported ∧
      nextCache.events = cache.events ++ [(kind, decide (bit ≠ s.ledger.truth stage))] := by
  obtain ⟨kind, current, hkind, hcurrent, _, hlen⟩ :=
    referenceStateAligned_testing_ready input initialAvailable risk cache s haligned hphase stage hcursor
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hstage := referenceStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  have hserial : s.clock = (historyActions cache.seen).length := by
    rw [haligned.seen]
    exact (prefix_historyActions_length input C .uncapped accounting policy seed truth tapes hp).symm
  have hpacket := referenceAvailableReplay_write_packet input initialAvailable risk s.history cache haligned.parsed
    hh hphase stage hstage kind hkind current hcurrent hlen bit (s.ledger.truth stage) s.clock hserial
  let nextCache : ReferenceReplayCache I := { cache with
    seen := cache.seen ++ [.wrote stage bit s.clock, .report stage (s.ledger.truth stage) s.clock]
    events := cache.events ++ [(kind, decide (bit ≠ s.ledger.truth stage))]
    phase := .reported }
  have hfields := haligned.current_fields stage hcursor
  simp only [hphase, referenceCurrentLedgerFits] at hfields
  refine ⟨kind, nextCache, .write s stage bit ⟨hactive, hcursor⟩ hfields.1 (.inl rfl), ?_, rfl, rfl⟩
  simpa only [record, writeResponses, hearly, ite_true, writeLedger, nextCache, List.singleton_append] using hpacket

private theorem historyCursor_append_abandon (history : List (VisibleEvent I)) :
    historyCursor (history ++ [.abandoned]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, eventAdvance]

private theorem historyUsed_append_abandon (history : List (VisibleEvent I)) :
    historyUsed (history ++ [.abandoned]) = historyUsed history := by
  simp [historyUsed, historyCommitments, List.filterMap_append, List.filterMap_cons, eventCommitment]

private theorem availableKind_abandoned (I : Instance) (initialAvailable : Finset I.Tool)
    (cache : ReferenceReplayCache I) :
    referenceAvailableKind I initialAvailable { cache with seen := cache.seen ++ [.abandoned], halted := true } =
      referenceAvailableKind I initialAvailable cache := by
  simp only [referenceAvailableKind, referenceReplayStage, historyCursor_append_abandon]

private theorem replayCorrect_abandoned (cache : ReferenceReplayCache I) (stage : I.Stage) :
    referenceReplayCorrect { cache with seen := cache.seen ++ [.abandoned], halted := true } stage =
      referenceReplayCorrect cache stage := by
  simp [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append, List.filterMap_cons, eventWrite, eventReport]

private theorem currentLedgerFits_stop (phase : ReferenceReplayPhase I) (s : State I) (stage : I.Stage) (abandon : Bool) :
    referenceCurrentLedgerFits phase (stopState s abandon) stage ↔ referenceCurrentLedgerFits phase s stage := by
  cases phase <;> rfl

/-- Abandonment preserves the alignment, including a reported no-tool failure
whose continuation budget is none. It retains every previously paid charge. -/
theorem referenceStateAligned_abandon (input : StatisticalInput I) (initialAvailable : Finset I.Tool)
    (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : ReferenceStateAligned input initialAvailable risk cache s) (hactive : s.halted = false) :
    ∃ nextCache, ReferenceStateAligned input initialAvailable risk nextCache (stopState s true) := by
  let nextCache : ReferenceReplayCache I := { cache with seen := cache.seen ++ [.abandoned], halted := true }
  have hs := referenceAvailableReplay_some_spec input initialAvailable risk s.history cache haligned.parsed
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hstep : referenceAvailableStep input initialAvailable risk cache .abandoned = some nextCache := by
    simp [referenceAvailableStep, hh, hs.2.2.1, nextCache]
  have hfold : (s.history ++ [VisibleEvent.abandoned]).foldlM (referenceAvailableStep input initialAvailable risk)
      (referenceReplayInitial I) = some nextCache := by
    rw [List.foldlM_append, hs.2.1]
    simpa using hstep
  have hg : nextCache.phase ≠ .written ∧ nextCache.events.length ≤ I.stageCount ∧
      historyCursor nextCache.seen ≤ I.stageCount ∧ nextCache.seen = s.history ++ [.abandoned] := by
    exact ⟨hs.2.2.1, hs.2.2.2.1, by simpa only [nextCache, historyCursor_append_abandon] using hs.2.2.2.2.1,
      congrArg (fun seen => seen ++ [.abandoned]) haligned.seen⟩
  have hparse : referenceAvailableReplay input initialAvailable risk (stopState s true).history = some nextCache := by
    simp only [referenceAvailableReplay, hs.1, stopState, ite_true]
    rw [hfold]
    exact ite_eq_left hg
  refine ⟨nextCache, ?_⟩
  constructor
  · exact hparse
  · simpa only [nextCache, stopState, ite_true] using congrArg (fun seen => seen ++ [.abandoned]) haligned.seen
  · rfl
  · simpa only [nextCache, stopState, historyCursor_append_abandon] using haligned.cursor
  · exact haligned.trace_count
  · intro hphase
    exact haligned.testing_risk hphase
  · intro stage hcursor
    exact (currentLedgerFits_stop cache.phase s stage true).mpr (haligned.current_fields stage hcursor)
  · simpa only [referenceEntryToolsFit, nextCache, historyUsed_append_abandon] using haligned.entry_tools
  · intro hcount stage hcursor
    obtain ⟨kind, entryRisk, hk, hv, hu⟩ := haligned.reported_update hcount stage hcursor
    refine ⟨kind, entryRisk, ?_, hv, ?_⟩
    · simpa only [nextCache, availableKind_abandoned] using hk
    · simpa only [nextCache, referenceReplayRisk, replayCorrect_abandoned] using hu
  · intro tool hphase
    exact haligned.correction_risk tool hphase

private theorem historyCursor_append_observation (history : List (VisibleEvent I))
    (stage : I.Stage) (symbol : ℕ) :
    historyCursor (history ++ [.observation stage symbol]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance]

private theorem historyUsed_append_observation (history : List (VisibleEvent I))
    (stage : I.Stage) (symbol : ℕ) :
    historyUsed (history ++ [.observation stage symbol]) = historyUsed history := by
  simp [historyUsed, historyCommitments, List.filterMap_append, List.filterMap_cons, eventCommitment]

private theorem currentLedgerFits_review (phase : ReferenceReplayPhase I)
    (accounting : NormalAccounting I) (s : State I) (stage current : I.Stage) (symbol : ℕ) :
    referenceCurrentLedgerFits phase
      (record accounting s (.review stage) [.observation stage symbol]
        (reviewLedger s stage) s.cursor false) current ↔ referenceCurrentLedgerFits phase s current := by
  cases phase <;> rfl

/-- A genuine review consumes precisely the next tape symbol and preserves
the testing invariant. Its target-isSome obligation is explicit here; it
will be obtained from the actual testing action in the full Prefix proof. -/
theorem referenceStateAligned_review (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (tapes : ReviewTapes input)
    (initialAvailable : Finset I.Tool) (risk : ℚ) (cache : ReferenceReplayCache I) (s : State I)
    (haligned : ReferenceStateAligned input initialAvailable risk cache s)
    (hphase : cache.phase = .testing) (hactive : s.halted = false) (stage : I.Stage)
    (hcursor : s.cursor = stage.val)
    (htarget : (referenceAvailableCacheTarget I initialAvailable risk cache).isSome) :
    ∃ nextCache nextState,
      Step input C .uncapped accounting tapes s (.review stage) nextState ∧
      ReferenceStateAligned input initialAvailable risk nextCache nextState := by
  let symbol := tapes stage (s.ledger.reviews stage).toNat
  let nextCache : ReferenceReplayCache I := { cache with seen := cache.seen ++ [.observation stage symbol.val] }
  let nextState : State I := record accounting s (.review stage) [.observation stage symbol.val]
    (reviewLedger s stage) s.cursor false
  have hs := referenceAvailableReplay_some_spec input initialAvailable risk s.history cache haligned.parsed
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hstage := referenceStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  have hfields := haligned.current_fields stage hcursor
  simp only [hphase, referenceCurrentLedgerFits] at hfields
  have hport : s.ledger.written stage = none := by
    exact hfields.1
  have hstep : referenceAvailableStep input initialAvailable risk cache (.observation stage symbol.val) = some nextCache := by
    have halphabet : symbol.val < (input.experiment stage).alphabetSize := symbol.isLt
    simp [referenceAvailableStep, hh, hstage, hphase, halphabet, htarget, nextCache]
  have hfold : (s.history ++ [VisibleEvent.observation stage symbol.val]).foldlM
      (referenceAvailableStep input initialAvailable risk) (referenceReplayInitial I) = some nextCache := by
    rw [List.foldlM_append, hs.2.1]
    simpa using hstep
  have hg : nextCache.phase ≠ .written ∧ nextCache.events.length ≤ I.stageCount ∧
      historyCursor nextCache.seen ≤ I.stageCount ∧ nextCache.seen = nextState.history := by
    exact ⟨hs.2.2.1, hs.2.2.2.1,
      by simpa only [nextCache, historyCursor_append_observation] using hs.2.2.2.2.1,
      congrArg (fun seen => seen ++ [.observation stage symbol.val]) haligned.seen⟩
  have hparse : referenceAvailableReplay input initialAvailable risk nextState.history = some nextCache := by
    simp only [referenceAvailableReplay, hs.1, nextState, record]
    rw [hfold]
    exact ite_eq_left hg
  refine ⟨nextCache, nextState, .review s stage ⟨hactive, hcursor⟩ hport (.inl rfl), ?_⟩
  constructor
  · exact hparse
  · exact congrArg (fun seen => seen ++ [.observation stage symbol.val]) haligned.seen
  · exact hh
  · simpa only [nextCache, nextState, record, historyCursor_append_observation] using haligned.cursor
  · exact haligned.trace_count
  · intro _
    exact haligned.testing_risk hphase
  · intro current hcurrent
    exact (currentLedgerFits_review cache.phase accounting s stage current symbol.val).mpr (haligned.current_fields current hcurrent)
  · simpa only [referenceEntryToolsFit, nextCache, historyUsed_append_observation] using haligned.entry_tools
  · intro hcount
    simp only [nextCache, hphase, referencePhaseReportCount] at hcount
    contradiction
  · intro tool hcorrection
    simp only [nextCache, hphase] at hcorrection
    rcases hcorrection with h | h <;> cases h

private theorem budgetPath_append (initial : ℚ) (events tail : List ReferenceBudgetEvent) :
    referenceBudgetPath initial (events ++ tail) =
      (referenceBudgetPath initial events).bind (fun current => referenceBudgetPath current tail) := by
  induction events generalizing initial with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.cons_append, referenceBudgetPath]
    cases hstep : referenceBudgetStep event.1 event.2 initial with
    | none => rfl
    | some child => simpa only [Option.bind_some] using ih child

private theorem historyUsed_append_write_report (history : List (VisibleEvent I))
    (stage : I.Stage) (bit truth : Bool) (serial : ℕ) :
    historyUsed (history ++ [.wrote stage bit serial, .report stage truth serial]) = historyUsed history := by
  simp [historyUsed, historyCommitments, List.filterMap_append, List.filterMap_cons, eventCommitment]

/-- Full alignment after an actual early write/report packet. The budget
case is computed from the unchanged entry snapshot, before any commitment.
An unrepairable error is allowed to produce none in this reported phase. -/
theorem referenceStateAligned_write (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) {Seed : Type*}
    (policy : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting policy seed truth tapes n s)
    (initialAvailable : Finset I.Tool) (risk : ℚ) (cache : ReferenceReplayCache I)
    (haligned : ReferenceStateAligned input initialAvailable risk cache s) (hphase : cache.phase = .testing)
    (hactive : s.halted = false) (stage : I.Stage) (hcursor : s.cursor = stage.val) (bit : Bool) :
    ∃ nextCache nextState,
      Step input C .uncapped accounting tapes s (.write stage bit) nextState ∧
      ReferenceStateAligned input initialAvailable risk nextCache nextState := by
  obtain ⟨kind, current, hkind, hcurrent, hvalid, hlen⟩ :=
    referenceStateAligned_testing_ready input initialAvailable risk cache s haligned hphase stage hcursor
  let nextCache : ReferenceReplayCache I := { cache with
    seen := cache.seen ++ [.wrote stage bit s.clock, .report stage (s.ledger.truth stage) s.clock]
    events := cache.events ++ [(kind, decide (bit ≠ s.ledger.truth stage))]
    phase := .reported }
  let nextState : State I := record accounting s (.write stage bit) (writeResponses C s stage bit)
    (reportedWriteLedger C s stage bit) s.cursor false
  have hh : cache.halted = false := haligned.halted.trans hactive
  have hstage := referenceStateAligned_stage input initialAvailable risk cache s haligned stage hcursor
  have hserial : s.clock = (historyActions cache.seen).length := by
    rw [haligned.seen]
    exact (prefix_historyActions_length input C .uncapped accounting policy seed truth tapes hp).symm
  have hpacket := referenceAvailableReplay_write_packet input initialAvailable risk s.history cache haligned.parsed
    hh hphase stage hstage kind hkind current hcurrent hlen bit (s.ledger.truth stage) s.clock hserial
  have hparse : referenceAvailableReplay input initialAvailable risk nextState.history = some nextCache := by
    simpa only [record, writeResponses, hearly, ite_true, writeLedger, nextCache, nextState,
      List.singleton_append] using hpacket
  have hfields := haligned.current_fields stage hcursor
  simp only [hphase, referenceCurrentLedgerFits] at hfields
  have hcorrect : referenceReplayCorrect nextCache stage = decide (bit = s.ledger.truth stage) := by
    simp [referenceReplayCorrect, nextCache, historyWrite, historyReport, List.filterMap_append,
      List.filterMap_cons, eventWrite, eventReport]
  have hnextKind : referenceAvailableKind I initialAvailable nextCache = some kind := by
    simpa only [nextCache, referenceAvailableKind, referenceReplayStage,
      historyCursor_append_write_report] using hkind
  have hnextRisk : referenceReplayRisk risk nextCache =
      referenceBudgetStep kind (!(referenceReplayCorrect nextCache stage)) current := by
    rw [hcorrect]
    simp only [referenceReplayRisk, nextCache, budgetPath_append, referenceBudgetPath]
    change (referenceReplayRisk risk cache).bind
      (fun child => (referenceBudgetStep kind (decide (bit ≠ s.ledger.truth stage)) child).bind some) = _
    rw [hcurrent]
    simp
  refine ⟨nextCache, nextState, .write s stage bit ⟨hactive, hcursor⟩ hfields.1 (.inl rfl), ?_⟩
  constructor
  · exact hparse
  · simpa only [nextCache, nextState, record, writeResponses, hearly, ite_true, writeLedger,
      List.singleton_append] using congrArg
        (fun seen => seen ++ [.wrote stage bit s.clock, .report stage (s.ledger.truth stage) s.clock]) haligned.seen
  · exact hh
  · simpa only [nextCache, nextState, record, historyCursor_append_write_report] using haligned.cursor
  · have hcount := haligned.trace_count
    simp only [hphase, referencePhaseReportCount, Nat.add_zero] at hcount
    simpa only [nextCache, nextState, record, List.length_append, List.length_singleton,
      referencePhaseReportCount] using congrArg (fun count => count + 1) hcount
  · intro htesting
    cases htesting
  · intro currentStage hcurrentCursor
    have heq : currentStage = stage := Fin.ext (hcurrentCursor.symm.trans hcursor)
    subst currentStage
    simp only [nextCache, referenceCurrentLedgerFits, nextState, record, reportedWriteLedger,
      hearly, ite_true, writeLedger, Function.update_self]
    exact ⟨by simp, by simp, hfields.2.2.1, hfields.2.2.2⟩
  · simpa only [referenceEntryToolsFit, nextCache, hphase, historyUsed_append_write_report]
      using haligned.entry_tools
  · intro _ currentStage hcurrentCursor
    have heq : currentStage = stage := Fin.ext (hcurrentCursor.symm.trans hcursor)
    subst currentStage
    exact ⟨kind, current, hnextKind, hvalid, hnextRisk⟩
  · intro tool hcorrection
    rcases hcorrection with h | h <;> cases h


end PaperProofs.Common.Native

