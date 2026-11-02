module

public import PaperProofs.Common.ReferenceDecisionRealization
public import PaperProofs.Common.NativeHorizon

/-!
Pathwise infinite-rank branch of the unchanged reference controller. The proof
uses the actual availability-aware replay and the genuine maximum-child picker.
Its invariant is proved from accepted events, not stored in a cache or Policy.
The infinite-rank branch has zero reviews, no abandonment, finite returned-action
completion, and successful completion on every sample. Its structural action
bound is proved in uncapped mode from zero reviews and one-use tools/ports;
no Native review quota or normal-call certificate is imposed. The general
finite-rank risk-budget induction remains a separate obligation.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

private theorem cursor_of_stage (cache : ReferenceReplayCache I) (stage : I.Stage)
    (hstage : referenceReplayStage I cache = some stage) :
    historyCursor cache.seen = stage.val := by
  unfold referenceReplayStage at hstage
  split_ifs at hstage with hb
  exact congrArg (fun i : I.Stage => i.val) (Option.some.inj hstage)

private theorem rank_top_children (stage : I.Stage) (remaining : Finset I.Tool)
    (h : errorRank (I.compatibility.drop stage.val) remaining = ⊤) :
    errorRank (I.compatibility.drop (stage.val + 1)) remaining = ⊤ ∧
      badChildRank (I.eligible stage) (I.compatibility.drop (stage.val + 1)) remaining = ⊤ := by
  rw [List.drop_eq_getElem_cons stage.isLt] at h
  exact (errorRank_cons_eq_top_iff _ _ _).mp h

private theorem availableKind_top (available : Finset I.Tool) (cache : ReferenceReplayCache I)
    (stage : I.Stage) (hstage : referenceReplayStage I cache = some stage)
    (hrank : errorRank (I.compatibility.drop (historyCursor cache.seen))
      (available \ historyUsed cache.entryHistory) = ⊤) :
    referenceAvailableKind I available cache = some .infiniteRank := by
  have hc := cursor_of_stage cache stage hstage
  have hk : referenceAvailableRankCase I available stage (historyUsed cache.entryHistory) = some .infiniteRank := by
    apply (referenceCaseOfRanks_infinite_iff _ _).mpr
    simpa only [referenceRankAt_eq, referenceRank_remaining, hc] using hrank
  simp only [referenceAvailableKind, hstage, Option.bind_eq_bind, Option.bind_some, hk]

private theorem used_no_commit (history : List (VisibleEvent I)) (event : VisibleEvent I)
    (h : eventCommitment event = none) :
    historyUsed (history ++ [event]) = historyUsed history := by
  simp [historyUsed, historyCommitments, List.filterMap_append, h]

private theorem cursor_no_advance (history : List (VisibleEvent I)) (event : VisibleEvent I)
    (h : eventAdvance event = none) :
    historyCursor (history ++ [event]) = historyCursor history := by
  simp [historyCursor, List.filterMap_append, h]

private theorem observations_no_observation (history : List (VisibleEvent I)) (event : VisibleEvent I)
    (h : ∀ stage : I.Stage, eventObservation stage event = none) (stage : I.Stage) :
    historyObservations (history ++ [event]) stage = historyObservations history stage := by
  simp [historyObservations, List.filterMap_append, h]

private theorem some_if_some {α : Type*} (P : Prop) [Decidable P] (value next : α)
    (h : (if P then some value else none) = some next) : P ∧ next = value := by
  by_cases hp : P
  · rw [ite_eq_left hp] at h
    exact ⟨hp, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hp] at h
    cases h

/-- Proof-only replay invariant. `repaired` refers to the actual selected tool
already committed in the visible history, rather than a future tool oracle. -/
private structure InfiniteReplayInvariant (available : Finset I.Tool) (cache : ReferenceReplayCache I) : Prop where
  entry_tools : referenceEntryToolsFit cache
  rank : errorRank (I.compatibility.drop (historyCursor cache.seen))
    (available \ historyUsed cache.entryHistory) = ⊤
  repaired : ∀ tool, cache.phase = .allocated tool ∨ cache.phase = .executed tool →
    errorRank (I.compatibility.drop (historyCursor cache.seen + 1))
      (available \ historyUsed cache.seen) = ⊤
  no_observations : ∀ stage : I.Stage, historyObservations cache.seen stage = []

private theorem infiniteReplay_initial (available : Finset I.Tool)
    (htop : errorRank I.compatibility available = ⊤) :
    InfiniteReplayInvariant available (referenceReplayInitial I) := by
  constructor
  · rfl
  · simpa [referenceReplayInitial, historyCursor, historyUsed, historyCommitments] using htop
  · intro tool hphase
    rcases hphase with hphase | hphase <;> cases hphase
  · intro stage
    rfl

private theorem infiniteReplay_step (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hinv : InfiniteReplayInvariant available cache)
    (hstep : referenceAvailableStep input available budget cache event = some next) :
    InfiniteReplayInvariant available next := by
  cases hh : cache.halted with
  | true => simp only [referenceAvailableStep, hh, ite_true] at hstep; cases hstep
  | false =>
    cases event with
    | observation stage symbol =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨current, hstage, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, _⟩ := some_if_some _ _ _ hstep
      have hk := availableKind_top available cache current hstage hinv.rank
      cases hr : referenceReplayRisk budget cache <;>
        simp [referenceAvailableCacheTarget, hh, hg.2.2.1, hk, hr, referenceBudgetTarget] at hg
    | wrote stage bit serial =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      subst next
      have hu := used_no_commit cache.seen (.wrote stage bit serial) rfl
      have hc := cursor_no_advance cache.seen (.wrote stage bit serial) rfl
      constructor
      · simpa only [referenceEntryToolsFit, hu, hg.2.2] using hinv.entry_tools
      · simpa only [hc] using hinv.rank
      · intro tool hphase
        rcases hphase with hphase | hphase <;> cases hphase
      · intro i
        rw [observations_no_observation cache.seen (.wrote stage bit serial) (by intro i; rfl)]
        exact hinv.no_observations i
    | report stage truth serial =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      subst next
      have hu := used_no_commit cache.seen (.report stage truth serial) rfl
      have hc := cursor_no_advance cache.seen (.report stage truth serial) rfl
      constructor
      · simpa only [referenceEntryToolsFit, hu, hg.2.2.1] using hinv.entry_tools
      · simpa only [hc] using hinv.rank
      · intro tool hphase
        rcases hphase with hphase | hphase <;> cases hphase
      · intro i
        rw [observations_no_observation cache.seen (.report stage truth serial) (by intro i; rfl)]
        exact hinv.no_observations i
    | committed handle tool =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨stage, hstage, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      subst next
      have hc := cursor_no_advance cache.seen (.committed handle tool) rfl
      have hu : historyUsed (cache.seen ++ [.committed handle tool]) = insert tool (historyUsed cache.seen) := by
        simp [historyUsed, historyCommitments, List.filterMap_append, eventCommitment, Finset.union_comm]
      have hentry : historyUsed cache.entryHistory = historyUsed cache.seen := by
        simpa only [referenceEntryToolsFit, hg.1] using hinv.entry_tools
      have hpick := referenceAvailableRepairTool_spec I available stage (historyUsed cache.entryHistory) tool hg.2.2.2.2.2
      constructor
      · simp only [referenceEntryToolsFit, hu]
        exact ⟨congrArg (insert tool) hentry, (Finset.mem_sdiff.mp (Finset.mem_inter.mp hpick.1).2).2⟩
      · simpa only [hc] using hinv.rank
      · intro _ _
        have hcstage := cursor_of_stage cache stage hstage
        have hchildren := rank_top_children stage (available \ historyUsed cache.entryHistory)
          (by simpa only [hcstage] using hinv.rank)
        have herase : available \ insert tool (historyUsed cache.seen) =
            (available \ historyUsed cache.entryHistory).erase tool := by
          rw [hentry]
          ext x
          simp [and_left_comm]
        simpa only [hc, hcstage, hu, herase] using hpick.2.trans hchildren.2
      · intro i
        rw [observations_no_observation cache.seen (.committed handle tool) (by intro i; rfl)]
        exact hinv.no_observations i
    | executed handle tool =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      subst next
      have hc := cursor_no_advance cache.seen (.executed handle tool) rfl
      have hu := used_no_commit cache.seen (.executed handle tool) rfl
      constructor
      · simpa only [referenceEntryToolsFit, hu, hg.1] using hinv.entry_tools
      · simpa only [hc] using hinv.rank
      · intro _ _
        simpa only [hc, hu] using hinv.repaired tool (Or.inl hg.1)
      · intro i
        rw [observations_no_observation cache.seen (.executed handle tool) (by intro i; rfl)]
        exact hinv.no_observations i
    | advanced stage =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨current, hstage, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      subst next
      have hc : historyCursor (cache.seen ++ [.advanced stage]) = historyCursor cache.seen + 1 := by
        simp [historyCursor, List.filterMap_append, eventAdvance]
      have hu := used_no_commit cache.seen (.advanced stage) rfl
      constructor
      · rfl
      · simp only [hc, hu]
        rcases hg.2 with ⟨hphase, _⟩ | ⟨tool, hphase⟩
        · have hentry : historyUsed cache.entryHistory = historyUsed cache.seen := by
            simpa only [referenceEntryToolsFit, hphase] using hinv.entry_tools
          have hcstage := cursor_of_stage cache current hstage
          simpa only [hcstage, hentry] using (rank_top_children current (available \ historyUsed cache.entryHistory)
            (by simpa only [hcstage] using hinv.rank)).1
        · exact hinv.repaired tool (Or.inr hphase)
      · intro tool hphase
        rcases hphase with hphase | hphase <;> cases hphase
      · intro i
        rw [observations_no_observation cache.seen (.advanced stage) (by intro i; rfl)]
        exact hinv.no_observations i
    | stopped =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      subst next
      have hc := cursor_no_advance cache.seen .stopped rfl
      have hu := used_no_commit cache.seen .stopped rfl
      constructor
      · simpa only [referenceEntryToolsFit, hu] using hinv.entry_tools
      · simpa only [hc] using hinv.rank
      · intro tool hphase
        simpa only [hc, hu] using hinv.repaired tool hphase
      · intro i
        rw [observations_no_observation cache.seen .stopped (by intro i; rfl)]
        exact hinv.no_observations i
    | abandoned =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
      subst next
      have hc := cursor_no_advance cache.seen .abandoned rfl
      have hu := used_no_commit cache.seen .abandoned rfl
      constructor
      · simpa only [referenceEntryToolsFit, hu] using hinv.entry_tools
      · simpa only [hc] using hinv.rank
      · intro tool hphase
        simpa only [hc, hu] using hinv.repaired tool hphase
      · intro i
        rw [observations_no_observation cache.seen .abandoned (by intro i; rfl)]
        exact hinv.no_observations i

private theorem infiniteReplay_fold (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (events : List (VisibleEvent I)) (cache next : ReferenceReplayCache I)
    (hinv : InfiniteReplayInvariant available cache)
    (hfold : events.foldlM (referenceAvailableStep input available budget) cache = some next) :
    InfiniteReplayInvariant available next := by
  induction events generalizing cache with
  | nil =>
    have heq : cache = next := Option.some.inj hfold
    exact heq ▸ hinv
  | cons event rest ih =>
    simp only [List.foldlM_cons] at hfold
    obtain ⟨middle, hstep, htail⟩ := Option.bind_eq_some_iff.mp hfold
    exact ih middle (infiniteReplay_step input available budget cache middle event hinv hstep) htail

private theorem infiniteReplay_of_parse (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (htop : errorRank I.compatibility available = ⊤)
    (hparse : referenceAvailableReplay input available budget history = some cache) :
    InfiniteReplayInvariant available cache :=
  infiniteReplay_fold input available budget history (referenceReplayInitial I) cache
    (infiniteReplay_initial available htop)
    (referenceAvailableReplay_some_spec input available budget history cache hparse).2.1

/-- The original entry rank stays infinite in every accepted phase, before
and after any correction. The selected corrected tail is also infinite. -/
theorem referenceAvailableReplay_rank_top_of_infinite_rank
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (htop : errorRank I.compatibility available = ⊤)
    (hparse : referenceAvailableReplay input available budget history = some cache) :
    errorRank (I.compatibility.drop (historyCursor cache.seen))
        (available \ historyUsed cache.entryHistory) = ⊤ ∧
      ∀ tool, cache.phase = .allocated tool ∨ cache.phase = .executed tool →
        errorRank (I.compatibility.drop (historyCursor cache.seen + 1))
          (available \ historyUsed cache.seen) = ⊤ := by
  have hinv := infiniteReplay_of_parse input available budget history cache htop hparse
  exact ⟨hinv.rank, hinv.repaired⟩

/-- Every history accepted by the actual reference replay has no observations
when the original initial-availability rank is infinite. No report-kind list
or actual-run success premise is supplied. -/
theorem referenceAvailableReplay_observations_nil_of_infinite_rank
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (htop : errorRank I.compatibility available = ⊤)
    (hparse : referenceAvailableReplay input available budget history = some cache) :
    ∀ stage : I.Stage, historyObservations history stage = [] := by
  have hs := referenceAvailableReplay_some_spec input available budget history cache hparse
  have hinv := infiniteReplay_of_parse input available budget history cache htop hparse
  rw [← hs.2.2.2.2.2]
  exact hinv.no_observations

/-- All actual finite prefixes, for any seed type, any original observation
limit, and every truth/tape path, spend zero review calls in infinite rank. -/
theorem prefix_reference_reviews_zero_of_infinite_rank {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget limit)
      seed truth tapes n s) :
    ∀ stage : I.Stage, s.ledger.reviews stage = 0 := by
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    hbudget hsmall limit seed truth tapes hp
  have hobs := referenceAvailableReplay_observations_nil_of_infinite_rank input available budget
    s.history cache htop haligned.parsed
  intro stage
  rw [← prefix_historyObservations_length input C .uncapped accounting
    (referenceRule input available budget limit) seed truth tapes hp stage, hobs stage]
  rfl

/-- The original stated infinite-rank zero-review target, now proved. -/
theorem referenceInfiniteRankZeroReviews (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (Seed : Type*) [MeasurableSpace Seed] :
    ReferenceInfiniteRankZeroReviews input C hearly accounting Seed := by
  intro available budget hbudget hsmall htop limit seed truth tapes n s hp
  exact prefix_reference_reviews_zero_of_infinite_rank input C hearly accounting available budget
    hbudget hsmall htop limit seed truth tapes hp

private theorem repair_exists_of_rank_top (available : Finset I.Tool) (cache : ReferenceReplayCache I)
    (stage : I.Stage) (hstage : referenceReplayStage I cache = some stage)
    (hrank : errorRank (I.compatibility.drop (historyCursor cache.seen))
      (available \ historyUsed cache.entryHistory) = ⊤) :
    ∃ tool, referenceAvailableRepairTool I available stage (historyUsed cache.entryHistory) = some tool := by
  have hc := cursor_of_stage cache stage hstage
  have hbad := (rank_top_children stage (available \ historyUsed cache.entryHistory)
    (by simpa only [hc] using hrank)).2
  cases hpick : referenceAvailableRepairTool I available stage (historyUsed cache.entryHistory) with
  | some tool => exact ⟨tool, rfl⟩
  | none =>
    have hp : pickGenericMaxRankTool I.toolCount (I.eligible stage)
        (I.compatibility.drop (stage.val + 1)) (available \ historyUsed cache.entryHistory) = none := by
      simpa only [referenceAvailableRepairTool, referenceRepairTool, referenceRank_remaining] using hpick
    have hzero := (badChildRank_eq_zero_iff (I.eligible stage)
      (I.compatibility.drop (stage.val + 1)) (available \ historyUsed cache.entryHistory)).mpr
      ((pickGenericMaxRankTool_eq_none _ _ _ _).mp hp)
    exact (ENat.zero_ne_top (hzero.symm.trans hbad)).elim

/-- On an actual infinite-rank reference prefix the original candidate never
abandons. This includes the finite quota variants, since they never review. -/
theorem referenceRule_ne_abandon_of_infinite_rank {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget limit)
      seed truth tapes n s) (hactive : s.halted = false) :
    referenceRule input available budget limit seed s.history ≠ .abandon := by
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    hbudget hsmall limit seed truth tapes hp
  have hinv := infiniteReplay_of_parse input available budget s.history cache htop haligned.parsed
  have hh : cache.halted = false := haligned.halted.trans hactive
  rw [referenceRule_eq_candidate_of_prefix input C hearly accounting available budget
    hbudget hsmall limit seed truth tapes hp]
  cases hstage : referenceReplayStage I cache with
  | none =>
    have hcursor : historyCursor s.history = I.stageCount := by
      have hb := (prefix_cursorInvariant input C .uncapped accounting
        (referenceRule input available budget limit) seed truth tapes hp).bound
      have hnot : ¬ historyCursor cache.seen < I.stageCount := by
        intro h
        simp [referenceReplayStage, h] at hstage
      rw [← haligned.seen, haligned.cursor]
      rw [haligned.cursor] at hnot
      omega
    simp [referenceCandidateAction, haligned.parsed, hh, hstage, hcursor]
  | some stage =>
    have hc : s.cursor = stage.val := haligned.cursor.symm.trans (cursor_of_stage cache stage hstage)
    have hk := availableKind_top available cache stage hstage hinv.rank
    cases hphase : cache.phase with
    | testing => simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, referenceTestingAction, hk]
    | written => exact ((referenceAvailableReplay_some_spec input available budget s.history cache
        haligned.parsed).2.2.1 hphase).elim
    | reported =>
      cases hcorrect : referenceReplayCorrect cache stage with
      | true => simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hcorrect]
      | false =>
        obtain ⟨kind, entryRisk, hk', _, hr⟩ := haligned.reported_update
          (by simp [hphase, referencePhaseReportCount]) stage hc
        have hkind : kind = .infiniteRank := Option.some.inj (hk'.symm.trans hk)
        subst kind
        have hrisk : referenceReplayRisk budget cache = some entryRisk := by
          simpa only [referenceBudgetStep] using hr
        have hf := haligned.current_fields stage hc
        simp only [referenceCurrentLedgerFits, hphase] at hf
        obtain ⟨bit, hwritten⟩ := Option.ne_none_iff_exists'.mp hf.1
        have hwrite := prefix_historyWrite input C .uncapped accounting
          (referenceRule input available budget limit) seed truth tapes hp stage
        rw [hwritten] at hwrite
        have hvisible : referenceVisibleHandle s.history stage = some ⟨stage, s.ledger.writeSerial stage⟩ := by
          simp [referenceVisibleHandle, hwrite]
        obtain ⟨tool, hpick⟩ := repair_exists_of_rank_top available cache stage hstage hinv.rank
        simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hcorrect, hrisk, hvisible, hpick]
    | allocated tool =>
      obtain ⟨handle, hhandle, hvalid, _, _, _, _⟩ := by
        simpa only [hphase, referenceCurrentLedgerFits] using haligned.current_fields stage hc
      have hvisible := prefix_visibleHandle_of_valid input C hearly .uncapped accounting
        (referenceRule input available budget limit) seed truth tapes hp handle hvalid
      rw [hhandle] at hvisible
      simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase, hvisible]
    | executed tool => simp [referenceCandidateAction, haligned.parsed, hh, hstage, hphase]

/-- A structural returned-action bound for a zero-observation run; this has
no review quota, resource cap, normal-call bound, or Native-mode premise. -/
def zeroReviewActionBound (I : Instance) : ℕ :=
  I.toolCount + I.toolCount + I.stageCount + I.stageCount + 1

theorem prefix_length_le_of_zero_reviews {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (policy : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C mode accounting policy seed truth tapes n s)
    (hzero : ∀ stage : I.Stage, s.ledger.reviews stage = 0) :
    n ≤ zeroReviewActionBound I := by
  have hwf := prefix_ledgerWellFormed input C mode accounting policy seed truth tapes hp
  have hcursor := (prefix_cursorInvariant input C mode accounting policy seed truth tapes hp).bound
  have hcommitments : s.ledger.commitments.length ≤ I.toolCount := by
    have hh := hwf.commitment_tools.length_le_card
    simpa only [List.length_map, Instance.Tool, Fintype.card_fin] using hh
  have hexecutions : s.ledger.executions.length ≤ I.toolCount :=
    (Ledger.execution_count_le hwf).trans (min_le_right _ _)
  have hwritten : (writtenPorts s.ledger).card ≤ I.stageCount := by
    have hh := Finset.card_le_card (Finset.filter_subset (fun stage : I.Stage => s.ledger.written stage ≠ none) Finset.univ)
    simpa only [writtenPorts, Finset.card_univ, Instance.Stage, Instance.stageCount, Fintype.card_fin] using hh
  have hhalted : (if s.halted then (1 : ℕ∞) else 0) ≤ 1 := by
    cases s.halted <;> simp
  have ht := add_le_add
    (add_le_add
      (add_le_add (add_le_add (ENat.natCast_le_natCast.mpr hcommitments)
        (ENat.natCast_le_natCast.mpr hexecutions))
        (ENat.natCast_le_natCast.mpr hcursor))
      (ENat.natCast_le_natCast.mpr hwritten)) hhalted
  have hprogress : actionProgress s ≤ (zeroReviewActionBound I : ℕ∞) := by
    simpa only [actionProgress, hzero, Finset.sum_const_zero, zero_add,
      zeroReviewActionBound, ENat.natCast_add, ENat.natCast_one] using ht
  rw [prefix_actionProgress input C mode accounting policy seed truth tapes hp] at hprogress
  exact ENat.natCast_le_natCast.mp hprogress

/-- Infinite-rank reference paths halt after a uniformly finite number of
returned actions in uncapped mode. The bound is derived from their proved
zero review count, rather than imposed on uncapped comparators. -/
theorem referenceRun_halted_of_infinite_rank {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (sample : Seed × input.World) :
    (run input C .uncapped accounting (referenceRule input available budget limit)
      sample (zeroReviewActionBound I + 1)).halted = true := by
  by_contra hh
  have ha : (run input C .uncapped accounting (referenceRule input available budget limit)
      sample (zeroReviewActionBound I + 1)).halted = false := Bool.eq_false_iff.mpr hh
  have hp := run_prefix_of_active input C .uncapped accounting (referenceRule input available budget limit)
    (referenceRule_uncapped_legal input C hearly accounting available budget limit) sample
    (zeroReviewActionBound I + 1) ha
  have hz := prefix_reference_reviews_zero_of_infinite_rank input C hearly accounting available budget
    hbudget hsmall htop limit sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hn := prefix_length_le_of_zero_reviews input C .uncapped accounting
    (referenceRule input available budget limit) sample.1 (input.truthAt sample.2)
    (worldTapes input sample.2) hp hz
  omega

private theorem replay_single_after (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hparse : referenceAvailableReplay input available budget history = some cache)
    (hnext : referenceAvailableReplay input available budget (history ++ [event]) = some next) :
    referenceAvailableStep input available budget cache event = some next := by
  have hs := referenceAvailableReplay_some_spec input available budget history cache hparse
  have hs' := referenceAvailableReplay_some_spec input available budget (history ++ [event]) next hnext
  rw [List.foldlM_append, hs.2.1] at hs'
  simpa using hs'.2.1

/-- An actual reference advance is preceded by an actually correct write or
an actual repair execution, for any initial availability and observation limit.
This is execution correctness, without a risk or completion assumption. -/
theorem referenceAdvance_correct_or_repaired {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s next : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget limit)
      seed truth tapes n s) (stage : I.Stage)
    (hstep : Step input C .uncapped accounting tapes s (.advance stage) next)
    (haction : referenceRule input available budget limit seed s.history = .advance stage) :
    s.ledger.written stage = some (s.ledger.truth stage) ∨
      ∃ e ∈ s.ledger.executions, e.handle.stage = stage := by
  have hpnext : Prefix input C .uncapped accounting (referenceRule input available budget limit)
      seed truth tapes (n + 1) next := .next hp (haction ▸ hstep)
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    hbudget hsmall limit seed truth tapes hp
  obtain ⟨nextCache, hnextAligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    hbudget hsmall limit seed truth tapes hpnext
  cases hstep with
  | advance stage live written resources =>
    have hsingle := replay_single_after input available budget s.history cache nextCache
      (.advanced stage) haligned.parsed hnextAligned.parsed
    have hh : cache.halted = false := haligned.halted.trans live.1
    simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hsingle
    obtain ⟨current, _, hsingle⟩ := Option.bind_eq_some_iff.mp hsingle
    obtain ⟨_, _, hsingle⟩ := Option.bind_eq_some_iff.mp hsingle
    obtain ⟨hg, _⟩ := some_if_some _ _ _ hsingle
    have heq : stage = current := hg.1
    subst current
    rcases hg.2 with ⟨hphase, hcorrect⟩ | ⟨tool, hphase⟩
    · have hf := haligned.current_fields stage live.2
      simp only [referenceCurrentLedgerFits, hphase] at hf
      obtain ⟨bit, hw, hr, hb⟩ := prefix_written_report_packet input C hearly .uncapped accounting
        (referenceRule input available budget limit) seed truth tapes hp stage hf.1 hf.2.1
      have hbit : bit = s.ledger.truth stage := by
        simpa only [referenceReplayCorrect, haligned.seen, hw, hr, decide_eq_true_eq, and_true] using hcorrect
      exact Or.inl (hb.trans (congrArg some hbit))
    · have hf := haligned.current_fields stage live.2
      obtain ⟨_, e, he, hstage, _⟩ := by simpa only [referenceCurrentLedgerFits, hphase] using hf
      exact Or.inr ⟨e, he, hstage⟩

/-- Every stage strictly before the actual reference cursor is physically
correct. The claim includes failed/abandoned prefixes and all quota variants. -/
theorem prefix_reference_pastCorrect {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget limit)
      seed truth tapes n s) :
    ∀ stage : I.Stage, stage.val < s.cursor →
      s.ledger.written stage = some (s.ledger.truth stage) ∨
        ∃ e ∈ s.ledger.executions, e.handle.stage = stage := by
  induction hp with
  | initial => intro stage hstage; exact (Nat.not_lt_zero _ hstage).elim
  | @next n s next earlier step ih =>
    generalize haction : referenceRule input available budget limit seed s.history = action at step
    cases step with
    | review current live port resources => exact ih
    | write current bit live port resources =>
      intro stage hstage
      have hne : stage ≠ current := by
        intro heq
        subst stage
        change current.val < s.cursor at hstage
        have hc := live.2
        omega
      simpa only [record, reportedWriteLedger, hearly, ite_true, writeLedger, Function.update_of_ne hne] using ih stage hstage
    | allocate handle tool active valid compatible unused unallocated window resources => exact ih
    | execute handle tool active valid compatible committed unused uncorrected window resources =>
      intro stage hstage
      rcases ih stage hstage with hcorrect | ⟨e, he, hs⟩
      · exact Or.inl hcorrect
      · exact Or.inr ⟨e, List.mem_append_left _ he, hs⟩
    | advance current live written resources =>
      intro stage hstage
      by_cases hold : stage.val < s.cursor
      · exact ih stage hold
      · have heq : stage = current := by
          apply Fin.ext
          change stage.val < s.cursor + 1 at hstage
          have hc := live.2
          omega
        subst stage
        exact referenceAdvance_correct_or_repaired input C hearly accounting available budget hbudget hsmall
          limit seed truth tapes earlier current (.advance s current live written resources) haction
    | stop active | abandon active => exact ih

private theorem referenceStop_cursor {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget limit)
      seed truth tapes n s) (hactive : s.halted = false)
    (haction : referenceRule input available budget limit seed s.history = .stop) :
    s.cursor = I.stageCount := by
  have hpnext : Prefix input C .uncapped accounting (referenceRule input available budget limit)
      seed truth tapes (n + 1) (stopState s false) := .next hp (haction ▸ .stop s hactive)
  obtain ⟨cache, haligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    hbudget hsmall limit seed truth tapes hp
  obtain ⟨nextCache, hnextAligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget
    hbudget hsmall limit seed truth tapes hpnext
  have hsingle := replay_single_after input available budget s.history cache nextCache
    .stopped haligned.parsed hnextAligned.parsed
  have hh : cache.halted = false := haligned.halted.trans hactive
  simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hsingle
  obtain ⟨hg, _⟩ := some_if_some _ _ _ hsingle
  exact haligned.cursor.symm.trans hg.1

/-- Any halted infinite-rank reference prefix has completed successfully.
The proof uses actual correct/repair advances and the original deadline
invariants, including the original current-allocation/ execution rights. -/
theorem prefix_reference_halted_success_of_infinite_rank {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (seed : Seed) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (referenceRule input available budget limit)
      seed truth tapes n s) (hhalt : s.halted = true) : s.ledger.success C := by
  classical
  cases hp with
  | initial => cases hhalt
  | @next n s next earlier step =>
    generalize haction : referenceRule input available budget limit seed s.history = action at step
    cases step with
    | review current live port resources => cases hhalt
    | write current bit live port resources => cases hhalt
    | allocate handle tool active valid compatible unused unallocated window resources => cases hhalt
    | execute handle tool active valid compatible committed unused uncorrected window resources => cases hhalt
    | advance stage live written resources => cases hhalt
    | abandon active =>
      exact (referenceRule_ne_abandon_of_infinite_rank input C hearly accounting available budget
        hbudget hsmall htop limit seed truth tapes earlier active haction).elim
    | stop active =>
      have hcursor := referenceStop_cursor input C hearly accounting available budget hbudget hsmall
        limit seed truth tapes earlier active haction
      have hcorrect (stage : I.Stage) : s.ledger.written stage = some (s.ledger.truth stage) ∨
          ∃ e ∈ s.ledger.executions, e.handle.stage = stage :=
        prefix_reference_pastCorrect input C hearly accounting available budget hbudget hsmall limit
          seed truth tapes earlier stage (hcursor ▸ stage.isLt)
      have hwf := prefix_ledgerWellFormed input C .uncapped accounting
        (referenceRule input available budget limit) seed truth tapes earlier
      have hall : allWritten s.ledger := by
        intro stage
        rcases hcorrect stage with hw | ⟨e, he, hs⟩
        · rw [hw]; simp
        · have hg := (hwf.genuine e he).1
          rw [hs] at hg
          rw [hg]; simp
      have hpnext : Prefix input C .uncapped accounting (referenceRule input available budget limit)
          seed truth tapes (n + 1) (stopState s false) := .next earlier (haction ▸ .stop s active)
      apply (prefix_success_iff_physical input C .uncapped accounting
        (referenceRule input available budget limit) seed truth tapes hpnext).mpr
      refine ⟨?_, rfl, ?_⟩
      · change decide (allWritten s.ledger) = true
        exact decide_eq_true hall
      · intro stage
        apply (finalOutput_correct_iff _ stage).mpr
        exact hcorrect stage

/-- Every sample of the original infinite-rank reference succeeds; both ideal
and quota variants are covered. No almost-sure termination assumption is used. -/
theorem referenceRun_success_of_infinite_rank {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (sample : Seed × input.World) :
    runSuccess input C .uncapped accounting (referenceRule input available budget limit) sample := by
  have hhalt := referenceRun_halted_of_infinite_rank input C hearly accounting available budget
    hbudget hsmall htop limit sample
  obtain ⟨n, _, hp⟩ := run_has_prefix input C .uncapped accounting (referenceRule input available budget limit)
    (referenceRule_uncapped_legal input C hearly accounting available budget limit) sample (zeroReviewActionBound I + 1)
  exact ⟨zeroReviewActionBound I + 1, hhalt,
    prefix_reference_halted_success_of_infinite_rank input C hearly accounting available budget hbudget
      hsmall htop limit sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp hhalt⟩

/-- The infinite-rank case of the ideal-risk target is exactly zero, for any
private-seed law. This does not prove the finite-rank risk-budget induction. -/
theorem referenceRisk_zero_of_infinite_rank {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (ν : Measure Seed) :
    risk input C .uncapped accounting (referenceRule input available budget limit) ν = 0 := by
  have hempty : {sample : Seed × input.World |
      ¬ runSuccess input C .uncapped accounting (referenceRule input available budget limit) sample} = ∅ := by
    ext sample
    simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_not]
    exact referenceRun_success_of_infinite_rank input C hearly accounting available budget hbudget hsmall htop limit sample
  rw [risk, hempty, measure_empty]

end PaperProofs.Common.Native
