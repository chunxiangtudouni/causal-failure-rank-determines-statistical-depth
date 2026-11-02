module

public import PaperProofs.Common.PSTR_ST_SelectorAlignment_019
public import PaperProofs.Common.ReferenceCostAsymptotics

/-! Infinite-rank variable-fee base for every fixed certified selector.
No paid observations occur; every correction is still charged. This is an
auxiliary fee-induction base, not a new runtime oracle or success premise. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Infinite

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

private theorem infiniteReplay_step (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available)
    (budget : ℚ) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hinv : InfiniteReplayInvariant available cache)
    (hstep : step selector.choose input available budget cache event = some next) :
    InfiniteReplayInvariant available next := by
  cases hh : cache.halted with
  | true => simp only [step, hh, ite_true] at hstep; cases hstep
  | false =>
    cases event with
    | observation stage symbol =>
      simp only [step, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨current, hstage, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, _⟩ := some_if_some _ _ _ hstep
      have hk := availableKind_top available cache current hstage hinv.rank
      cases hr : referenceReplayRisk budget cache <;>
        simp [referenceAvailableCacheTarget, hh, hg.2.2.1, hk, hr, referenceBudgetTarget] at hg
    | wrote stage bit serial =>
      simp only [step, hh, Bool.false_eq_true, ite_false] at hstep
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
      simp only [step, hh, Bool.false_eq_true, ite_false] at hstep
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
      simp only [step, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨stage, hstage, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := some_if_some _ _ _ hstep
      subst next
      have hc := cursor_no_advance cache.seen (.committed handle tool) rfl
      have hu : historyUsed (cache.seen ++ [.committed handle tool]) = insert tool (historyUsed cache.seen) := by
        simp [historyUsed, historyCommitments, List.filterMap_append, eventCommitment, Finset.union_comm]
      have hentry : historyUsed cache.entryHistory = historyUsed cache.seen := by
        simpa only [referenceEntryToolsFit, hg.1] using hinv.entry_tools
      have hpick := selector.spec.some stage (historyUsed cache.entryHistory) tool hg.2.2.2.2.2
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
      simp only [step, hh, Bool.false_eq_true, ite_false] at hstep
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
      simp only [step, hh, Bool.false_eq_true, ite_false] at hstep
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
      simp only [step, hh, Bool.false_eq_true, ite_false] at hstep
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
      simp only [step, hh, Bool.false_eq_true, ite_false] at hstep
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

private theorem infiniteReplay_fold (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available)
    (budget : ℚ) (events : List (VisibleEvent I)) (cache next : ReferenceReplayCache I)
    (hinv : InfiniteReplayInvariant available cache)
    (hfold : events.foldlM (step selector.choose input available budget) cache = some next) :
    InfiniteReplayInvariant available next := by
  induction events generalizing cache with
  | nil =>
    have heq : cache = next := Option.some.inj hfold
    exact heq ▸ hinv
  | cons event rest ih =>
    simp only [List.foldlM_cons] at hfold
    obtain ⟨middle, hstep, htail⟩ := Option.bind_eq_some_iff.mp hfold
    exact ih middle (infiniteReplay_step input available selector budget cache middle event hinv hstep) htail

private theorem infiniteReplay_of_parse (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available)
    (budget : ℚ) (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (htop : errorRank I.compatibility available = ⊤)
    (hparse : replay selector.choose input available budget history = some cache) :
    InfiniteReplayInvariant available cache :=
  infiniteReplay_fold input available selector budget history (referenceReplayInitial I) cache
    (infiniteReplay_initial available htop)
    (replay_some_spec selector.choose input available budget history cache hparse).2.1

/-- The original entry rank stays infinite in every accepted phase, before
and after any correction. The selected corrected tail is also infinite. -/
theorem selectorReplay_rank_top_of_infinite_rank
    (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (htop : errorRank I.compatibility available = ⊤)
    (hparse : replay selector.choose input available budget history = some cache) :
    errorRank (I.compatibility.drop (historyCursor cache.seen))
        (available \ historyUsed cache.entryHistory) = ⊤ ∧
      ∀ tool, cache.phase = .allocated tool ∨ cache.phase = .executed tool →
        errorRank (I.compatibility.drop (historyCursor cache.seen + 1))
          (available \ historyUsed cache.seen) = ⊤ := by
  have hinv := infiniteReplay_of_parse input available selector budget history cache htop hparse
  exact ⟨hinv.rank, hinv.repaired⟩

/-- Every history accepted by the actual reference replay has no observations
when the original initial-availability rank is infinite. No report-kind list
or actual-run success premise is supplied. -/
theorem selectorReplay_observations_nil_of_infinite_rank
    (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (htop : errorRank I.compatibility available = ⊤)
    (hparse : replay selector.choose input available budget history = some cache) :
    ∀ stage : I.Stage, historyObservations history stage = [] := by
  have hs := replay_some_spec selector.choose input available budget history cache hparse
  have hinv := infiniteReplay_of_parse input available selector budget history cache htop hparse
  rw [← hs.2.2.2.2.2]
  exact hinv.no_observations

/-- All actual finite prefixes, for any seed type, any original observation
limit, and every truth/tape path, spend zero review calls in infinite rank. -/
theorem prefix_selector_reviews_zero_of_infinite_rank 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (seed : Unit) (truth : I.Stage → Bool)
    (tapes : ReviewTapes input) {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting (MaxSelector.rule selector.choose input available budget limit)
      seed truth tapes n s) :
    ∀ stage : I.Stage, s.ledger.reviews stage = 0 := by
  obtain ⟨cache, haligned⟩ := prefix_stateAligned (selector := selector) input C hearly accounting available budget
    hbudget hsmall limit seed truth tapes hp
  have hobs := selectorReplay_observations_nil_of_infinite_rank input available selector budget
    s.history cache htop haligned.parsed
  intro stage
  rw [← prefix_historyObservations_length input C .uncapped accounting
    (MaxSelector.rule selector.choose input available budget limit) seed truth tapes hp stage, hobs stage]
  rfl

theorem selectorExpectedObservationBill_infiniteRank 
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤)
    (limit : ReferenceObservationLimit I) (ν : Measure Unit) :
    expectedObservationBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget limit) ν = 0 := by
  have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget limit
  have hzero (stage : I.Stage) (sample : Unit × input.World) :
      runStageObservationBill input C .uncapped accounting
        (MaxSelector.rule selector.choose input available budget limit) stage sample = 0 := by
    unfold runStageObservationBill
    apply le_antisymm (iSup_le fun n => ?_) bot_le
    obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget limit) hlegal sample n
    have hz := prefix_selector_reviews_zero_of_infinite_rank input C hearly accounting
      available selector budget hbudget hsmall htop limit sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) hp stage
    simp [hz]
  rw [expectedObservationBill_eq_sum_stage input C .uncapped accounting _ hlegal
    (policy selector.choose input C hearly accounting available budget limit).measurable_rule]
  simp only [hzero, lintegral_zero, Finset.sum_const_zero]

theorem selectorExpectedBill_infiniteRank_le_corrections
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (htop : errorRank I.compatibility available = ⊤) :
    expectedBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
      (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  have hbill := expectedBill_le_observation_add input C .uncapped accounting
    (policy selector.choose input C hearly accounting available budget none) (Measure.dirac ())
  change expectedBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
    expectedObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) + _ at hbill
  rw [selectorExpectedObservationBill_infiniteRank input C hearly accounting available selector budget
    hbudget hsmall htop none (Measure.dirac ()), zero_add] at hbill
  exact hbill


end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Infinite
