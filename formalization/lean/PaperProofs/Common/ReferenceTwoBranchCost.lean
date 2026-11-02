module

public import PaperProofs.Common.ReferenceGlobalCost

/-!
The fixed first-stage children of the unchanged ideal reference.  The
repair picker and error labels below are derived from the existing replay
grammar; they are not additional alignment or Markov premises.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics

variable {I : Instance}

private theorem firstBranch_some_if_some {α : Type*} (P : Prop) [Decidable P] (value next : α)
    (h : (if P then some value else none) = some next) : P ∧ next = value := by
  by_cases hp : P
  · rw [ite_eq_left hp] at h
    exact ⟨hp, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hp] at h
    cases h

private theorem firstBranch_replayCorrect_append (cache : ReferenceReplayCache I)
    (event : VisibleEvent I) (phase : ReferenceReplayPhase I) (stage : I.Stage)
    (hw : eventWrite stage event = none) (hr : eventReport stage event = none) :
    referenceReplayCorrect {cache with seen := cache.seen ++ [event], phase := phase} stage =
      referenceReplayCorrect cache stage := by
  simp [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append, hw, hr]

private theorem firstBranch_replayStage_sameCursor (cache next : ReferenceReplayCache I)
    (hc : historyCursor next.seen = historyCursor cache.seen) :
    referenceReplayStage I next = referenceReplayStage I cache := by
  unfold referenceReplayStage
  rw [hc]

theorem referenceReplayMismatch_not_correct (cache : ReferenceReplayCache I) (stage : I.Stage)
    (handle : MismatchHandle I) (hmismatch : referenceReplayMismatch cache stage handle = true) :
    referenceReplayCorrect cache stage = false := by
  cases hw : historyWrite cache.seen stage with
  | none => simp [referenceReplayMismatch, hw] at hmismatch
  | some written =>
    cases hr : historyReport cache.seen stage with
    | none => simp [referenceReplayMismatch, hw, hr] at hmismatch
    | some reported =>
      have hh : written.1 ≠ reported.1 ∧ handle.stage = stage ∧
          handle.writeSerial = written.2 ∧ reported.2 = written.2 := by
        simpa only [referenceReplayMismatch, hw, hr, decide_eq_true_eq] using hmismatch
      simp [referenceReplayCorrect, hw, hr, hh.1]

/-- Every actual repair phase remembers the original entry maximizer, and
has a genuinely incorrect ordinary reported bit in the replay grammar. -/
def ReferenceRepairPickerFits (available : Finset I.Tool) (cache : ReferenceReplayCache I) : Prop :=
  ∀ (stage : I.Stage) (tool : I.Tool), referenceReplayStage I cache = some stage →
    cache.phase = .allocated tool ∨ cache.phase = .executed tool →
      referenceAvailableRepairTool I available stage (historyUsed cache.entryHistory) = some tool ∧
        referenceReplayCorrect cache stage = false

private theorem referenceRepairPickerFits_step
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hfit : ReferenceRepairPickerFits available cache)
    (hstep : referenceAvailableStep input available budget cache event = some next) :
    ReferenceRepairPickerFits available next := by
  cases hh : cache.halted with
  | true => simp only [referenceAvailableStep, hh, ite_true] at hstep; cases hstep
  | false =>
    cases event with
    | observation stage symbol =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool _ hp
      rcases hp with hp | hp <;> simp only [hg.2.2.1] at hp <;> cases hp
    | wrote stage bit serial =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool _ hp
      rcases hp with hp | hp <;> cases hp
    | report stage truth serial =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool _ hp
      rcases hp with hp | hp <;> cases hp
    | committed handle picked =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨stage, hs, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool hc hp
      have hc' : referenceReplayStage I cache = some current := by
        exact (firstBranch_replayStage_sameCursor cache _ (by
          simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance])).symm.trans hc
      have heq : current = stage := Option.some.inj (hc'.symm.trans hs)
      subst current
      have ht : picked = tool := by
        rcases hp with hp | hp
        · exact ReferenceReplayPhase.allocated.inj hp
        · cases hp
      subst tool
      refine ⟨hg.2.2.2.2.2, ?_⟩
      have hcorrect := referenceReplayMismatch_not_correct cache stage handle hg.2.1
      simpa [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append,
        List.filterMap_cons, eventWrite, eventReport] using hcorrect
    | executed handle picked =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨stage, hs, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool hc hp
      have hc' : referenceReplayStage I cache = some current := by
        exact (firstBranch_replayStage_sameCursor cache _ (by
          simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance])).symm.trans hc
      have ht : picked = tool := by
        rcases hp with hp | hp
        · cases hp
        · exact ReferenceReplayPhase.executed.inj hp
      subst tool
      obtain ⟨hpicker, hcorrect⟩ := hfit current picked hc' (Or.inl hg.1)
      refine ⟨hpicker, ?_⟩
      simpa [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append,
        List.filterMap_cons, eventWrite, eventReport] using hcorrect
    | advanced stage =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool _ hp
      rcases hp with hp | hp <;> cases hp
    | stopped =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool hc hp
      have hc' : referenceReplayStage I cache = some current := by
        exact (firstBranch_replayStage_sameCursor cache _ (by
          simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance])).symm.trans hc
      obtain ⟨hpicker, hcorrect⟩ := hfit current tool hc' hp
      refine ⟨hpicker, ?_⟩
      simpa [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append,
        List.filterMap_cons, eventWrite, eventReport] using hcorrect
    | abandoned =>
      simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool hc hp
      have hc' : referenceReplayStage I cache = some current := by
        exact (firstBranch_replayStage_sameCursor cache _ (by
          simp [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance])).symm.trans hc
      obtain ⟨hpicker, hcorrect⟩ := hfit current tool hc' hp
      refine ⟨hpicker, ?_⟩
      simpa [referenceReplayCorrect, historyWrite, historyReport, List.filterMap_append,
        List.filterMap_cons, eventWrite, eventReport] using hcorrect

private theorem referenceRepairPickerFits_fold
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (events : List (VisibleEvent I)) (cache next : ReferenceReplayCache I)
    (hfit : ReferenceRepairPickerFits available cache)
    (hfold : events.foldlM (referenceAvailableStep input available budget) cache = some next) :
    ReferenceRepairPickerFits available next := by
  induction events generalizing cache with
  | nil => exact (Option.some.inj hfold) ▸ hfit
  | cons event rest ih =>
    simp only [List.foldlM_cons] at hfold
    obtain ⟨middle, hstep, htail⟩ := Option.bind_eq_some_iff.mp hfold
    exact ih middle (referenceRepairPickerFits_step input available budget cache middle event hfit hstep) htail

theorem referenceAvailableReplay_repair_picker
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : referenceAvailableReplay input available budget history = some cache) :
    ReferenceRepairPickerFits available cache := by
  apply referenceRepairPickerFits_fold input available budget history (referenceReplayInitial I) cache
  · intro stage tool _ hp
    rcases hp with hp | hp <;> cases hp
  · exact (referenceAvailableReplay_some_spec input available budget history cache hparse).2.1

private theorem firstBranch_replay_single_after
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (history : List (VisibleEvent I)) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hparse : referenceAvailableReplay input available budget history = some cache)
    (hnext : referenceAvailableReplay input available budget (history ++ [event]) = some next) :
    referenceAvailableStep input available budget cache event = some next := by
  have hs := referenceAvailableReplay_some_spec input available budget history cache hparse
  have hs' := referenceAvailableReplay_some_spec input available budget (history ++ [event]) next hnext
  rw [List.foldlM_append, hs.2.1] at hs'
  simpa using hs'.2.1

theorem referenceAvailableEntryKind_initial
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (first : I.Stage) (hfirst : first.val = 0) :
    referenceAvailableEntryKind input available budget [] =
      referenceAvailableRankCase I available first ∅ := by
  have hstage : referenceReplayStage I (referenceReplayInitial I) = some first := by
    unfold referenceReplayStage
    have hc : historyCursor (referenceReplayInitial I).seen = first.val := by
      simpa only [referenceReplayInitial, historyCursor, List.filterMap_nil, List.length_nil] using hfirst.symm
    rw [hc]
    simp only [show first.val < I.stageCount from first.isLt, dite_true]
  simp only [referenceAvailableEntryKind, referenceAvailableReplay_initial input available budget hbudget hsmall,
    Option.bind_eq_bind, Option.bind_some, referenceAvailableKind]
  rw [hstage]
  rfl

private theorem firstBranch_early_written_reported {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (stage : I.Stage) (hw : s.ledger.written stage ≠ none) : s.ledger.reportTime stage ≠ none := by
  induction hp with
  | initial => exact (hw rfl).elim
  | @next n s next earlier step ih =>
    generalize ha : rule seed s.history = action at step
    cases step with
    | write current bit live port resources =>
      by_cases heq : stage = current
      · subst current
        simp only [record, reportedWriteLedger, hearly, ite_true, writeLedger, Function.update_self]
        simp
      · have hwold : s.ledger.written stage ≠ none := by
          simpa [record, reportedWriteLedger, hearly, writeLedger, Function.update_of_ne heq] using hw
        simpa [record, reportedWriteLedger, hearly, writeLedger, Function.update_of_ne heq] using ih hwold
    | review | allocate | execute | advance | stop | abandon => exact ih hw

private theorem firstBranch_wrong_of_not_correct {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I} (hp : Prefix input C .uncapped accounting rule seed truth tapes n s)
    (cache : ReferenceReplayCache I) (hseen : cache.seen = s.history) (stage : I.Stage)
    (hw : s.ledger.written stage ≠ none) (hcorrect : referenceReplayCorrect cache stage = false) :
    s.ledger.written stage = some (!s.ledger.truth stage) := by
  obtain ⟨bit, hwrite, hreport, hb⟩ := prefix_written_report_packet input C hearly .uncapped accounting
    rule seed truth tapes hp stage hw (firstBranch_early_written_reported input C hearly accounting rule seed truth tapes hp stage hw)
  have hn : bit ≠ s.ledger.truth stage := by
    intro heq
    simp [referenceReplayCorrect, hseen, hwrite, hreport, heq] at hcorrect
  exact hb.trans (congrArg some (Bool.eq_not_iff.mpr hn))

/-- Every actual second-stage entry has one of the two fixed original
children. Its error label, budget update and selected tool all come from
the actual first native advance, including zero-probability paths. -/
theorem referenceInitialNextEntry_children
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (kind : ReferenceBudgetCase)
    (hkind : referenceAvailableRankCase I available first ∅ = some kind)
    (sample : Unit × input.World) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) nextStage sample = some history) :
    ∃ (error : Bool) (risk : ℚ), ReferenceBudgetValid risk ∧
      referenceAvailableEntryRisk input available budget history = some risk ∧
      some risk = referenceBudgetStep kind error (budget / 2) ∧
      (if error then ∃ tool, referenceAvailableRepairTool I available first ∅ = some tool ∧
          historyUsed history = {tool} else historyUsed history = ∅) ∧
      (error = true → sample ∈ referenceStageWriteError input C accounting available budget first) := by
  obtain ⟨n, s, next, hp, hrun, hs, ha, hhistory⟩ := referenceNextEntry_has_advance input C hearly accounting available budget
    sample first nextStage (by omega) history hentry
  obtain ⟨cache, oldHistory, oldKind, oldRisk, haligned, holdEntry, _, hk, hr, hv, hu⟩ :=
    referenceAdvance_entry_budget input C hearly accounting available budget hbudget hsmall sample hp first nextStage (by omega) hs ha
  have he : oldHistory = [] := Option.some.inj (holdEntry.symm.trans
    (entryHistory_stageZero input C .uncapped accounting _ first hfirst sample))
  subst oldHistory
  have hk0 := referenceAvailableEntryKind_initial input available budget hbudget hsmall first hfirst
  have hkeq : oldKind = kind := Option.some.inj (hk.symm.trans (hk0.trans hkind))
  subst oldKind
  have hreq : oldRisk = budget / 2 := Option.some.inj (hr.symm.trans
    (referenceAvailableEntryRisk_initial input available budget hbudget hsmall))
  subst oldRisk
  have hactive := step_source_active input C .uncapped accounting (worldTapes input sample.2) hs
  have hcursor : s.cursor = first.val := by cases hs with | advance _ live _ _ => exact live.2
  obtain ⟨entryCache, horigin⟩ := prefix_referenceEntryBudgetTrace input C hearly accounting available budget
    hbudget hsmall sample hp cache haligned hactive first hcursor
  have hentryNil : cache.entryHistory = [] := Option.some.inj (horigin.actual_entry.symm.trans
    (entryHistory_stageZero input C .uncapped accounting _ first hfirst sample))
  have hpnext : Prefix input C .uncapped accounting (referenceRule input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) (n + 1) next := .next hp (ha ▸ hs)
  obtain ⟨nextCache, hnextAligned⟩ := prefix_referenceStateAligned input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext
  have hparseNext : referenceAvailableReplay input available budget (s.history ++ [.advanced first]) = some nextCache := by
    cases hs with | advance _ live written resources => exact hnextAligned.parsed
  have hsingle := firstBranch_replay_single_after input available budget s.history cache nextCache (.advanced first)
    haligned.parsed hparseNext
  have hh : cache.halted = false := haligned.halted.trans hactive
  simp only [referenceAvailableStep, hh, Bool.false_eq_true, ite_false] at hsingle
  obtain ⟨current, hc, hsingle⟩ := Option.bind_eq_some_iff.mp hsingle
  obtain ⟨_, _, hsingle⟩ := Option.bind_eq_some_iff.mp hsingle
  obtain ⟨hg, _⟩ := firstBranch_some_if_some _ _ _ hsingle
  have hcur : current = first := hg.1.symm
  subst current
  obtain ⟨_, risk, _, hrisk, hvalid, _⟩ := referenceEntryRisk_kind_target input C hearly accounting available budget
    hbudget hsmall sample nextStage history hentry
  have hupdate : some risk = referenceBudgetStep kind (!(referenceReplayCorrect cache first)) (budget / 2) := by
    rw [hhistory] at hu
    exact hrisk.symm.trans hu
  have hused : historyUsed history = historyUsed cache.seen := by
    cases hs with
    | advance _ live written resources =>
      rw [← hhistory]
      change historyUsed (s.history ++ [.advanced first]) = historyUsed cache.seen
      rw [← haligned.seen]
      simp [historyUsed, historyCommitments, List.filterMap_append, List.filterMap_cons, eventCommitment]
  refine ⟨!(referenceReplayCorrect cache first), risk, hvalid, hrisk, hupdate, ?_, ?_⟩
  · rcases hg.2 with ⟨hphase, hcorrect⟩ | ⟨tool, hphase⟩
    · have hfit : historyUsed cache.entryHistory = historyUsed cache.seen := by
        simpa only [referenceEntryToolsFit, hphase] using haligned.entry_tools
      simp only [hcorrect, Bool.not_true, Bool.false_eq_true, ite_false]
      rw [hused, ← hfit, hentryNil]
      simp [historyUsed, historyCommitments]
    · have hpicker := referenceAvailableReplay_repair_picker input available budget s.history cache haligned.parsed first tool hc (Or.inr hphase)
      have hfit : insert tool (historyUsed cache.entryHistory) = historyUsed cache.seen ∧ tool ∉ historyUsed cache.entryHistory := by
        simpa only [referenceEntryToolsFit, hphase] using haligned.entry_tools
      simp only [hpicker.2, Bool.not_false, ite_true]
      refine ⟨tool, ?_, ?_⟩
      · simpa [hentryNil, historyUsed, historyCommitments] using hpicker.1
      · rw [hused, ← hfit.1, hentryNil]
        simp [historyUsed, historyCommitments]
  · intro herr
    have hcorrect : referenceReplayCorrect cache first = false := by
      cases hc : referenceReplayCorrect cache first <;> simp_all
    have hw : s.ledger.written first ≠ none := by cases hs with | advance _ _ written _ => exact written
    refine ⟨n, ?_⟩
    rw [hrun]
    exact firstBranch_wrong_of_not_correct input C hearly accounting _ sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) hp cache haligned.seen first hw hcorrect

/-- The genuine fresh reference continuation price, still in ENNReal. -/
noncomputable def referenceFreshChildObservationCost (input : StatisticalInput I)
    (stage : I.Stage) (available : Finset I.Tool) (budget : ℚ) : ℝ≥0∞ :=
  expectedObservationBill (input.freshSuffix stage.val)
    (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
    (zeroNormalAccounting (I.freshSuffix stage.val))
    (referenceRule (input.freshSuffix stage.val) available budget none) (Measure.dirac ())

noncomputable def referenceNextEntryCostFunction (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (stage : I.Stage) (sample : Unit × input.World) : ℝ≥0∞ :=
  match entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample with
  | none => 0
  | some history => referenceEntryFreshObservationCost input available budget stage history

theorem measurable_referenceNextEntryCostFunction (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (available : Finset I.Tool)
    (budget : ℚ) (stage : I.Stage) :
    Measurable (referenceNextEntryCostFunction input C accounting available budget stage) := by
  let price : Option (List (VisibleEvent I)) → ℝ≥0∞ := fun entry => match entry with
    | none => 0
    | some history => referenceEntryFreshObservationCost input available budget stage history
  change Measurable (price ∘ entryHistory input C .uncapped accounting (referenceRule input available budget none) stage)
  exact (measurable_of_countable price).comp
    (measurable_entryHistory input C .uncapped accounting (referenceRule input available budget none)
      (measurable_referenceRule input available budget none) stage)

theorem lintegral_referenceNextEntryCostFunction
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    (∫⁻ sample, referenceNextEntryCostFunction input C accounting available budget stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
      ∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
        (referenceRule input available budget none) stage.val sample ∂input.seededWorldLaw (Measure.dirac ()) := by
  rw [referenceRemainingObservationBill_eq_entryFreshCosts input C hcurrent accounting available budget hbudget hsmall stage,
    lintegral_eq_tsum_referenceEntry input C accounting available budget stage _
      (measurable_referenceNextEntryCostFunction input C accounting available budget stage)
      (fun sample hs => by simp only [referenceNextEntryCostFunction, hs])]
  apply tsum_congr
  intro history
  have heq := setLIntegral_congr_fun (μ := input.seededWorldLaw (Measure.dirac ()))
    (measurableSet_referenceEntryEvent input C accounting available budget stage history)
    (fun sample (hs : sample ∈ referenceEntryEvent input C accounting available budget stage history) =>
      show referenceNextEntryCostFunction input C accounting available budget stage sample =
        referenceEntryFreshObservationCost input available budget stage history by
          simp only [referenceNextEntryCostFunction, show entryHistory input C .uncapped accounting
            (referenceRule input available budget none) stage sample = some history from hs])
  rw [heq, setLIntegral_const, mul_comm]

/-- Pointwise compression of the genuine next-entry price to the TWO fixed
first-stage children. The bad price is charged only on a real first-stage
ordinary write error. No branch-choice, Markov or run-alignment premise. -/
theorem referenceNextEntryCostFunction_finiteBad_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (depth : ℕ+) (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth))
    (tool : I.Tool) (hpick : referenceAvailableRepairTool I available first ∅ = some tool)
    (sample : Unit × input.World) :
    referenceNextEntryCostFunction input C accounting available budget nextStage sample ≤
      referenceFreshChildObservationCost input nextStage available (budget / 2) +
        (referenceStageWriteError input C accounting available budget first).indicator
          (fun _ => referenceFreshChildObservationCost input nextStage (available.erase tool)
            (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val))) sample := by
  cases hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) nextStage sample with
  | none => simp only [referenceNextEntryCostFunction, hentry]; exact bot_le
  | some history =>
    obtain ⟨error, risk, _, hrisk, hstep, hused, herr⟩ := referenceInitialNextEntry_children input C hearly accounting
      available budget hbudget hsmall first nextStage hfirst hnext (.finiteBad depth) hkind sample history hentry
    cases error with
    | false =>
      have hr : risk = budget / 2 / 2 := Option.some.inj hstep
      have hu : historyUsed history = ∅ := hused
      have htwo : 2 * (budget / 2 / 2) = budget / 2 := by ring
      simp only [referenceNextEntryCostFunction, hentry, referenceEntryFreshObservationCost, hrisk, hu, hr, htwo]
      apply le_add_right
      change referenceFreshChildObservationCost input nextStage (available \ (∅ : Finset I.Tool)) (budget / 2) ≤
        referenceFreshChildObservationCost input nextStage available (budget / 2)
      rw [Finset.sdiff_empty]
    | true =>
      have hr : risk = controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val) :=
        Option.some.inj hstep
      obtain ⟨picked, hselected, hu⟩ := hused
      have ht : picked = tool := Option.some.inj (hselected.symm.trans hpick)
      subst picked
      rw [Set.indicator_of_mem (herr rfl)]
      simp only [referenceNextEntryCostFunction, hentry, referenceEntryFreshObservationCost, hrisk, hu, hr]
      apply le_add_left
      change referenceFreshChildObservationCost input nextStage (available \ ({tool} : Finset I.Tool))
        (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val)) ≤
        referenceFreshChildObservationCost input nextStage (available.erase tool)
          (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val))
      rw [Finset.sdiff_singleton_eq_erase]

theorem referenceAvailableEntryTarget_initial
    (input : StatisticalInput I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (first : I.Stage) (hfirst : first.val = 0)
    (kind : ReferenceBudgetCase) (hkind : referenceAvailableRankCase I available first ∅ = some kind) :
    referenceAvailableEntryTarget input available budget [] = referenceBudgetTarget kind (budget / 2) := by
  have hs : referenceReplayStage I (referenceReplayInitial I) = some first := by
    unfold referenceReplayStage
    have hc : historyCursor (referenceReplayInitial I).seen = first.val := by
      simpa only [referenceReplayInitial, historyCursor, List.filterMap_nil, List.length_nil] using hfirst.symm
    rw [hc]
    simp only [show first.val < I.stageCount from first.isLt, dite_true]
  have hk : referenceAvailableKind I available (referenceReplayInitial I) = some kind := by
    unfold referenceAvailableKind
    rw [hs]
    simpa only [Option.bind_eq_bind, Option.bind_some, referenceReplayInitial, historyUsed, historyCommitments,
      List.filterMap_nil, List.map_nil, List.toFinset_nil] using hkind
  have hr : referenceReplayRisk budget (referenceReplayInitial I) = some (budget / 2) := rfl
  have hh : ((referenceReplayInitial I).halted || decide ((referenceReplayInitial I).phase ≠ .testing)) = false := rfl
  have hb : 0 < budget / 2 ∧ budget / 2 ≤ 1 / 4 ∧ (referenceReplayInitial I).events.length ≤ I.stageCount :=
    ⟨by linarith, by linarith, Nat.zero_le _⟩
  rw [referenceAvailableEntryTarget, referenceAvailableReplay_initial input available budget hbudget hsmall]
  change referenceAvailableCacheTarget I available budget (referenceReplayInitial I) = _
  simp only [referenceAvailableCacheTarget, hh, Bool.false_eq_true, ite_false, hk, hr,
    Option.bind_eq_bind, Option.bind_some, hb, and_self, ite_true]

/-- A genuine finite-bad one-stage recurrence: the maximum-rank error child
has exactly its original bad budget, and its cost carries the original local
SPRT probability factor. All costs and all failed-path corrections remain. -/
theorem referenceExpectedObservationBill_finiteBad_le
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (depth : ℕ+) (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth))
    (tool : I.Tool) (hpick : referenceAvailableRepairTool I available first ∅ = some tool) :
    expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
      referenceEntryLocalObservationPrice input available budget first [] +
        (referenceFreshChildObservationCost input nextStage available (budget / 2) +
          ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) *
            referenceFreshChildObservationCost input nextStage (available.erase tool)
              (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val))) := by
  let μ := input.seededWorldLaw (Measure.dirac ())
  let E := referenceStageWriteError input C accounting available budget first
  let good := referenceFreshChildObservationCost input nextStage available (budget / 2)
  let bad := referenceFreshChildObservationCost input nextStage (available.erase tool)
    (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val))
  have hE : MeasurableSet E := measurableSet_referenceStageWriteError input C accounting available budget first
  have ht : referenceAvailableEntryTarget input available budget [] =
      some (controllerTarget (budget / 2) depth.val) :=
    referenceAvailableEntryTarget_initial input available budget hbudget hsmall first hfirst (.finiteBad depth) hkind
  have hentry : referenceEntryEvent input C accounting available budget first [] = Set.univ := by
    apply Set.eq_univ_of_forall
    intro sample
    exact entryHistory_stageZero input C .uncapped accounting _ first hfirst sample
  have he : μ E ≤ ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) := by
    have hb := referenceStageWriteError_on_entry_le input C hcurrent.1 accounting available budget
      hbudget hsmall first [] _ ht
    change μ (E ∩ referenceEntryEvent input C accounting available budget first []) ≤
      ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) * μ (referenceEntryEvent input C accounting available budget first []) at hb
    simpa only [hentry, Set.inter_univ, measure_univ, mul_one] using hb
  have hfuture : (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
      (referenceRule input available budget none) nextStage.val sample ∂μ) ≤
        good + ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) * bad := by
    rw [← lintegral_referenceNextEntryCostFunction input C hcurrent accounting available budget hbudget hsmall nextStage]
    calc
      _ ≤ ∫⁻ sample, good + E.indicator (fun _ => bad) sample ∂μ :=
        lintegral_mono (referenceNextEntryCostFunction_finiteBad_le input C hcurrent.1 accounting available budget
          hbudget hsmall first nextStage hfirst hnext depth hkind tool hpick)
      _ = good + bad * μ E := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator_const hE]
      _ ≤ _ := add_le_add le_rfl (by simpa only [mul_comm] using mul_le_mul' (le_refl bad) he)
  calc
    _ ≤ referenceEntryLocalObservationPrice input available budget first [] +
        (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
          (referenceRule input available budget none) nextStage.val sample ∂μ) := by
      rw [referenceRemainingObservationBill_eq_entryFreshCosts input C hcurrent accounting available budget hbudget hsmall nextStage]
      exact referenceExpectedObservationBill_le_initial_add_entryFreshCosts input C hcurrent accounting available budget
        hbudget hsmall first nextStage hfirst hnext
    _ ≤ _ := add_le_add le_rfl hfuture

/-- A finite positive bad rank really has a selected tool. This lookup is
the actual executable reference callback, not an extra strategy premise. -/
theorem referenceAvailableRepairTool_exists_finiteBad
    (available : Finset I.Tool) (first : I.Stage) (depth : ℕ+)
    (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth)) :
    ∃ tool, referenceAvailableRepairTool I available first ∅ = some tool := by
  cases hpick : referenceAvailableRepairTool I available first ∅ with
  | some tool => exact ⟨tool, rfl⟩
  | none =>
    have hp : referenceRepairTool I first (referenceRankExcluded I available ∅) = none := hpick
    have hz : referenceBadRank I first (referenceRankExcluded I available ∅) = 0 := by
      simp only [referenceBadRank, hp]
    have hc := referenceCaseOfRanks_finite_spec _ _ depth hkind
    rw [hz] at hc
    have hn : depth.val = 0 := by exact_mod_cast hc.2.symm
    exact (depth.ne_zero hn).elim

/-- The recurrence is available for EVERY actual finite-bad entry, and the
tool attains the original maximum bad-child rank. -/
theorem referenceExpectedObservationBill_finiteBad_maximizer
    (input : StatisticalInput I) (C : Contract I) (hcurrent : C.IsCurrentAllocation)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (depth : ℕ+) (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth)) :
    ∃ tool, referenceAvailableRepairTool I available first ∅ = some tool ∧
      tool ∈ I.eligible first ∩ available ∧
      PaperProofs.Structure.errorRank (I.compatibility.drop (first.val + 1)) (available.erase tool) =
        PaperProofs.Structure.badChildRank (I.eligible first) (I.compatibility.drop (first.val + 1)) available ∧
      expectedObservationBill input C .uncapped accounting (referenceRule input available budget none) (Measure.dirac ()) ≤
        referenceEntryLocalObservationPrice input available budget first [] +
          (referenceFreshChildObservationCost input nextStage available (budget / 2) +
            ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) *
              referenceFreshChildObservationCost input nextStage (available.erase tool)
                (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val))) := by
  obtain ⟨tool, hpick⟩ := referenceAvailableRepairTool_exists_finiteBad available first depth hkind
  have hs := referenceAvailableRepairTool_spec I available first ∅ tool hpick
  simp only [Finset.sdiff_empty] at hs
  exact ⟨tool, hpick, hs.1, hs.2, referenceExpectedObservationBill_finiteBad_le input C hcurrent accounting
    available budget hbudget hsmall first nextStage hfirst hnext depth hkind tool hpick⟩

end PaperProofs.Common.Native
