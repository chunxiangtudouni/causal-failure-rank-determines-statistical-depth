module

public import Common.PSTR_ST_SelectorEntryTrace_024
public import PaperProofs.Common.ReferenceTwoBranchCost

/-! The actual first-stage alternatives for a fixed certified selector.
The selected bad tool is fixed before budget/contracts; an absent bad tool
does not create a fictitious continuation. Every real error branch remains. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Branch

open PaperProofs.Statistics

variable {I : Instance}

def selectorStageWriteError (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available)
    (budget : ℚ) (stage : I.Stage) : Set (Unit × input.World) :=
  {sample | ∃ n,
    let s := run input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) sample n
    s.ledger.written stage = some (!s.ledger.truth stage)}

theorem traceEntryKind_initial (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first : I.Stage) (hfirst : first.val = 0) :
    Trace.traceEntryKind input available selector budget [] = referenceAvailableRankCase I available first ∅ := by
  have hsame : Trace.traceEntryKind input available selector budget [] =
      referenceAvailableEntryKind input available budget [] := by
    simp only [Trace.traceEntryKind, referenceAvailableEntryKind,
      replay_initial (selector := selector) input available budget hbudget hsmall,
      referenceAvailableReplay_initial input available budget hbudget hsmall]
  exact hsame.trans (referenceAvailableEntryKind_initial input available budget hbudget hsmall first hfirst)

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

def SelectorRepairPickerFits (choose : Selector I) (cache : ReferenceReplayCache I) : Prop :=
  ∀ (stage : I.Stage) (tool : I.Tool), referenceReplayStage I cache = some stage →
    cache.phase = .allocated tool ∨ cache.phase = .executed tool →
      choose stage (historyUsed cache.entryHistory) = some tool ∧
        referenceReplayCorrect cache stage = false

private theorem selectorRepairPickerFits_step
    (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hfit : SelectorRepairPickerFits selector.choose cache)
    (hstep : MaxSelector.step selector.choose input available budget cache event = some next) :
    SelectorRepairPickerFits selector.choose next := by
  cases hh : cache.halted with
  | true => simp only [MaxSelector.step, hh, ite_true] at hstep; cases hstep
  | false =>
    cases event with
    | observation stage symbol =>
      simp only [MaxSelector.step, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨hg, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool _ hp
      rcases hp with hp | hp <;> simp only [hg.2.2.1] at hp <;> cases hp
    | wrote stage bit serial =>
      simp only [MaxSelector.step, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool _ hp
      rcases hp with hp | hp <;> cases hp
    | report stage truth serial =>
      simp only [MaxSelector.step, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool _ hp
      rcases hp with hp | hp <;> cases hp
    | committed handle picked =>
      simp only [MaxSelector.step, hh, Bool.false_eq_true, ite_false] at hstep
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
      simp only [MaxSelector.step, hh, Bool.false_eq_true, ite_false] at hstep
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
      simp only [MaxSelector.step, hh, Bool.false_eq_true, ite_false] at hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
      obtain ⟨_, he⟩ := firstBranch_some_if_some _ _ _ hstep
      subst next
      intro current tool _ hp
      rcases hp with hp | hp <;> cases hp
    | stopped =>
      simp only [MaxSelector.step, hh, Bool.false_eq_true, ite_false] at hstep
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
      simp only [MaxSelector.step, hh, Bool.false_eq_true, ite_false] at hstep
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

private theorem selectorRepairPickerFits_fold
    (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (events : List (VisibleEvent I)) (cache next : ReferenceReplayCache I)
    (hfit : SelectorRepairPickerFits selector.choose cache)
    (hfold : events.foldlM (MaxSelector.step selector.choose input available budget) cache = some next) :
    SelectorRepairPickerFits selector.choose next := by
  induction events generalizing cache with
  | nil => exact (Option.some.inj hfold) ▸ hfit
  | cons event rest ih =>
    simp only [List.foldlM_cons] at hfold
    obtain ⟨middle, hstep, htail⟩ := Option.bind_eq_some_iff.mp hfold
    exact ih middle (selectorRepairPickerFits_step input available selector budget cache middle event hfit hstep) htail

theorem selectorReplay_repair_picker
    (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (history : List (VisibleEvent I)) (cache : ReferenceReplayCache I)
    (hparse : replay selector.choose input available budget history = some cache) :
    SelectorRepairPickerFits selector.choose cache := by
  apply selectorRepairPickerFits_fold input available selector budget history (referenceReplayInitial I) cache
  · intro stage tool _ hp
    rcases hp with hp | hp <;> cases hp
  · exact (replay_some_spec selector.choose input available budget history cache hparse).2.1

private theorem firstBranch_replay_single_after
    (input : StatisticalInput I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (history : List (VisibleEvent I)) (cache next : ReferenceReplayCache I) (event : VisibleEvent I)
    (hparse : replay selector.choose input available budget history = some cache)
    (hnext : replay selector.choose input available budget (history ++ [event]) = some next) :
    MaxSelector.step selector.choose input available budget cache event = some next := by
  have hs := replay_some_spec selector.choose input available budget history cache hparse
  have hs' := replay_some_spec selector.choose input available budget (history ++ [event]) next hnext
  rw [List.foldlM_append, hs.2.1] at hs'
  simpa using hs'.2.1

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
theorem selectorInitialNextEntry_children
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (kind : ReferenceBudgetCase)
    (hkind : referenceAvailableRankCase I available first ∅ = some kind)
    (sample : Unit × input.World) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) nextStage sample = some history) :
    ∃ (error : Bool) (risk : ℚ), ReferenceBudgetValid risk ∧
      Trace.traceEntryRisk input available selector budget history = some risk ∧
      some risk = referenceBudgetStep kind error (budget / 2) ∧
      (if error then ∃ tool, selector.choose first ∅ = some tool ∧
          historyUsed history = {tool} else historyUsed history = ∅) ∧
      (error = true → sample ∈ selectorStageWriteError input C accounting available selector budget first) := by
  obtain ⟨n, s, next, hp, hrun, hs, ha, hhistory⟩ := nextEntry_has_advance input C accounting _ (rule_uncapped_legal selector.choose input C hearly accounting available budget none)
    sample first nextStage (by omega) history hentry
  obtain ⟨cache, oldHistory, oldKind, oldRisk, haligned, holdEntry, _, hk, hr, hv, hu⟩ :=
    Trace.selectorAdvance_entry_budget input C hearly accounting available selector budget hbudget hsmall sample hp first nextStage (by omega) hs ha
  have he : oldHistory = [] := Option.some.inj (holdEntry.symm.trans
    (entryHistory_stageZero input C .uncapped accounting _ first hfirst sample))
  subst oldHistory
  have hk0 := traceEntryKind_initial input available selector budget hbudget hsmall first hfirst
  have hkeq : oldKind = kind := Option.some.inj (hk.symm.trans (hk0.trans hkind))
  subst oldKind
  have hreq : oldRisk = budget / 2 := Option.some.inj (hr.symm.trans
    (Trace.traceEntryRisk_initial input available selector budget hbudget hsmall))
  subst oldRisk
  have hactive := step_source_active input C .uncapped accounting (worldTapes input sample.2) hs
  have hcursor : s.cursor = first.val := by cases hs with | advance _ live _ _ => exact live.2
  obtain ⟨entryCache, horigin⟩ := Trace.prefix_selectorEntryBudgetTrace input C hearly accounting available selector budget
    hbudget hsmall sample hp cache haligned hactive first hcursor
  have hentryNil : cache.entryHistory = [] := Option.some.inj (horigin.actual_entry.symm.trans
    (entryHistory_stageZero input C .uncapped accounting _ first hfirst sample))
  have hpnext : Prefix input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample.1
      (input.truthAt sample.2) (worldTapes input sample.2) (n + 1) next := .next hp (ha ▸ hs)
  obtain ⟨nextCache, hnextAligned⟩ := prefix_stateAligned (selector := selector) input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext
  have hparseNext : replay selector.choose input available budget (s.history ++ [.advanced first]) = some nextCache := by
    cases hs with | advance _ live written resources => exact hnextAligned.parsed
  have hsingle := firstBranch_replay_single_after input available selector budget s.history cache nextCache (.advanced first)
    haligned.parsed hparseNext
  have hh : cache.halted = false := haligned.halted.trans hactive
  simp only [MaxSelector.step, hh, Bool.false_eq_true, ite_false] at hsingle
  obtain ⟨current, hc, hsingle⟩ := Option.bind_eq_some_iff.mp hsingle
  obtain ⟨_, _, hsingle⟩ := Option.bind_eq_some_iff.mp hsingle
  obtain ⟨hg, _⟩ := firstBranch_some_if_some _ _ _ hsingle
  have hcur : current = first := hg.1.symm
  subst current
  obtain ⟨_, risk, _, hrisk, hvalid, _⟩ := Trace.traceEntryRisk_kind_target input C hearly accounting available selector budget
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
    · have hpicker := selectorReplay_repair_picker input available selector budget s.history cache haligned.parsed first tool hc (Or.inr hphase)
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


end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Branch
