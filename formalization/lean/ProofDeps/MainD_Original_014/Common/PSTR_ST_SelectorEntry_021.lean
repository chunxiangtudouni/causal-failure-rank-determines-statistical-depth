module

public import Common.PSTR_ST_SelectorSuffixReplay_020

/-! Genuine-entry restart bases for the inherited fixed selector.
The entry cache and risk are reconstructed from actual Prefixes, with no
alignment or suffix-transport hypothesis in the public entry theorem. -/

@[expose] public section

open MeasureTheory

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector

open PaperProofs.Statistics

variable {I : Instance}

theorem first_entry_active 
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Unit) (hlegal : LegalRule input C .uncapped accounting rule)
    (sample : Unit × input.World) (stage : I.Stage) (n : ℕ)
    (hcursor : (run input C .uncapped accounting rule sample n).cursor = stage.val)
    (hbefore : ∀ k < n, (run input C .uncapped accounting rule sample k).cursor ≠ stage.val) :
    (run input C .uncapped accounting rule sample n).halted = false := by
  cases n with
  | zero => rfl
  | succ n =>
    by_cases hh : (run input C .uncapped accounting rule sample n).halted = true
    · rw [run_succ_of_halted input C .uncapped accounting rule sample n hh] at hcursor
      exact (hbefore n (Nat.lt_succ_self n) hcursor).elim
    · have ha : (run input C .uncapped accounting rule sample n).halted = false := Bool.eq_false_iff.mpr hh
      have hp := run_prefix_of_active input C .uncapped accounting rule hlegal sample n ha
      obtain ⟨next, hs⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n _ hp ha
      have he := run_succ_of_step input C .uncapped accounting rule sample n next ha hs
      rw [he] at hcursor ⊢
      generalize haction : rule sample.1 (run input C .uncapped accounting rule sample n).history = action at hs
      cases hs with
      | review | write | allocate | execute | advance => rfl
      | stop | abandon =>
        exact (hbefore n (Nat.lt_succ_self n) hcursor).elim

theorem nextEntry_has_advance 
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I) (chooseRule : PolicyRule I Unit) (hlegal : LegalRule input C .uncapped accounting chooseRule)
    (sample : Unit × input.World) (stage nextStage : I.Stage)
    (hnextStage : nextStage.val = stage.val + 1) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting chooseRule
      nextStage sample = some history) :
    ∃ (n : ℕ) (s next : State I),
      Prefix input C .uncapped accounting chooseRule sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) n s ∧
      run input C .uncapped accounting chooseRule sample n = s ∧
      Step input C .uncapped accounting (worldTapes input sample.2) s (.advance stage) next ∧
      chooseRule sample.1 s.history = .advance stage ∧ next.history = history := by
  obtain ⟨n, hcursor, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C .uncapped accounting chooseRule nextStage sample history).mp hentry
  cases n with
  | zero =>
    change 0 = nextStage.val at hcursor
    have hs := stage.isLt
    omega
  | succ n =>
    have ha : (run input C .uncapped accounting chooseRule sample n).halted = false := by
      apply Bool.eq_false_iff.mpr
      intro hh
      rw [run_succ_of_halted input C .uncapped accounting chooseRule sample n hh] at hcursor
      exact hbefore n (Nat.lt_succ_self n) hcursor
    have hp := run_prefix_of_active input C .uncapped accounting chooseRule hlegal sample n ha
    obtain ⟨next, hs⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) n _ hp ha
    have he := run_succ_of_step input C .uncapped accounting chooseRule sample n next ha hs
    rw [he] at hcursor hhistory
    generalize haction : chooseRule sample.1
      (run input C .uncapped accounting chooseRule sample n).history = action at hs
    cases hs with
    | review | write | allocate | execute | stop | abandon =>
      exact (hbefore n (Nat.lt_succ_self n) hcursor).elim
    | advance current live written resources =>
      have hcurrent : current = stage := by
        apply Fin.ext
        change (run input C .uncapped accounting chooseRule sample n).cursor + 1 = nextStage.val at hcursor
        have hc := live.2
        omega
      subst current
      exact ⟨n, _, _, hp, rfl, .advance _ stage live written resources, haction, hhistory⟩

theorem entry_unborn_queries
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (chooseRule : PolicyRule I Unit) (hlegal : LegalRule input C .uncapped accounting chooseRule)
    (sample : Unit × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting chooseRule stage sample = some history)
    (target : I.Stage) (htarget : stage.val ≤ target.val) :
    historyObservations history target = [] ∧ historyWrite history target = none ∧ historyReport history target = none := by
  by_cases hz : stage.val = 0
  · have he := entryHistory_stageZero input C .uncapped accounting chooseRule stage hz sample
    have hh : history = [] := Option.some.inj (hentry.symm.trans he)
    subst history
    exact ⟨rfl, rfl, rfl⟩
  · let previous : I.Stage := ⟨stage.val - 1, by have hs := stage.isLt; omega⟩
    have hnext : stage.val = previous.val + 1 := by dsimp only [previous]; omega
    obtain ⟨n, s, next, hp, _, hs, haction, hhistory⟩ := nextEntry_has_advance input C accounting chooseRule hlegal
      sample previous stage hnext history hentry
    cases hs with
    | advance current live written resources =>
      have hfuture : s.cursor < target.val := by have hc := live.2; omega
      have hclean := prefix_future_port_clean input C .uncapped accounting chooseRule
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp target hfuture
      have hr := (prefix_cursorInvariant input C .uncapped accounting chooseRule
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp).future_reviews target hfuture
      have hpnext : Prefix input C .uncapped accounting chooseRule sample.1
          (input.truthAt sample.2) (worldTapes input sample.2) (n + 1)
          (record accounting s (.advance previous) [.advanced previous] (advanceLedger s previous) (s.cursor + 1) false) := by
        apply Prefix.next hp
        rw [haction]
        exact Step.advance s previous live written resources
      have hlength := prefix_historyObservations_length_toNat input C .uncapped accounting chooseRule
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext target
      have hwrite := prefix_historyWritten input C .uncapped accounting chooseRule
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext target
      have hreport := prefix_historyReport_early input C hearly .uncapped accounting chooseRule
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext target
      rw [hhistory] at hlength hwrite hreport
      refine ⟨?_, ?_, ?_⟩
      · apply List.eq_nil_of_length_eq_zero
        simpa only [record, advanceLedger, hr, ENat.toNat_zero] using hlength
      · have hw : historyWritten history target = none := by
          simpa only [record, advanceLedger, hclean.1] using hwrite
        cases hraw : historyWrite history target with
        | none => rfl
        | some pair => simp only [historyWritten, hraw, Option.map_some] at hw; cases hw
      · simpa only [record, advanceLedger, hclean.2.1, Option.map_none] using hreport


private theorem some_if_some {α : Type*} (P : Prop) [Decidable P] (value next : α)
    (h : (if P then some value else none) = some next) : P ∧ next = value := by
  by_cases hp : P
  · rw [ite_eq_left hp] at h
    exact ⟨hp, (Option.some.inj h).symm⟩
  · rw [ite_eq_right hp] at h
    cases h

private theorem step_advance_snapshot (choose : Selector I) (input : StatisticalInput I)
    (available : Finset I.Tool) (budget : ℚ) (before after : ReferenceReplayCache I)
    (stage : I.Stage) (hstep : step choose input available budget before (.advanced stage) = some after) :
    after.phase = .testing ∧ after.entryHistory = after.seen := by
  cases hh : before.halted with
  | true => simp only [step, hh, ite_true] at hstep; cases hstep
  | false =>
    simp only [step, hh, Bool.false_eq_true, ite_false] at hstep
    obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
    obtain ⟨_, _, hstep⟩ := Option.bind_eq_some_iff.mp hstep
    obtain ⟨_, he⟩ := some_if_some _ _ _ hstep
    rw [he]
    exact ⟨rfl, rfl⟩

/-- The accepted entry cache is testing and snapshots exactly the genuine
entry history, including stage zero and entries immediately followed by write. -/
theorem entry_replay_snapshot (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting
      (rule selector.choose input available budget none) stage sample = some history) :
    ∃ cache : ReferenceReplayCache I,
      replay selector.choose input available budget history = some cache ∧
      cache.seen = history ∧ cache.entryHistory = history ∧ cache.phase = .testing ∧
      cache.halted = false ∧ historyCursor cache.seen = stage.val ∧ cache.events.length = stage.val := by
  have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget none
  obtain ⟨n, hcursor, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C .uncapped accounting
      (rule selector.choose input available budget none) stage sample history).mp hentry
  have ha := first_entry_active input C accounting _ hlegal sample stage n hcursor hbefore
  have hp := run_prefix_of_active input C .uncapped accounting _ hlegal sample n ha
  obtain ⟨cache, aligned⟩ := prefix_stateAligned (selector := selector) input C hearly accounting
    available budget hbudget hsmall none sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hseen : cache.seen = history := aligned.seen.trans hhistory
  have hparse : replay selector.choose input available budget history = some cache := by
    rw [← hhistory]
    exact aligned.parsed
  have fields : cache.phase = .testing ∧ cache.entryHistory = cache.seen := by
    by_cases hz : stage.val = 0
    · have he := entryHistory_stageZero input C .uncapped accounting
        (rule selector.choose input available budget none) stage hz sample
      have hnil : history = [] := Option.some.inj (hentry.symm.trans he)
      have hi := replay_initial (selector := selector) input available budget hbudget hsmall
      rw [hnil] at hparse
      have heq : cache = referenceReplayInitial I := Option.some.inj (hparse.symm.trans hi)
      subst cache
      exact ⟨rfl, rfl⟩
    · let previous : I.Stage := ⟨stage.val - 1, by have hs := stage.isLt; omega⟩
      have hnext : stage.val = previous.val + 1 := by dsimp only [previous]; omega
      obtain ⟨m, s, next, hpast, _hrun, hstep, haction, hnextHistory⟩ :=
        nextEntry_has_advance input C accounting _ hlegal sample previous stage hnext history hentry
      obtain ⟨old, oldAligned⟩ := prefix_stateAligned (selector := selector) input C hearly accounting
        available budget hbudget hsmall none sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpast
      have hpacket : history = s.history ++ [.advanced previous] := by
        cases hstep
        exact hnextHistory.symm
      have beforeSpec := replay_some_spec selector.choose input available budget s.history old oldAligned.parsed
      have afterSpec := replay_some_spec selector.choose input available budget history cache hparse
      rw [hpacket, List.foldlM_append, beforeSpec.2.1] at afterSpec
      have hsingle : step selector.choose input available budget old (.advanced previous) = some cache := by
        simpa using afterSpec.2.1
      exact step_advance_snapshot selector.choose input available budget old cache previous hsingle
  refine ⟨cache, hparse, hseen, fields.2.trans hseen, fields.1, aligned.halted.trans ha,
    aligned.cursor.trans hcursor, ?_⟩
  simpa only [fields.1, referencePhaseReportCount, Nat.add_zero, hcursor] using aligned.trace_count

def entryRisk (choose : Selector I) (input : StatisticalInput I) (available : Finset I.Tool)
    (budget : ℚ) (history : List (VisibleEvent I)) : Option ℚ := do
  let cache ← replay choose input available budget history
  referenceReplayRisk budget cache

/-- Every restart fact is derived from the actual entry. The restart budget
is exactly twice the original current risk, with the original rank labels. -/
theorem entry_suffixBase (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Unit × input.World)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting
      (rule selector.choose input available budget none) stage sample = some history) :
    ∃ base risk, replay selector.choose input available budget history = some base ∧ base.seen = history ∧
      entryRisk selector.choose input available budget history = some risk ∧
      ReferenceSuffixBase I stage.val budget risk base := by
  obtain ⟨base, hp, hseen, hsnap, hphase, hactive, hcursor, hcount⟩ := entry_replay_snapshot
    input C hearly accounting available selector budget hbudget hsmall sample stage history hentry
  obtain ⟨risk, hrisk⟩ : ∃ risk : ℚ, referenceReplayRisk budget base = some risk := by
    obtain ⟨n, _hc, _hb, hhistory⟩ :=
      (entryHistory_some_iff input C .uncapped accounting
        (rule selector.choose input available budget none) stage sample history).mp hentry
    have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget none
    obtain ⟨_, _, hprefix⟩ := run_has_prefix input C .uncapped accounting _ hlegal sample n
    obtain ⟨cache, aligned⟩ := prefix_stateAligned (selector := selector) input C hearly accounting
      available budget hbudget hsmall none sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hprefix
    have hparse : replay selector.choose input available budget history = some cache := by
      rw [← hhistory]
      exact aligned.parsed
    have heq : cache = base := Option.some.inj (hparse.symm.trans hp)
    subst cache
    exact aligned.testing_risk hphase
  have hvalid : ReferenceBudgetValid risk :=
    (referenceBudgetPath_valid_floor base.events (budget / 2) risk
      (show ReferenceBudgetValid (budget / 2) from ⟨by linarith, by linarith⟩) hrisk).1
  have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget none
  refine ⟨base, risk, hp, hseen, ?_, ?_⟩
  · simp only [entryRisk, hp, Option.bind_eq_bind, Option.bind_some, hrisk]
  · refine ⟨stage.isLt.le, hcursor, hcount, hsnap.trans hseen.symm, hphase, hactive, hrisk, hvalid, ?_, ?_, ?_⟩
    · intro current
      rw [hseen]
      exact (entry_unborn_queries input C hearly accounting _ hlegal sample stage history hentry
        (I.freshStageLift stage.val current) (by change stage.val ≤ stage.val + current.val; omega)).1
    · intro current
      rw [hseen]
      exact (entry_unborn_queries input C hearly accounting _ hlegal sample stage history hentry
        (I.freshStageLift stage.val current) (by change stage.val ≤ stage.val + current.val; omega)).2.1
    · intro current
      rw [hseen]
      exact (entry_unborn_queries input C hearly accounting _ hlegal sample stage history hentry
        (I.freshStageLift stage.val current) (by change stage.val ≤ stage.val + current.val; omega)).2.2

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector
