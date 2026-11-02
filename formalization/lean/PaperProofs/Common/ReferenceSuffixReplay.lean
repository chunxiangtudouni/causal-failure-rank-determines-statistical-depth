module

public import PaperProofs.Common.ReferenceObservationCost

/-!
Visible fresh-suffix reindexing for the actual reference controller.
Only stage labels and public action serials are shifted. No hidden truth,
future tape or complete Native.State is inserted in a private seed. This
module does not yet prove a full continuation run/expense transport.
-/

@[expose] public section

namespace PaperProofs.Common.Native

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

theorem freshStageLift_injective (I : Instance) (first : ℕ) : Function.Injective (I.freshStageLift first) := by
  intro a b h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change first + a.val = first + b.val at hh
  omega

/-- A suffix handle keeps the same tool-independent write identity, with
the old public action-clock offset restored. -/
def referenceSuffixHandleLift (I : Instance) (first clock : ℕ)
    (handle : MismatchHandle (I.freshSuffix first)) : MismatchHandle I :=
  ⟨I.freshStageLift first handle.stage, clock + handle.writeSerial⟩

def referenceSuffixActionLift (I : Instance) (first clock : ℕ) :
    Action (I.freshSuffix first) → Action I
  | .review stage => .review (I.freshStageLift first stage)
  | .write stage bit => .write (I.freshStageLift first stage) bit
  | .allocate handle tool => .allocate (referenceSuffixHandleLift I first clock handle) tool
  | .execute handle tool => .execute (referenceSuffixHandleLift I first clock handle) tool
  | .advance stage => .advance (I.freshStageLift first stage)
  | .stop => .stop
  | .abandon => .abandon

def referenceSuffixEventLift (I : Instance) (first clock : ℕ) :
    VisibleEvent (I.freshSuffix first) → VisibleEvent I
  | .observation stage symbol => .observation (I.freshStageLift first stage) symbol
  | .wrote stage bit serial => .wrote (I.freshStageLift first stage) bit (clock + serial)
  | .report stage truth serial => .report (I.freshStageLift first stage) truth (clock + serial)
  | .committed handle tool => .committed (referenceSuffixHandleLift I first clock handle) tool
  | .executed handle tool => .executed (referenceSuffixHandleLift I first clock handle) tool
  | .advanced stage => .advanced (I.freshStageLift first stage)
  | .stopped => .stopped
  | .abandoned => .abandoned

def referenceSuffixHistoryLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) : List (VisibleEvent I) :=
  history.map (referenceSuffixEventLift I first clock)

theorem referenceSuffixHistoryLift_append (I : Instance) (first clock : ℕ)
    (left right : List (VisibleEvent (I.freshSuffix first))) :
    referenceSuffixHistoryLift I first clock (left ++ right) =
      referenceSuffixHistoryLift I first clock left ++ referenceSuffixHistoryLift I first clock right :=
  List.map_append

theorem eventAction_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (event : VisibleEvent (I.freshSuffix first)) :
    eventAction (referenceSuffixEventLift I first clock event) =
      (eventAction event).map (referenceSuffixActionLift I first clock) := by
  cases event <;> rfl

theorem historyActions_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    historyActions (referenceSuffixHistoryLift I first clock history) =
      (historyActions history).map (referenceSuffixActionLift I first clock) := by
  simp only [historyActions, referenceSuffixHistoryLift, List.filterMap_map, Function.comp_def,
    eventAction_referenceSuffixLift, ← List.map_filterMap]

theorem historyActions_referenceSuffixLift_length (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    (historyActions (referenceSuffixHistoryLift I first clock history)).length = (historyActions history).length := by
  rw [historyActions_referenceSuffixLift, List.length_map]

theorem historyCursor_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    historyCursor (referenceSuffixHistoryLift I first clock history) = historyCursor history := by
  induction history with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp_all only [referenceSuffixHistoryLift, referenceSuffixEventLift, List.map_cons, historyCursor,
      List.filterMap_cons, eventAdvance, List.length_cons]

theorem historyObservations_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) (stage : (I.freshSuffix first).Stage) :
    historyObservations (referenceSuffixHistoryLift I first clock history) (I.freshStageLift first stage) =
      historyObservations history stage := by
  induction history with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp_all only [referenceSuffixHistoryLift, List.map_cons, referenceSuffixEventLift,
      historyObservations, List.filterMap_cons, eventObservation, (freshStageLift_injective I first).eq_iff]

theorem historyWrite_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) (stage : (I.freshSuffix first).Stage) :
    historyWrite (referenceSuffixHistoryLift I first clock history) (I.freshStageLift first stage) =
      (historyWrite history stage).map (fun entry => (entry.1, clock + entry.2)) := by
  have he : ∀ event : VisibleEvent (I.freshSuffix first),
      eventWrite (I.freshStageLift first stage) (referenceSuffixEventLift I first clock event) =
        (eventWrite stage event).map (fun entry => (entry.1, clock + entry.2)) := by
    intro event
    cases event <;> simp only [referenceSuffixEventLift, eventWrite, (freshStageLift_injective I first).eq_iff,
      Option.map_none, Option.map_ite]
  simp only [historyWrite, referenceSuffixHistoryLift, List.filterMap_map, Function.comp_def, he,
    ← List.map_filterMap, List.getLast?_map]

theorem historyReport_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) (stage : (I.freshSuffix first).Stage) :
    historyReport (referenceSuffixHistoryLift I first clock history) (I.freshStageLift first stage) =
      (historyReport history stage).map (fun entry => (entry.1, clock + entry.2)) := by
  have he : ∀ event : VisibleEvent (I.freshSuffix first),
      eventReport (I.freshStageLift first stage) (referenceSuffixEventLift I first clock event) =
        (eventReport stage event).map (fun entry => (entry.1, clock + entry.2)) := by
    intro event
    cases event <;> simp only [referenceSuffixEventLift, eventReport, (freshStageLift_injective I first).eq_iff,
      Option.map_none, Option.map_ite]
  simp only [historyReport, referenceSuffixHistoryLift, List.filterMap_map, Function.comp_def, he,
    ← List.map_filterMap, List.getLast?_map]

theorem historyUsed_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    historyUsed (referenceSuffixHistoryLift I first clock history) = historyUsed history := by
  have he : ∀ event : VisibleEvent (I.freshSuffix first),
      (eventCommitment (referenceSuffixEventLift I first clock event)).map Prod.snd =
        (eventCommitment event).map Prod.snd := by
    intro event
    cases event <;> rfl
  simp only [historyUsed, historyCommitments, referenceSuffixHistoryLift, List.filterMap_map,
    List.map_filterMap, Function.comp_def, he]
  rfl

theorem referenceVisibleHandle_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) (stage : (I.freshSuffix first).Stage) :
    referenceVisibleHandle (referenceSuffixHistoryLift I first clock history) (I.freshStageLift first stage) =
      (referenceVisibleHandle history stage).map (referenceSuffixHandleLift I first clock) := by
  simp only [referenceVisibleHandle, historyWrite_referenceSuffixLift]
  cases historyWrite history stage <;> rfl

theorem freshSuffix_drop_stage (I : Instance) (first : ℕ) (stage : (I.freshSuffix first).Stage) :
    (I.freshSuffix first).compatibility.drop stage.val =
      I.compatibility.drop (I.freshStageLift first stage).val := by
  simp only [Instance.freshSuffix, Instance.freshStageLift, List.drop_drop]

theorem freshSuffix_drop_after_stage (I : Instance) (first : ℕ) (stage : (I.freshSuffix first).Stage) :
    (I.freshSuffix first).compatibility.drop (stage.val + 1) =
      I.compatibility.drop ((I.freshStageLift first stage).val + 1) := by
  simp only [Instance.freshSuffix, Instance.freshStageLift, List.drop_drop, Nat.add_assoc]

/-- The same executable finite picker is used after suffix reindexing,
with the old used tools removed only from the available-set argument. -/
theorem referenceAvailableRepairTool_freshSuffix (I : Instance) (first : ℕ)
    (available oldUsed used : Finset I.Tool) (stage : (I.freshSuffix first).Stage) :
    referenceAvailableRepairTool (I.freshSuffix first) (available \ oldUsed) stage used =
      referenceAvailableRepairTool I available (I.freshStageLift first stage) (oldUsed ∪ used) := by
  unfold referenceAvailableRepairTool referenceRepairTool
  rw [referenceRank_remaining (I.freshSuffix first) (available \ oldUsed) used,
    referenceRank_remaining I available (oldUsed ∪ used), I.freshSuffix_eligible, freshSuffix_drop_after_stage]
  change pickGenericMaxRankTool I.toolCount (I.eligible (I.freshStageLift first stage))
    (I.compatibility.drop ((I.freshStageLift first stage).val + 1)) ((available \ oldUsed) \ used) = _
  have hrem : (available \ oldUsed) \ used = available \ (oldUsed ∪ used) := by ext tool; simp [and_assoc]
  exact congrArg (pickGenericMaxRankTool I.toolCount (I.eligible (I.freshStageLift first stage))
    (I.compatibility.drop ((I.freshStageLift first stage).val + 1))) hrem

theorem referenceAvailableRankCase_freshSuffix (I : Instance) (first : ℕ)
    (available oldUsed used : Finset I.Tool) (stage : (I.freshSuffix first).Stage) :
    referenceAvailableRankCase (I.freshSuffix first) (available \ oldUsed) stage used =
      referenceAvailableRankCase I available (I.freshStageLift first stage) (oldUsed ∪ used) := by
  unfold referenceAvailableRankCase referenceRankCase
  have hcurrent : referenceRankAt (I.freshSuffix first)
      ⟨stage.val, Nat.lt_succ_of_lt stage.isLt⟩ (referenceRankExcluded (I.freshSuffix first) (available \ oldUsed) used) =
      referenceRankAt I ⟨(I.freshStageLift first stage).val, Nat.lt_succ_of_lt (I.freshStageLift first stage).isLt⟩
        (referenceRankExcluded I available (oldUsed ∪ used)) := by
    rw [referenceRankAt_eq, referenceRankAt_eq,
      referenceRank_remaining (I.freshSuffix first) (available \ oldUsed) used,
      referenceRank_remaining I available (oldUsed ∪ used), freshSuffix_drop_stage]
    change errorRank (I.compatibility.drop (I.freshStageLift first stage).val) ((available \ oldUsed) \ used) = _
    have hrem : (available \ oldUsed) \ used = available \ (oldUsed ∪ used) := by ext tool; simp [and_assoc]
    exact congrArg (errorRank (I.compatibility.drop (I.freshStageLift first stage).val)) hrem
  have hbad : referenceBadRank (I.freshSuffix first) stage (referenceRankExcluded (I.freshSuffix first) (available \ oldUsed) used) =
      referenceBadRank I (I.freshStageLift first stage) (referenceRankExcluded I available (oldUsed ∪ used)) := by
    rw [referenceBadRank_eq, referenceBadRank_eq,
      referenceRank_remaining (I.freshSuffix first) (available \ oldUsed) used,
      referenceRank_remaining I available (oldUsed ∪ used),
      I.freshSuffix_eligible, freshSuffix_drop_after_stage]
    change badChildRank (I.eligible (I.freshStageLift first stage))
      (I.compatibility.drop ((I.freshStageLift first stage).val + 1)) ((available \ oldUsed) \ used) = _
    have hrem : (available \ oldUsed) \ used = available \ (oldUsed ∪ used) := by ext tool; simp [and_assoc]
    exact congrArg (badChildRank (I.eligible (I.freshStageLift first stage))
      (I.compatibility.drop ((I.freshStageLift first stage).val + 1))) hrem
  rw [hcurrent, hbad]

theorem referenceBudgetPath_append (initial : ℚ) (before after : List ReferenceBudgetEvent) :
    referenceBudgetPath initial (before ++ after) =
      (referenceBudgetPath initial before).bind (fun risk => referenceBudgetPath risk after) := by
  induction before generalizing initial with
  | nil => rfl
  | cons event rest ih =>
    simp only [List.cons_append, referenceBudgetPath, ih, Option.bind_assoc]

/-- The exact child parser budget is 2r, because the unchanged parser
starts at half its public budget. This is an algebraic replay identity. -/
theorem referenceBudgetPath_restart (budget risk : ℚ) (before after : List ReferenceBudgetEvent)
    (hbefore : referenceBudgetPath (budget / 2) before = some risk) :
    referenceBudgetPath (budget / 2) (before ++ after) = referenceBudgetPath ((2 * risk) / 2) after := by
  rw [referenceBudgetPath_append, hbefore, Option.bind_some]
  congr 1
  ring

def referenceFreshHead (I : Instance) (stage : I.Stage) : (I.freshSuffix stage.val).Stage :=
  ⟨0, by
    simpa only [Instance.freshSuffix, List.length_drop] using (Nat.sub_pos_of_lt stage.isLt)⟩

theorem freshStageLift_referenceFreshHead (I : Instance) (stage : I.Stage) :
    I.freshStageLift stage.val (referenceFreshHead I stage) = stage := by
  apply Fin.ext
  simp only [Instance.freshStageLift, referenceFreshHead, Nat.add_zero]

theorem referenceAvailableKind_fresh_initial (I : Instance) (stage : I.Stage)
    (available oldUsed : Finset I.Tool) :
    referenceAvailableKind (I.freshSuffix stage.val) (available \ oldUsed)
      (referenceReplayInitial (I.freshSuffix stage.val)) =
      referenceAvailableRankCase I available stage oldUsed := by
  have hstage : referenceReplayStage (I.freshSuffix stage.val) (referenceReplayInitial (I.freshSuffix stage.val)) =
      some (referenceFreshHead I stage) := by
    have hpos : 0 < (I.freshSuffix stage.val).stageCount := (referenceFreshHead I stage).isLt
    unfold referenceReplayStage
    split
    · congr 1
    · rename_i hneg
      exact (hneg hpos).elim
  simp only [referenceAvailableKind, hstage, Option.bind_eq_bind, Option.bind_some]
  change referenceAvailableRankCase (I.freshSuffix stage.val) (available \ oldUsed) (referenceFreshHead I stage) ∅ = _
  exact (referenceAvailableRankCase_freshSuffix I stage.val available oldUsed ∅ (referenceFreshHead I stage)).trans
    (by rw [freshStageLift_referenceFreshHead, Finset.union_empty])

/-- The original child constructor with public budget 2r selects precisely
the parent's entry target r. No risk shrinkage or fresh-cost recurrence is used. -/
theorem referenceAvailableEntryTarget_fresh_initial (input : StatisticalInput I) (stage : I.Stage)
    (available oldUsed : Finset I.Tool) (risk : ℚ) (hvalid : ReferenceBudgetValid risk)
    (kind : ReferenceBudgetCase)
    (hkind : referenceAvailableRankCase I available stage oldUsed = some kind) :
    referenceAvailableEntryTarget (input.freshSuffix stage.val) (available \ oldUsed) (2 * risk) [] =
      referenceBudgetTarget kind risk := by
  have hbpos : 0 < 2 * risk := by linarith [hvalid.1]
  have hbsmall : 2 * risk ≤ 1 / 2 := by linarith [hvalid.2]
  have hhalf : (2 * risk) / 2 = risk := by ring
  have hk := referenceAvailableKind_fresh_initial I stage available oldUsed
  rw [hkind] at hk
  simp only [referenceAvailableEntryTarget,
    referenceAvailableReplay_initial (input.freshSuffix stage.val) (available \ oldUsed) (2 * risk) hbpos hbsmall,
    Option.bind_eq_bind, Option.bind_some]
  unfold referenceAvailableCacheTarget
  rw [show ((referenceReplayInitial (I.freshSuffix stage.val)).halted ||
      decide ((referenceReplayInitial (I.freshSuffix stage.val)).phase ≠ .testing)) = false by rfl]
  simp only [Bool.false_eq_true, ite_false, hk, Option.bind_eq_bind, Option.bind_some]
  simp only [referenceReplayRisk, referenceReplayInitial, referenceBudgetPath, hhalf, Option.bind_some]
  change (if 0 < risk ∧ risk ≤ 1 / 4 ∧ 0 ≤ (I.freshSuffix stage.val).stageCount then referenceBudgetTarget kind risk else none) = _
  rw [ite_eq_left ⟨hvalid.1, hvalid.2, Nat.zero_le _⟩]

private theorem first_entry_active {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (sample : Seed × input.World) (stage : I.Stage) (n : ℕ)
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
      | stop | abandon => exact (hbefore n (Nat.lt_succ_self n) hcursor).elim

/-- An actual entry supplies the cache relation; it is not a startup-data
field or an alignment/Markov premise added to the controller. -/
theorem referenceEntry_replay_snapshot {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history) :
    ∃ cache : ReferenceReplayCache I,
      referenceAvailableReplay input available budget history = some cache ∧
      cache.seen = history ∧ cache.entryHistory = history ∧ cache.phase = .testing ∧ cache.halted = false ∧
      historyCursor cache.seen = stage.val ∧ cache.events.length = stage.val := by
  obtain ⟨n, hcursor, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C .uncapped accounting (referenceRule input available budget none) stage sample history).mp hentry
  have hlegal := referenceRule_uncapped_legal (Seed := Seed) input C hearly accounting available budget none
  have ha := first_entry_active input C accounting _ hlegal sample stage n hcursor hbefore
  have hp := run_prefix_of_active input C .uncapped accounting _ hlegal sample n ha
  obtain ⟨cache, entry, haligned, horigin⟩ := referenceEntryBudgetTrace_of_prefix input C hearly accounting available budget
    hbudget hsmall sample hp ha stage hcursor
  have hsnapshot : cache.entryHistory = history := Option.some.inj (horigin.actual_entry.symm.trans hentry)
  have hparse : referenceAvailableReplay input available budget history = some cache := by
    rw [← hhistory]
    exact haligned.parsed
  have hparseEntry : referenceAvailableReplay input available budget history = some entry := hsnapshot ▸ horigin.parsed_entry
  have heq : entry = cache := Option.some.inj (hparseEntry.symm.trans hparse)
  subst entry
  refine ⟨cache, hparse, haligned.seen.trans hhistory, hsnapshot, horigin.entry_testing,
    horigin.entry_active, haligned.cursor.trans hcursor, ?_⟩
  simpa only [horigin.entry_testing, referencePhaseReportCount, Nat.add_zero, hcursor] using haligned.trace_count

/-- Actual-entry target transport to the original fresh-suffix constructor,
with available tools R minus genuinely used tools and exactly public 2r. -/
theorem referenceEntry_target_eq_freshSuffix {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history) :
    ∃ risk : ℚ, referenceAvailableEntryRisk input available budget history = some risk ∧ ReferenceBudgetValid risk ∧
      referenceAvailableEntryTarget input available budget history =
        referenceAvailableEntryTarget (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) [] := by
  obtain ⟨kind, risk, hk, hr, hv, ht⟩ := referenceEntryRisk_kind_target input C hearly accounting available budget hbudget hsmall
    sample stage history hentry
  obtain ⟨cache, hp, hseen, hsnap, hphase, hactive, hcursor, _⟩ := referenceEntry_replay_snapshot input C hearly accounting
    available budget hbudget hsmall sample stage history hentry
  have hstage : referenceReplayStage I cache = some stage := by
    unfold referenceReplayStage
    rw [hcursor]
    rw [dite_eq_left (show stage.val < I.stageCount from stage.isLt)]
  have hkind : referenceAvailableRankCase I available stage (historyUsed history) = some kind := by
    simpa only [referenceAvailableEntryKind, hp, Option.bind_eq_bind, Option.bind_some,
      referenceAvailableKind, hstage, hsnap] using hk
  exact ⟨risk, hr, hv, ht.trans (referenceAvailableEntryTarget_fresh_initial input stage available (historyUsed history) risk hv kind hkind).symm⟩

theorem referenceEntry_observations_nil {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (sample : Seed × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history) :
    historyObservations history stage = [] := by
  by_cases hz : stage.val = 0
  · have he := entryHistory_stageZero input C .uncapped accounting (referenceRule input available budget none) stage hz sample
    have hh : history = [] := Option.some.inj (hentry.symm.trans he)
    rw [hh]
    rfl
  · let previous : I.Stage := ⟨stage.val - 1, by have hs := stage.isLt; omega⟩
    have hnext : stage.val = previous.val + 1 := by dsimp only [previous]; omega
    obtain ⟨n, s, next, hp, _, hs, haction, hhistory⟩ := referenceNextEntry_has_advance input C hearly accounting available budget
      sample previous stage hnext history hentry
    cases hs with
    | advance current live written resources =>
      have hfuture : s.cursor < stage.val := by have hc := live.2; omega
      have hr := (prefix_cursorInvariant input C .uncapped accounting (referenceRule input available budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp).future_reviews stage hfuture
      have hpnext : Prefix input C .uncapped accounting (referenceRule input available budget none) sample.1
          (input.truthAt sample.2) (worldTapes input sample.2) (n + 1)
          (record accounting s (.advance previous) [.advanced previous] (advanceLedger s previous) (s.cursor + 1) false) := by
        apply Prefix.next hp
        rw [haction]
        exact Step.advance s previous live written resources
      have hlength := prefix_historyObservations_length_toNat input C .uncapped accounting (referenceRule input available budget none)
        sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hpnext stage
      rw [hhistory] at hlength
      have hzero : (historyObservations history stage).length = 0 := by
        simpa only [record, advanceLedger, hr, ENat.toNat_zero] using hlength
      exact List.eq_nil_of_length_eq_zero hzero

private def emptyPosteriorData (E : BinaryExperiment) (p : ℚ) : Bool × Bool :=
  let word : E.StoppedWord := ⟨0, fun k => Fin.elim0 k⟩
  (E.rationalWordHits p word, E.rationalWordMAP word)

private def emptyReferenceTestingAction (input : StatisticalInput I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (target : Option ℚ) : Action I :=
  match kind with
  | .infiniteRank => .write stage false
  | .noTool | .finiteBad _ => match target with
    | none => .abandon
    | some p => if (emptyPosteriorData (input.experiment stage) p).1 then
        .write stage (emptyPosteriorData (input.experiment stage) p).2 else .review stage

private theorem historyObservationWord_empty (input : StatisticalInput I) (history : List (VisibleEvent I))
    (stage : I.Stage) (hword : historyObservations history stage = [])
    (hvalid : ∀ symbol ∈ historyObservations history stage, symbol < (input.experiment stage).alphabetSize) :
    historyObservationWord input history stage hvalid = ⟨0, fun k => Fin.elim0 k⟩ := by
  unfold historyObservationWord
  have hz : (historyObservations history stage).length = 0 := by rw [hword]; rfl
  apply Sigma.ext hz
  apply Function.hfunext (congrArg Fin hz)
  intro _ k _
  exact Fin.elim0 k

private theorem referenceTestingAction_empty (input : StatisticalInput I)
    (available : Finset I.Tool) (budget : ℚ) (cache : ReferenceReplayCache I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (target : Option ℚ)
    (hkind : referenceAvailableKind I available cache = some kind)
    (htarget : referenceAvailableCacheTarget I available budget cache = target)
    (hword : historyObservations cache.seen stage = []) :
    referenceTestingAction input available budget none cache stage = emptyReferenceTestingAction input stage kind target := by
  have hv : ∀ symbol ∈ historyObservations cache.seen stage, symbol < (input.experiment stage).alphabetSize := by simp [hword]
  cases kind with
  | infiniteRank => simp only [referenceTestingAction, hkind, emptyReferenceTestingAction]
  | noTool | finiteBad depth =>
    simp only [referenceTestingAction, hkind, htarget, emptyReferenceTestingAction]
    cases target with
    | none => rfl
    | some p =>
      dsimp only
      rw [dite_eq_left hv, historyObservationWord_empty input cache.seen stage hword hv]
      rfl

private theorem emptyReferenceTestingAction_freshSuffix (input : StatisticalInput I) (stage : I.Stage)
    (kind : ReferenceBudgetCase) (target : Option ℚ) (clock : ℕ) :
    referenceSuffixActionLift I stage.val clock
      (emptyReferenceTestingAction (input.freshSuffix stage.val) (referenceFreshHead I stage) kind target) =
        emptyReferenceTestingAction input stage kind target := by
  have he : (input.freshSuffix stage.val).experiment (referenceFreshHead I stage) = input.experiment stage :=
    (input.freshSuffix_experiment stage.val (referenceFreshHead I stage)).trans
      (congrArg input.experiment (freshStageLift_referenceFreshHead I stage))
  cases kind with
  | infiniteRank => simp only [emptyReferenceTestingAction, referenceSuffixActionLift, freshStageLift_referenceFreshHead]
  | noTool | finiteBad depth =>
    cases target with
    | none => rfl
    | some p =>
      simp only [emptyReferenceTestingAction, he]
      split <;> simp only [referenceSuffixActionLift, freshStageLift_referenceFreshHead]

private theorem referenceRule_initial_testing {Seed : Type*} (input : StatisticalInput I)
    (available : Finset I.Tool) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (hz : stage.val = 0) (seed : Seed) :
    referenceRule input available budget none seed [] =
      referenceTestingAction input available budget none (referenceReplayInitial I) stage := by
  have hp := referenceAvailableReplay_initial input available budget hbudget hsmall
  have hstage : referenceReplayStage I (referenceReplayInitial I) = some stage := by
    unfold referenceReplayStage
    split
    · congr 1
      apply Fin.ext
      exact hz.symm
    · rename_i hneg
      have hstagepos : stage.val < I.stageCount := stage.isLt
      have hpos : historyCursor (referenceReplayInitial I).seen < I.stageCount := by simpa only [referenceReplayInitial, historyCursor, List.filterMap_nil, List.length_nil, hz] using hstagepos
      exact (hneg hpos).elim
  have hc : referenceCandidateAction input available budget none [] =
      referenceTestingAction input available budget none (referenceReplayInitial I) stage := by
    have hh : (referenceReplayInitial I).halted = false := rfl
    have hphase : (referenceReplayInitial I).phase = .testing := rfl
    simp only [referenceCandidateAction, hp, hh, Bool.false_eq_true, ite_false, hstage, hphase]
  have ha : historyAllowsAction [] (referenceTestingAction input available budget none (referenceReplayInitial I) stage) := by
    rcases referenceTestingAction_supported input available budget none (referenceReplayInitial I) stage with hreview | ⟨bit, hwrite⟩ | habandon
    · rw [hreview]
      simp [historyAllowsAction, historyCursor, historyWritten, historyWrite, hz]
    · rw [hwrite]
      simp [historyAllowsAction, historyCursor, historyWritten, historyWrite, hz]
    · rw [habandon]
      trivial
  simp only [referenceRule, hc, ite_eq_left ha]

/-- A genuine entry's first returned action is precisely the unchanged
fresh-suffix rule's first action, with the true remaining tools and public
budget 2r. The proof derives both snapshots and nonbinding guards. -/
theorem referenceEntry_firstAction_eq_freshSuffix {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (sample : Seed × input.World)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (referenceRule input available budget none) stage sample = some history) :
    ∃ risk : ℚ, referenceAvailableEntryRisk input available budget history = some risk ∧ ReferenceBudgetValid risk ∧
      referenceRule input available budget none sample.1 history =
        referenceSuffixActionLift I stage.val (historyActions history).length
          (referenceRule (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none sample.1 []) := by
  obtain ⟨risk, hr, hv, ht⟩ := referenceEntry_target_eq_freshSuffix input C hearly accounting available budget hbudget hsmall
    sample stage history hentry
  obtain ⟨cache, hp, hseen, hsnap, hphase, hactive, hcursor, _⟩ := referenceEntry_replay_snapshot input C hearly accounting
    available budget hbudget hsmall sample stage history hentry
  have hstage : referenceReplayStage I cache = some stage := by
    unfold referenceReplayStage
    rw [hcursor, dite_eq_left (show stage.val < I.stageCount from stage.isLt)]
  obtain ⟨kind, hk⟩ := referenceAvailableRankCase_exists I available stage (historyUsed history)
  have hkind : referenceAvailableKind I available cache = some kind := by simp only [referenceAvailableKind, hstage, Option.bind_eq_bind, Option.bind_some, hsnap, hk]
  have hword : historyObservations cache.seen stage = [] := hseen ▸ referenceEntry_observations_nil input C hearly accounting available budget sample stage history hentry
  have hcurrent : referenceAvailableCacheTarget I available budget cache =
      referenceAvailableEntryTarget input available budget history := by simp only [referenceAvailableEntryTarget, hp, Option.bind_eq_bind, Option.bind_some]
  have hfirstKind : referenceAvailableKind (I.freshSuffix stage.val) (available \ historyUsed (I := I) history)
      (referenceReplayInitial (I.freshSuffix stage.val)) = some kind :=
    (referenceAvailableKind_fresh_initial I stage available (historyUsed history)).trans hk
  have hbpos : 0 < 2 * risk := by linarith [hv.1]
  have hbsmall : 2 * risk ≤ 1 / 2 := by linarith [hv.2]
  have hfparse := referenceAvailableReplay_initial (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) hbpos hbsmall
  have hfirstTarget : referenceAvailableCacheTarget (I.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk)
      (referenceReplayInitial (I.freshSuffix stage.val)) = referenceAvailableEntryTarget input available budget history := by
    rw [ht]
    simp only [referenceAvailableEntryTarget, hfparse, Option.bind_eq_bind, Option.bind_some]
  have htest := referenceTestingAction_empty input available budget cache stage kind _ hkind hcurrent hword
  have hftest := referenceTestingAction_empty (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk)
    (referenceReplayInitial (I.freshSuffix stage.val)) (referenceFreshHead I stage) kind _ hfirstKind hfirstTarget rfl
  obtain ⟨n, hrunCursor, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C .uncapped accounting (referenceRule input available budget none) stage sample history).mp hentry
  have hlegal := referenceRule_uncapped_legal (Seed := Seed) input C hearly accounting available budget none
  have ha := first_entry_active input C accounting _ hlegal sample stage n hrunCursor hbefore
  have hprefix := run_prefix_of_active input C .uncapped accounting _ hlegal sample n ha
  have hcandidate := referenceRule_eq_candidate_of_prefix input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hprefix
  rw [hhistory] at hcandidate
  refine ⟨risk, hr, hv, ?_⟩
  rw [hcandidate]
  have hc : referenceCandidateAction input available budget none history = referenceTestingAction input available budget none cache stage := by
    simp only [referenceCandidateAction, hp, hactive, Bool.false_eq_true, ite_false, hstage, hphase]
  rw [hc, htest, referenceRule_initial_testing (input.freshSuffix stage.val) (available \ historyUsed (I := I) history)
    (2 * risk) hbpos hbsmall (referenceFreshHead I stage) rfl sample.1, hftest]
  exact (emptyReferenceTestingAction_freshSuffix input stage kind _ _).symm

end PaperProofs.Common.Native
