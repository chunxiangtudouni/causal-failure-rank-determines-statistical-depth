module

public import PaperProofs.Common.NativeBellmanUpper
public import PaperProofs.Common.NativeBellmanLower

/-!
Public-history permission transport for an arbitrary available-tool suffix
policy. Old commitments and executions stay occupied; only stage labels
and visible write serials are shifted. No policy performance is assumed.
-/

@[expose] public section

namespace PaperProofs.Common.Native

namespace GuardLift

variable {I : Instance}

theorem historyCommitments_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    historyCommitments (referenceSuffixHistoryLift I first clock history) =
      (historyCommitments history).map
        (fun pair => (referenceSuffixHandleLift I first clock pair.1, pair.2)) := by
  have he (event : VisibleEvent (I.freshSuffix first)) :
      eventCommitment (referenceSuffixEventLift I first clock event) =
        (eventCommitment event).map
          (fun pair => (referenceSuffixHandleLift I first clock pair.1, pair.2)) := by
    cases event <;> rfl
  simp only [historyCommitments, referenceSuffixHistoryLift, List.filterMap_map,
    Function.comp_def, he, List.map_filterMap]
  rfl

theorem historyExecutions_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    historyExecutions (referenceSuffixHistoryLift I first clock history) =
      (historyExecutions history).map
        (fun pair => (referenceSuffixHandleLift I first clock pair.1, pair.2)) := by
  have he (event : VisibleEvent (I.freshSuffix first)) :
      eventExecution (referenceSuffixEventLift I first clock event) =
        (eventExecution event).map
          (fun pair => (referenceSuffixHandleLift I first clock pair.1, pair.2)) := by
    cases event <;> rfl
  simp only [historyExecutions, referenceSuffixHistoryLift, List.filterMap_map,
    Function.comp_def, he, List.map_filterMap]
  rfl

theorem historyCommitments_referenceSuffixJoin (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first))) :
    historyCommitments (referenceSuffixHistoryJoin I first before after) =
      historyCommitments before ++ (historyCommitments after).map
        (fun pair => ((referenceSuffixHandleLift I first (historyActions before).length pair.1, pair.2) :
          MismatchHandle I × I.Tool)) := by
  rw [referenceSuffixHistoryJoin]
  change (before ++ referenceSuffixHistoryLift I first _ after).filterMap eventCommitment = _
  rw [List.filterMap_append]
  exact congrArg (historyCommitments before ++ ·)
    (historyCommitments_referenceSuffixLift I first _ after)

theorem historyExecutions_referenceSuffixJoin (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first))) :
    historyExecutions (referenceSuffixHistoryJoin I first before after) =
      historyExecutions before ++ (historyExecutions after).map
        (fun pair => ((referenceSuffixHandleLift I first (historyActions before).length pair.1, pair.2) :
          MismatchHandle I × I.Tool)) := by
  rw [referenceSuffixHistoryJoin]
  change (before ++ referenceSuffixHistoryLift I first _ after).filterMap eventExecution = _
  rw [List.filterMap_append]
  exact congrArg (historyExecutions before ++ ·)
    (historyExecutions_referenceSuffixLift I first _ after)

theorem historyWritten_referenceSuffixJoin (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first)))
    (stage : (I.freshSuffix first).Stage)
    (hbefore : historyWrite before (I.freshStageLift first stage) = none) :
    historyWritten (referenceSuffixHistoryJoin I first before after) (I.freshStageLift first stage) =
      historyWritten after stage := by
  simp only [historyWritten, historyWrite_referenceSuffixJoin I first before after stage hbefore,
    Option.map_map]
  rfl

theorem historyWriteSerial_referenceSuffixJoin (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first)))
    (stage : (I.freshSuffix first).Stage)
    (hbefore : historyWrite before (I.freshStageLift first stage) = none)
    (hwritten : historyWritten after stage ≠ none) :
    historyWriteSerial (referenceSuffixHistoryJoin I first before after) (I.freshStageLift first stage) =
      (historyActions before).length + historyWriteSerial after stage := by
  cases hw : historyWrite after stage with
  | none => simp only [historyWritten, hw, Option.map_none] at hwritten; contradiction
  | some pair =>
    simp only [historyWriteSerial, historyWrite_referenceSuffixJoin I first before after stage hbefore,
      hw, Option.map_some, Option.getD_some]

theorem replayValidHandle_referenceSuffixJoin (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first)))
    (handle : MismatchHandle (I.freshSuffix first))
    (hw : historyWrite before (I.freshStageLift first handle.stage) = none)
    (hr : historyReport before (I.freshStageLift first handle.stage) = none)
    (hvalid : replayValidHandle after handle) :
    replayValidHandle (referenceSuffixHistoryJoin I first before after)
      (referenceSuffixHandleLift I first (historyActions before).length handle) := by
  cases hreport : historyReport after handle.stage with
  | none => simp only [replayValidHandle, hreport] at hvalid
  | some pair =>
    simp only [replayValidHandle, hreport] at hvalid
    have hnonempty : historyWritten after handle.stage ≠ none := by rw [hvalid.1]; simp
    simp only [replayValidHandle, referenceSuffixHandleLift,
      historyReport_referenceSuffixJoin I first before after handle.stage hr, hreport,
      Option.map_some]
    rw [historyWritten_referenceSuffixJoin I first before after handle.stage hw,
      historyWriteSerial_referenceSuffixJoin I first before after handle.stage hw hnonempty]
    exact ⟨hvalid.1, congrArg ((historyActions before).length + ·) hvalid.2.1,
      congrArg ((historyActions before).length + ·) hvalid.2.2⟩

structure Base (I : Instance) (first : ℕ) (before : List (VisibleEvent I))
    (available childAvailable : Finset I.Tool) : Prop where
  cursor : historyCursor before = first
  written : ∀ stage : (I.freshSuffix first).Stage,
    historyWrite before (I.freshStageLift first stage) = none
  reported : ∀ stage : (I.freshSuffix first).Stage,
    historyReport before (I.freshStageLift first stage) = none
  commitments : ∀ pair ∈ historyCommitments before, pair.1.stage.val < first
  executions : ∀ pair ∈ historyExecutions before, pair.1.stage.val < first
  available_subset : childAvailable ⊆ available
  unused : ∀ tool ∈ childAvailable, tool ∉ historyUsed before
  execution_disjoint : ∀ pair ∈ historyExecutions before, pair.2 ∉ childAvailable

theorem tool_mem_historyUsed {J : Instance} (history : List (VisibleEvent J))
    (handle : MismatchHandle J) (tool : J.Tool)
    (hm : (handle, tool) ∈ historyCommitments history) : tool ∈ historyUsed history := by
  exact List.mem_toFinset.mpr (List.mem_map.mpr ⟨(handle, tool), hm, rfl⟩)

theorem replayAllowsAction_referenceSuffixJoin (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first)))
    (available childAvailable : Finset I.Tool)
    (base : Base I first before available childAvailable)
    (hused : historyUsed after ⊆ childAvailable)
    (action : Action (I.freshSuffix first))
    (hallow : replayAllowsAction (I := I.freshSuffix first) childAvailable after action) :
    replayAllowsAction available (referenceSuffixHistoryJoin I first before after)
      (referenceSuffixActionLift I first (historyActions before).length action) := by
  have hcursor (stage : (I.freshSuffix first).Stage)
      (hc : historyCursor after = stage.val) :
      historyCursor (referenceSuffixHistoryJoin I first before after) =
        (I.freshStageLift first stage).val := by
    rw [historyCursor_referenceSuffixJoin, base.cursor, hc]
    rfl
  have hstage (stage : (I.freshSuffix first).Stage) :
      first ≤ (I.freshStageLift first stage).val := by
    change first ≤ first + stage.val
    omega
  cases action with
  | review stage =>
    exact ⟨hcursor stage hallow.1,
      (historyWritten_referenceSuffixJoin I first before after stage (base.written stage)).trans hallow.2⟩
  | write stage bit =>
    exact ⟨hcursor stage hallow.1,
      (historyWritten_referenceSuffixJoin I first before after stage (base.written stage)).trans hallow.2⟩
  | advance stage =>
    refine ⟨hcursor stage hallow.1, ?_⟩
    rw [historyWritten_referenceSuffixJoin I first before after stage (base.written stage)]
    exact hallow.2
  | allocate handle tool =>
    obtain ⟨htool, hc, hv, hcompat, hunused, hslot⟩ := hallow
    refine ⟨base.available_subset htool, hcursor handle.stage hc,
      replayValidHandle_referenceSuffixJoin I first before after handle
        (base.written handle.stage) (base.reported handle.stage) hv, ?_, ?_, ?_⟩
    · change tool ∈ I.eligible (I.freshStageLift first handle.stage)
      rw [← I.freshSuffix_eligible first handle.stage]
      exact hcompat
    · rw [historyUsed_referenceSuffixJoin]
      change (show I.Tool from tool) ∉
        (historyUsed before ∪ (show Finset I.Tool from historyUsed (I := I.freshSuffix first) after))
      intro hm
      rcases Finset.mem_union.mp hm with hold | hnew
      · exact base.unused tool htool hold
      · exact hunused hnew
    · intro pair hm
      rw [historyCommitments_referenceSuffixJoin] at hm
      rcases List.mem_append.mp hm with hold | hnew
      · intro heq
        have hlt := base.commitments pair hold
        have hge := hstage handle.stage
        have hh := congrArg Fin.val heq
        change pair.1.stage.val = (I.freshStageLift first handle.stage).val at hh
        omega
      · obtain ⟨child, hchild, heq⟩ := List.mem_map.mp hnew
        subst pair
        exact fun heq => hslot child hchild ((freshStageLift_injective I first) heq)
  | execute handle tool =>
    obtain ⟨hv, hcompat, hcommit, hunused, hslot⟩ := hallow
    have htool : tool ∈ childAvailable := hused (tool_mem_historyUsed after handle tool hcommit)
    refine ⟨replayValidHandle_referenceSuffixJoin I first before after handle
      (base.written handle.stage) (base.reported handle.stage) hv, ?_, ?_, ?_, ?_⟩
    · change tool ∈ I.eligible (I.freshStageLift first handle.stage)
      rw [← I.freshSuffix_eligible first handle.stage]
      exact hcompat
    · rw [historyCommitments_referenceSuffixJoin]
      exact List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨(handle, tool), hcommit, rfl⟩))
    · intro pair hm
      rw [historyExecutions_referenceSuffixJoin] at hm
      rcases List.mem_append.mp hm with hold | hnew
      · intro heq
        exact base.execution_disjoint pair hold (heq ▸ htool)
      · obtain ⟨child, hchild, heq⟩ := List.mem_map.mp hnew
        subst pair
        exact hunused child hchild
    · intro pair hm
      rw [historyExecutions_referenceSuffixJoin] at hm
      rcases List.mem_append.mp hm with hold | hnew
      · intro heq
        have hlt := base.executions pair hold
        have hge := hstage handle.stage
        have hh := congrArg Fin.val heq
        change pair.1.stage.val = (I.freshStageLift first handle.stage).val at hh
        omega
      · obtain ⟨child, hchild, heq⟩ := List.mem_map.mp hnew
        subst pair
        exact fun heq => hslot child hchild ((freshStageLift_injective I first) heq)
  | stop => trivial
  | abandon => trivial

theorem prefix_usesOnly_commitments {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (available : Finset I.Tool) (huses : UsesOnly input C accounting rule available)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes n s) :
    ∀ commitment ∈ s.ledger.commitments, commitment.tool ∈ available := by
  intro commitment hm
  exact (prefix_commitments_usable input C accounting rule available huses
    seed truth tapes hp commitment hm).1

theorem prefix_historyUsed_subset {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (available : Finset I.Tool) (huses : UsesOnly input C accounting rule available)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes n s) :
    historyUsed s.history ⊆ available := by
  intro tool hm
  obtain ⟨pair, hpair, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp hm)
  rw [prefix_historyCommitments input C .uncapped accounting rule seed truth tapes hp] at hpair
  obtain ⟨commitment, hcommit, hceq⟩ := List.mem_map.mp hpair
  have ht : commitment.tool = tool := by
    rw [← heq, ← hceq]
  exact ht ▸ prefix_usesOnly_commitments input C accounting rule available huses
    seed truth tapes hp commitment hcommit

/-- All base facts are consequences of a genuine first entry. The child
available set removes the old committed tools, including old executions. -/
theorem base_of_firstEntry {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (sample : Seed × input.World) (start : ℕ)
    (hentry : FirstEntryAt input C .uncapped accounting rule first start sample)
    (available : Finset I.Tool) :
    Base I first (run input C .uncapped accounting rule sample start).history
      available (available \ historyUsed (run input C .uncapped accounting rule sample start).history) := by
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample start
  have hinv := prefix_invariant input C .uncapped accounting rule sample.1 _ _ hp
  have hf := firstEntryAt_unborn input C .uncapped accounting rule hlegal sample first start hentry
  have hstage (stage : (I.freshSuffix first).Stage) :
      first ≤ (I.freshStageLift first stage).val := by
    change first ≤ first + stage.val
    omega
  refine ⟨?_, ?_, ?_, ?_, ?_, Finset.sdiff_subset, ?_, ?_⟩
  · exact (prefix_historyCursor input C .uncapped accounting rule sample.1 _ _ hp).trans hentry.1
  · intro stage
    have hw := prefix_historyWritten input C .uncapped accounting rule sample.1 _ _ hp
      (I.freshStageLift first stage)
    rw [(hf.2 (I.freshStageLift first stage) (hstage stage)).1] at hw
    cases hwrite : historyWrite (run input C .uncapped accounting rule sample start).history
        (I.freshStageLift first stage) with
    | none => rfl
    | some pair => simp only [historyWritten, hwrite, Option.map_some] at hw; cases hw
  · intro stage
    rw [prefix_historyReport_early input C hearly .uncapped accounting rule sample.1 _ _ hp]
    cases ht : (run input C .uncapped accounting rule sample start).ledger.reportTime
        (I.freshStageLift first stage) with
    | none => rfl
    | some time =>
      exact (hinv.report_written _ time ht ((hf.2 _ (hstage stage)).1)).elim
  · intro pair hm
    rw [prefix_historyCommitments input C .uncapped accounting rule sample.1 _ _ hp] at hm
    obtain ⟨commitment, hmem, rfl⟩ := List.mem_map.mp hm
    by_contra hnot
    have hg := (hinv.commitment_genuine commitment hmem).1
    rw [(hf.2 commitment.handle.stage (Nat.le_of_not_gt hnot)).1] at hg
    cases hg
  · intro pair hm
    rw [prefix_historyExecutions input C .uncapped accounting rule sample.1 _ _ hp] at hm
    obtain ⟨execution, hmem, rfl⟩ := List.mem_map.mp hm
    by_contra hnot
    have hg := (hinv.wellFormed.genuine execution hmem).1
    rw [(hf.2 execution.handle.stage (Nat.le_of_not_gt hnot)).1] at hg
    cases hg
  · intro tool hm
    exact (Finset.mem_sdiff.mp hm).2
  · intro pair hm hchild
    rw [prefix_historyExecutions input C .uncapped accounting rule sample.1 _ _ hp] at hm
    obtain ⟨execution, hmem, rfl⟩ := List.mem_map.mp hm
    obtain ⟨commitment, hcommit, _, ht, _⟩ := hinv.wellFormed.backed execution hmem
    have hpublic : (commitment.handle, commitment.tool) ∈
        historyCommitments (run input C .uncapped accounting rule sample start).history := by
      rw [prefix_historyCommitments input C .uncapped accounting rule sample.1 _ _ hp]
      exact List.mem_map.mpr ⟨commitment, hcommit, rfl⟩
    have hused := tool_mem_historyUsed _ commitment.handle commitment.tool hpublic
    exact (Finset.mem_sdiff.mp hchild).2 (ht ▸ hused)

/-- Child legality and UsesOnly give a concrete permission at its actual
prefix; the joined parent history preserves it under the proved base facts.
The next parent Step is a conclusion, never an input alignment premise. -/
theorem replayAllowsAction_of_prefixes {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (first : ℕ)
    (before : List (VisibleEvent I)) (available childAvailable : Finset I.Tool)
    (base : Base I first before available childAvailable)
    (child : AvailablePolicy (input.freshSuffix first)
      (currentRelaxedContract (I.freshSuffix first)) (zeroNormalAccounting (I.freshSuffix first))
      childAvailable Seed)
    (seed : Seed) (truth : (I.freshSuffix first).Stage → Bool)
    (tapes : ReviewTapes (input.freshSuffix first))
    {n : ℕ} {s : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      .uncapped (zeroNormalAccounting (I.freshSuffix first)) child.val.rule seed truth tapes n s)
    (ha : s.halted = false) :
    replayAllowsAction available (referenceSuffixHistoryJoin I first before s.history)
      (referenceSuffixActionLift I first (historyActions before).length (child.val.rule seed s.history)) := by
  obtain ⟨next, hs⟩ := child.val.legal seed truth tapes n s hp ha
  have hallow := replayAllowsAction_complete (input.freshSuffix first)
    (currentRelaxedContract (I.freshSuffix first)) rfl rfl .uncapped
    (zeroNormalAccounting (I.freshSuffix first)) child.val.rule seed truth tapes hp childAvailable hs
    (fun handle tool heq => child.property seed truth tapes n s hp ha handle tool heq)
  exact replayAllowsAction_referenceSuffixJoin I first before s.history available childAvailable base
    (prefix_historyUsed_subset (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      (zeroNormalAccounting (I.freshSuffix first)) child.val.rule childAvailable child.property
      seed truth tapes hp) _ hallow

/-- The implemented lifted child rule passes its public guard on every
actual child prefix, rather than only on successful or terminating paths. -/
theorem guarded_bellmanLiftedAfter_join {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (first : ℕ)
    (before : List (VisibleEvent I)) (available childAvailable : Finset I.Tool)
    (base : Base I first before available childAvailable)
    (child : AvailablePolicy (input.freshSuffix first)
      (currentRelaxedContract (I.freshSuffix first)) (zeroNormalAccounting (I.freshSuffix first))
      childAvailable Seed)
    (seed : Seed) (truth : (I.freshSuffix first).Stage → Bool)
    (tapes : ReviewTapes (input.freshSuffix first))
    {n : ℕ} {s : State (I.freshSuffix first)}
    (hp : Prefix (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      .uncapped (zeroNormalAccounting (I.freshSuffix first)) child.val.rule seed truth tapes n s)
    (ha : s.halted = false) :
    guardedReplayRule available (bellmanLiftedAfter first before child.val.rule) seed
        (referenceSuffixHistoryJoin I first before s.history) =
      referenceSuffixActionLift I first (historyActions before).length (child.val.rule seed s.history) := by
  have hallow := replayAllowsAction_of_prefixes input first before available childAvailable
    base child seed truth tapes hp ha
  simp only [guardedReplayRule, bellmanLiftedAfter_join, hallow, ↓reduceIte]

theorem childStep_lift_of_prefixes {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (hearly : C.reporting = .early) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (before : List (VisibleEvent I)) (available childAvailable : Finset I.Tool)
    (base : Base I first before available childAvailable)
    (child : AvailablePolicy (input.freshSuffix first)
      (currentRelaxedContract (I.freshSuffix first)) (zeroNormalAccounting (I.freshSuffix first))
      childAvailable Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (childTruth : (I.freshSuffix first).Stage → Bool)
    (childTapes : ReviewTapes (input.freshSuffix first))
    {m n : ℕ} {parent : State I} {childState : State (I.freshSuffix first)}
    (hp : Prefix input C .uncapped accounting rule seed truth tapes m parent)
    (hc : Prefix (input.freshSuffix first) (currentRelaxedContract (I.freshSuffix first))
      .uncapped (zeroNormalAccounting (I.freshSuffix first)) child.val.rule seed childTruth childTapes n childState)
    (view : ReferenceSuffixView I first before parent childState)
    (ha : parent.halted = false) :
    ∃ next, Step input C .uncapped accounting tapes parent
      (referenceSuffixActionLift I first (historyActions before).length
        (child.val.rule seed childState.history)) next := by
  have hchildActive : childState.halted = false := view.halted.symm.trans ha
  have hallow := replayAllowsAction_of_prefixes input first before available childAvailable
    base child seed childTruth childTapes hc hchildActive
  rw [← view.history] at hallow
  exact replayAllowsAction_sound input C hearly hdeferred accounting rule seed truth tapes hp ha available _ hallow

end GuardLift

end PaperProofs.Common.Native
