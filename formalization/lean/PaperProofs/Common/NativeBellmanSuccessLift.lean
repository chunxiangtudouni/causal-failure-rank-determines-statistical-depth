module

public import PaperProofs.Common.NativeBellmanUpper
public import PaperProofs.Common.HistorySuffixSuccess
public import PaperProofs.Common.NativeHeadAccounting

/-!
Success of an arbitrary actual suffix continuation transfers back to the
original native run once the old head obligations were genuinely resolved.
All written/executed facts are recovered from paired public histories and
real Prefix ledgers, not assumed as a success guarantee of the controller.
-/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem prefix_halted_not_abandoned_last_stopped {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {n : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes n s)
    (hhalt : s.halted = true) (habandon : s.ledger.abandoned = false) :
    s.history.getLast? = some .stopped := by
  cases hp with
  | initial => cases hhalt
  | next earlier hs =>
    generalize rule seed _ = action at hs
    cases hs <;> try cases hhalt
    · simp only [stopState, Bool.false_eq_true, ↓reduceIte, List.getLast?_append,
        List.getLast?_cons, List.getLast?_nil, Option.some_or, Option.getD_none]
    · cases habandon

theorem historyExecutions_referenceSuffixLift (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    historyExecutions (referenceSuffixHistoryLift I first clock history) =
      (historyExecutions history).map (fun pair =>
        (referenceSuffixHandleLift I first clock pair.1, pair.2)) := by
  induction history with
  | nil => rfl
  | cons event rest ih =>
    cases event <;> simp_all only [referenceSuffixHistoryLift, List.map_cons,
      historyExecutions, List.filterMap_cons, eventExecution, referenceSuffixEventLift,
      List.map_cons] <;> rfl

theorem historyWrite_referenceSuffixLift_old (I : Instance) (first clock : ℕ)
    (history : List (VisibleEvent (I.freshSuffix first))) (stage : I.Stage)
    (hold : stage.val < first) :
    historyWrite (referenceSuffixHistoryLift I first clock history) stage = none := by
  have hnone : ∀ event : VisibleEvent (I.freshSuffix first),
      eventWrite stage (referenceSuffixEventLift I first clock event) = none := by
    intro event
    cases event <;> try rfl
    rename_i source bit serial
    have hne : I.freshStageLift first source ≠ stage := by
      intro heq
      have hh := congrArg Fin.val heq
      change first + source.val = stage.val at hh
      omega
    simp only [referenceSuffixEventLift, eventWrite, hne, ↓reduceIte]
  have hf : history.filterMap (fun event => eventWrite stage (referenceSuffixEventLift I first clock event)) = [] :=
    List.filterMap_eq_nil_iff.mpr (fun event _ => hnone event)
  change (List.filterMap (eventWrite stage) (history.map (referenceSuffixEventLift I first clock))).getLast? = none
  rw [List.filterMap_map]
  change (history.filterMap (fun event => eventWrite stage (referenceSuffixEventLift I first clock event))).getLast? = none
  rw [hf]
  rfl

theorem historyWritten_referenceSuffixJoin_old (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first)))
    (stage : I.Stage) (hold : stage.val < first) :
    historyWritten (referenceSuffixHistoryJoin I first before after) stage =
      historyWritten before stage := by
  have he := historyWrite_referenceSuffixLift_old I first (historyActions before).length after stage hold
  simp only [historyWritten, historyWrite, referenceSuffixHistoryJoin, List.filterMap_append,
    List.getLast?_append] at he ⊢
  rw [he]
  rfl

theorem historyWritten_referenceSuffixJoin_future (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first)))
    (stage : (I.freshSuffix first).Stage)
    (hbefore : historyWrite before (I.freshStageLift first stage) = none) :
    historyWritten (referenceSuffixHistoryJoin I first before after) (I.freshStageLift first stage) =
      historyWritten after stage := by
  simp only [historyWritten, historyWrite_referenceSuffixJoin I first before after stage hbefore,
    Option.map_map, Function.comp_def]

theorem last_stopped_referenceSuffixJoin (I : Instance) (first : ℕ)
    (before : List (VisibleEvent I)) (after : List (VisibleEvent (I.freshSuffix first)))
    (hlast : after.getLast? = some .stopped) :
    (referenceSuffixHistoryJoin I first before after).getLast? = some .stopped := by
  simp only [referenceSuffixHistoryJoin, referenceSuffixHistoryLift, List.getLast?_append,
    List.getLast?_map, hlast, Option.map_some, referenceSuffixEventLift, Option.some_or]

/-- A successful actual child, with all old obligations already genuinely
resolved in the public prefix, gives actual parent success. No failure
event or expected-cost performance claim is assumed for either rule. -/
theorem suffixSuccess_of_prefixes {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (childC : Contract (I.freshSuffix first))
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed) (sample : Seed × input.World)
    (before : List (VisibleEvent I)) {m n : ℕ}
    {parent : State I} {child : State (I.freshSuffix first)}
    (hp : Prefix input C .uncapped accounting rule sample.1 (input.truthAt sample.2)
      (worldTapes input sample.2) m parent)
    (hc : Prefix (input.freshSuffix first) childC .uncapped childAccounting childRule sample.1
      ((input.freshSuffix first).truthAt (referenceSuffixWorld input first sample.2))
      (worldTapes (input.freshSuffix first) (referenceSuffixWorld input first sample.2)) n child)
    (view : ReferenceSuffixView I first before parent child)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage,
      historyWrite before (I.freshStageLift first stage) = none)
    (hresolved : ∀ stage : I.Stage, stage.val < first →
      historyWritten before stage = some (input.truthAt sample.2 stage) ∨
        ∃ pair ∈ historyExecutions before, pair.1.stage = stage)
    (hhalt : child.halted = true) (hsuccess : child.ledger.success childC) :
    parent.ledger.success C := by
  have hparentTruth := prefix_truth input C .uncapped accounting rule sample.1 _ _ hp
  have hchildTruth := prefix_truth (input.freshSuffix first) childC .uncapped childAccounting childRule sample.1 _ _ hc
  have htruth (stage : (I.freshSuffix first).Stage) :
      parent.ledger.truth (I.freshStageLift first stage) = child.ledger.truth stage := by
    rw [hparentTruth, hchildTruth]
    rfl
  have hwritten (stage : (I.freshSuffix first).Stage) :
      parent.ledger.written (I.freshStageLift first stage) = child.ledger.written stage := by
    rw [← prefix_historyWritten input C .uncapped accounting rule sample.1 _ _ hp,
      view.history, historyWritten_referenceSuffixJoin_future I first before child.history stage (hbefore stage)]
    exact prefix_historyWritten (input.freshSuffix first) childC .uncapped childAccounting childRule sample.1 _ _ hc stage
  have parentExecution (pair : MismatchHandle I × I.Tool)
      (hmem : pair ∈ historyExecutions parent.history) :
      ∃ e ∈ parent.ledger.executions, e.handle.stage = pair.1.stage := by
    rw [prefix_historyExecutions input C .uncapped accounting rule sample.1 _ _ hp] at hmem
    obtain ⟨e, he, heq⟩ := List.mem_map.mp hmem
    exact ⟨e, he, congrArg (fun p => p.1.stage) heq⟩
  have hcorrect (stage : I.Stage) :
      parent.ledger.written stage = some (parent.ledger.truth stage) ∨
        ∃ e ∈ parent.ledger.executions, e.handle.stage = stage := by
    by_cases hold : stage.val < first
    · rcases hresolved stage hold with hw | ⟨pair, hpair, hstage⟩
      · left
        rw [← prefix_historyWritten input C .uncapped accounting rule sample.1 _ _ hp,
          view.history, historyWritten_referenceSuffixJoin_old I first before child.history stage hold,
          hw, hparentTruth]
      · right
        have hmem : pair ∈ historyExecutions parent.history := by
          rw [view.history]
          change pair ∈ (before ++ referenceSuffixHistoryLift I first (historyActions before).length child.history).filterMap eventExecution
          rw [List.filterMap_append]
          exact List.mem_append_left _ hpair
        obtain ⟨e, he, hs⟩ := parentExecution pair hmem
        exact ⟨e, he, hs.trans hstage⟩
    · have hfuture : first ≤ stage.val := Nat.le_of_not_gt hold
      let target := suffixStageOf first stage hfuture
      have htarget : I.freshStageLift first target = stage := freshStageLift_suffixStageOf first stage hfuture
      rcases hsuccess.2.2.2 target with hright | ⟨e, he, hstage⟩
      · left
        rw [← htarget, hwritten target, htruth target]
        exact hright
      · right
        have hchildMem : (e.handle, e.tool) ∈ historyExecutions child.history := by
          rw [prefix_historyExecutions (input.freshSuffix first) childC .uncapped childAccounting childRule sample.1 _ _ hc]
          exact List.mem_map.mpr ⟨e, he, rfl⟩
        let pair : MismatchHandle I × I.Tool :=
          (referenceSuffixHandleLift I first (historyActions before).length e.handle, e.tool)
        have hparentMem : pair ∈ historyExecutions parent.history := by
          rw [view.history]
          change pair ∈ (before ++ referenceSuffixHistoryLift I first (historyActions before).length child.history).filterMap eventExecution
          rw [List.filterMap_append]
          apply List.mem_append_right
          change pair ∈ historyExecutions (referenceSuffixHistoryLift I first (historyActions before).length child.history)
          rw [historyExecutions_referenceSuffixLift]
          exact List.mem_map.mpr ⟨(e.handle, e.tool), hchildMem, rfl⟩
        obtain ⟨parentE, hparentE, hstageE⟩ := parentExecution pair hparentMem
        refine ⟨parentE, hparentE, hstageE.trans ?_⟩
        change I.freshStageLift first e.handle.stage = stage
        rw [hstage, htarget]
  have hparentHalt : parent.halted = true := view.halted.trans hhalt
  have hchildLast := prefix_halted_not_abandoned_last_stopped (input.freshSuffix first)
    childC .uncapped childAccounting childRule sample.1 _ _ hc hhalt hsuccess.2.1
  have hparentLast : parent.history.getLast? = some .stopped := by
    rw [view.history]
    exact last_stopped_referenceSuffixJoin I first before child.history hchildLast
  have habandon := prefix_last_stopped_not_abandoned input C hearly .uncapped accounting rule sample.1 _ _ hp hparentLast
  have hwf := prefix_ledgerWellFormed input C .uncapped accounting rule sample.1 _ _ hp
  have hall : allWritten parent.ledger := by
    intro stage
    rcases hcorrect stage with hw | ⟨e, he, hs⟩
    · rw [hw]
      intro hnone
      cases hnone
    · have hg := (hwf.genuine e he).1
      rw [hs] at hg
      rw [hg]
      intro hnone
      cases hnone
  have hfinished := prefix_halted_allWritten_finished input C .uncapped accounting rule sample.1 _ _ hp hparentHalt hall
  apply (prefix_success_iff_physical input C .uncapped accounting rule sample.1 _ _ hp).mpr
  exact ⟨hfinished, habandon, fun stage => (finalOutput_correct_iff _ stage).mpr (hcorrect stage)⟩

theorem suffixRun_success_of_views {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first))
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage,
      historyWrite before (I.freshStageLift first stage) = none)
    (hresolved : ∀ stage : I.Stage, stage.val < first →
      historyWritten before stage = some (input.truthAt sample.2 stage) ∨
        ∃ pair ∈ historyExecutions before, pair.1.stage = stage)
    (views : ∀ k : ℕ, ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k))
    (hsuccess : runSuccess (input.freshSuffix first) childC .uncapped childAccounting childRule
      (sample.1, referenceSuffixWorld input first sample.2)) :
    runSuccess input C .uncapped accounting rule sample := by
  obtain ⟨k, hh, hs⟩ := hsuccess
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (start + k)
  obtain ⟨n, _, hc⟩ := run_has_prefix (input.freshSuffix first) childC .uncapped childAccounting childRule
    hchildLegal (sample.1, referenceSuffixWorld input first sample.2) k
  exact ⟨start + k, (views k).halted.trans hh,
    suffixSuccess_of_prefixes input first C hearly accounting rule childC childAccounting childRule sample before
      hp hc (views k) hbefore hresolved hh hs⟩

/-- All remaining paid observations agree exactly with the child, including
failed, abandoned and infinite paths. Old-stage review counts freeze behind
the real cursor; future-stage counts start at zero by the public history. -/
theorem suffixRun_futureObservationBill_of_views {Seed : Type*}
    (input : StatisticalInput I) (first : ℕ) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first))
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage,
      historyObservations before (I.freshStageLift first stage) = [])
    (views : ∀ k : ℕ, ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k)) :
    futureObservationBill input C .uncapped accounting rule start sample =
      runObservationBill (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) := by
  let childSample := (sample.1, referenceSuffixWorld input first sample.2)
  let parentAt := fun k => run input C .uncapped accounting rule sample (start + k)
  let childAt := fun k => run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k
  have hcounts (k : ℕ) (stage : (I.freshSuffix first).Stage) :
      (parentAt k).ledger.reviews (I.freshStageLift first stage) = (childAt k).ledger.reviews stage := by
    obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (start + k)
    obtain ⟨n, _, hc⟩ := run_has_prefix (input.freshSuffix first) childC .uncapped childAccounting childRule hchildLegal childSample k
    exact referenceSuffix_reviews_of_prefixes input first C accounting rule childC childAccounting childRule
      sample.1 _ _ _ _ hp hc before (views k) hbefore stage
  have hcursor : (run input C .uncapped accounting rule sample start).cursor = first := by
    simpa only [Nat.add_zero, run, initial] using (views 0).cursor
  unfold futureObservationBill runObservationBill
  apply iSup_congr
  intro k
  change observationIncrement input (run input C .uncapped accounting rule sample start) (parentAt k) =
    (childAt k).ledger.observationBill (input.freshSuffix first).fees
  have hsum : observationIncrement input (run input C .uncapped accounting rule sample start) (parentAt k) =
      ∑ stage : I.Stage, if first ≤ stage.val then
        ENNReal.ofReal (input.fees.observation stage : ℝ) * ((parentAt k).ledger.reviews stage : ℝ≥0∞) else 0 := by
    unfold observationIncrement
    apply Finset.sum_congr rfl
    intro stage _
    by_cases hf : first ≤ stage.val
    · let target := suffixStageOf first stage hf
      have hlift : I.freshStageLift first target = stage := freshStageLift_suffixStageOf first stage hf
      have hz := hcounts 0 target
      change (run input C .uncapped accounting rule sample (start + 0)).ledger.reviews
        (I.freshStageLift first target) = 0 at hz
      rw [Nat.add_zero, hlift] at hz
      simp only [hf, ↓reduceIte, hz, tsub_zero]
    · have hold : stage.val < (run input C .uncapped accounting rule sample start).cursor := by rw [hcursor]; omega
      have he := run_reviews_behind_cursor input C .uncapped accounting rule hlegal sample start k stage hold
      change (parentAt k).ledger.reviews stage = _ at he
      simp only [hf, ↓reduceIte, he, tsub_self, ENat.toENNReal_zero, mul_zero]
  rw [hsum, sum_referenceSuffix_stages]
  unfold Ledger.observationBill
  apply Finset.sum_congr rfl
  intro stage _
  have hfee := congrArg PaperProofs.Statistics.BinaryExperiment.observationFee
    (input.freshSuffix_experiment first stage)
  change (input.freshSuffix first).fees.observation stage = input.fees.observation (I.freshStageLift first stage) at hfee
  rw [hfee, hcounts k stage]

/-- With the same original eventual-failure penalty, continuation success
dominates parent failure pointwise and all future observation costs agree.
No successful-path conditioning or finite-bill assumption is introduced. -/
theorem suffixRun_comparisonCharge_le {Seed : Type*}
    (input : StatisticalInput I) (first : ℕ) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first))
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbeforeObs : ∀ stage : (I.freshSuffix first).Stage,
      historyObservations before (I.freshStageLift first stage) = [])
    (hbeforeWrite : ∀ stage : (I.freshSuffix first).Stage,
      historyWrite before (I.freshStageLift first stage) = none)
    (hresolved : ∀ stage : I.Stage, stage.val < first →
      historyWritten before stage = some (input.truthAt sample.2 stage) ∨
        ∃ pair ∈ historyExecutions before, pair.1.stage = stage)
    (views : ∀ k : ℕ, ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k))
    (penalty : ℝ≥0∞) :
    historyComparisonCharge input C .uncapped accounting rule start penalty sample ≤
      runPenaltyCharge (input.freshSuffix first) childC .uncapped childAccounting childRule penalty
        (sample.1, referenceSuffixWorld input first sample.2) := by
  classical
  unfold historyComparisonCharge runPenaltyCharge
  rw [suffixRun_futureObservationBill_of_views input first C accounting rule hlegal childC
    childAccounting childRule hchildLegal sample before start hbeforeObs views]
  by_cases hs : runSuccess (input.freshSuffix first) childC .uncapped childAccounting childRule
      (sample.1, referenceSuffixWorld input first sample.2)
  · have hp := suffixRun_success_of_views input first C hearly accounting rule hlegal childC
      childAccounting childRule hchildLegal sample before start hbeforeWrite hresolved views hs
    simp only [ite_eq_left hs, ite_eq_left hp, le_refl]
  · rw [ite_eq_right hs]
    split_ifs with hp
    · simp only [add_zero]
      exact le_self_add
    · exact le_rfl

/-- The original whole-run penalty charge is bounded by the actual prefix
observation bill plus the unchanged full-policy child charge. -/
theorem suffixRun_penaltyCharge_le_prefix_add_child {Seed : Type*}
    (input : StatisticalInput I) (first : ℕ) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first))
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbeforeObs : ∀ stage : (I.freshSuffix first).Stage,
      historyObservations before (I.freshStageLift first stage) = [])
    (hbeforeWrite : ∀ stage : (I.freshSuffix first).Stage,
      historyWrite before (I.freshStageLift first stage) = none)
    (hresolved : ∀ stage : I.Stage, stage.val < first →
      historyWritten before stage = some (input.truthAt sample.2 stage) ∨
        ∃ pair ∈ historyExecutions before, pair.1.stage = stage)
    (views : ∀ k : ℕ, ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k))
    (penalty : ℝ≥0∞) :
    runPenaltyCharge input C .uncapped accounting rule penalty sample ≤
      (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
        runPenaltyCharge (input.freshSuffix first) childC .uncapped childAccounting childRule penalty
          (sample.1, referenceSuffixWorld input first sample.2) := by
  classical
  have hdom := suffixRun_comparisonCharge_le input first C hearly accounting rule hlegal childC
    childAccounting childRule hchildLegal sample before start hbeforeObs hbeforeWrite hresolved views penalty
  have hsplit : runPenaltyCharge input C .uncapped accounting rule penalty sample =
      (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees +
        historyComparisonCharge input C .uncapped accounting rule start penalty sample := by
    unfold runPenaltyCharge historyComparisonCharge
    rw [runObservationBill_eq_prefix_add_future input C .uncapped accounting rule hlegal sample start, add_assoc]
  rw [hsplit]
  exact add_le_add le_rfl hdom

end PaperProofs.Common.Native
