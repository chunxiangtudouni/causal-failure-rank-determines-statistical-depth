module

public import PaperProofs.Common.NativeBellmanHistoryLift
public import PaperProofs.Common.NativeBellmanGuardLift

/-! Actual arbitrary-policy continuation runs for B08. Action identification
is needed only on active prefixes; halted rules are never queried by the run.
The concrete branch lemmas below discharge this local interface from the
actual head construction, public-history parser and child legality. -/

@[expose] public section

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem suffixRun_view_of_rule_lift_active {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (childC : Contract (I.freshSuffix first)) (hchildEarly : childC.reporting = .early)
    (childAccounting : NormalAccounting (I.freshSuffix first))
    (childRule : PolicyRule (I.freshSuffix first) Seed)
    (hchildLegal : LegalRule (input.freshSuffix first) childC .uncapped childAccounting childRule)
    (sample : Seed × input.World) (before : List (VisibleEvent I)) (start : ℕ)
    (hbefore : ∀ stage : (I.freshSuffix first).Stage,
      historyObservations before (I.freshStageLift first stage) = [])
    (hstart : ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample start)
      (initial ((input.freshSuffix first).truthAt (referenceSuffixWorld input first sample.2))))
    (hlift : ∀ k : ℕ,
      ReferenceSuffixView I first before
        (run input C .uncapped accounting rule sample (start + k))
        (run (input.freshSuffix first) childC .uncapped childAccounting childRule
          (sample.1, referenceSuffixWorld input first sample.2) k) →
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k).halted = false →
      rule sample.1 (run input C .uncapped accounting rule sample (start + k)).history =
        referenceSuffixActionLift I first (historyActions before).length
          (childRule sample.1 (run (input.freshSuffix first) childC .uncapped childAccounting
            childRule (sample.1, referenceSuffixWorld input first sample.2) k).history)) :
    ∀ k : ℕ, ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule
        (sample.1, referenceSuffixWorld input first sample.2) k) := by
  let childSample : Seed × (input.freshSuffix first).World :=
    (sample.1, referenceSuffixWorld input first sample.2)
  intro k
  induction k with
  | zero => simpa only [Nat.add_zero, run] using hstart
  | succ k ih =>
    change ReferenceSuffixView I first before
      (run input C .uncapped accounting rule sample (start + (k + 1)))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample (k + 1))
    by_cases hh : (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).halted = true
    · have hparentHalt : (run input C .uncapped accounting rule sample (start + k)).halted = true := ih.halted.trans hh
      rw [Nat.add_succ, run_succ_of_halted input C .uncapped accounting rule sample (start + k) hparentHalt,
        run_succ_of_halted (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k hh]
      exact ih
    · have hchildActive : (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).halted = false :=
        Bool.eq_false_iff.mpr hh
      have hparentActive : (run input C .uncapped accounting rule sample (start + k)).halted = false := ih.halted.trans hchildActive
      obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (start + k)
      obtain ⟨l, _, hc⟩ := run_has_prefix (input.freshSuffix first) childC .uncapped childAccounting childRule hchildLegal childSample k
      have ha := hlift k ih hchildActive
      obtain ⟨nextParent, hps⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) m _ hp hparentActive
      obtain ⟨nextChild, hcs⟩ := hchildLegal sample.1 ((input.freshSuffix first).truthAt childSample.2)
        (worldTapes (input.freshSuffix first) childSample.2) l _ hc hchildActive
      have hpsLift := hps
      rw [ha] at hpsLift
      have hcounts := referenceSuffix_reviews_of_prefixes input first C accounting rule childC childAccounting childRule sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) ((input.freshSuffix first).truthAt childSample.2)
        (worldTapes (input.freshSuffix first) childSample.2) hp hc before ih hbefore
      have htruths : ∀ stage, (run input C .uncapped accounting rule sample (start + k)).ledger.truth (I.freshStageLift first stage) =
          (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).ledger.truth stage := by
        intro stage
        calc
          _ = input.truthAt sample.2 (I.freshStageLift first stage) := congrFun (prefix_truth input C .uncapped accounting rule sample.1 _ _ hp) _
          _ = (input.freshSuffix first).truthAt childSample.2 stage := rfl
          _ = _ := (congrFun (prefix_truth (input.freshSuffix first) childC .uncapped childAccounting childRule sample.1 _ _ hc) stage).symm
      have hnext := referenceSuffix_step_view input first C childC hearly hchildEarly accounting childAccounting
        (worldTapes input sample.2) (worldTapes (input.freshSuffix first) childSample.2) before ih hcounts htruths
        (fun stage index => (referenceSuffixWorld_letter input first sample.2 stage index).symm) hpsLift hcs
      rw [Nat.add_succ, run_succ_of_step input C .uncapped accounting rule sample (start + k) nextParent hparentActive hps,
        run_succ_of_step (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k nextChild hchildActive hcs]
      exact hnext


theorem bellmanEntry_observations_empty {Seed : Type*} (input : StatisticalInput I) (first : ℕ)
    (C : Contract I) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (hlegal : LegalRule input C .uncapped accounting rule) (sample : Seed × input.World)
    (start : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule first start sample) :
    ∀ stage : (I.freshSuffix first).Stage,
      historyObservations (run input C .uncapped accounting rule sample start).history
        (I.freshStageLift first stage) = [] := by
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample start
  have hf := firstEntryAt_unborn input C .uncapped accounting rule hlegal sample first start hentry
  intro stage
  have hge : first ≤ (I.freshStageLift first stage).val := by change first ≤ first + stage.val; omega
  have hzero := (hf.2 (I.freshStageLift first stage) hge).2
  have hlen := prefix_historyObservations_length_toNat input C .uncapped accounting rule sample.1 _ _ hp
    (I.freshStageLift first stage)
  rw [hzero, ENat.toNat_zero] at hlen
  exact List.eq_nil_of_length_eq_zero hlen

set_option maxHeartbeats 800000 in
theorem bellmanHeadThen_correct_firstEntry {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head) :
    FirstEntryAt input C .uncapped accounting
      (bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head repair good bad))
      1 (n + 2) sample := by
  let after := bellmanPostHeadRaw input head repair good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good bad hgood hbad)
  have hbefore : (run input C .uncapped accounting policy.val.rule sample (n + 1)).cursor = 0 := by
    exact (congrArg (fun s : State I => s.cursor)
      (bellmanHeadThen_run_write input C accounting head hhead test available after sample n hstop)).trans
        (bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
          (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)))
  have hafter : (run input C .uncapped accounting policy.val.rule sample (n + 2)).cursor = 1 := by
    exact congrArg (fun s : State I => s.cursor)
      (bellmanHeadThen_run_correct_advance input C hearly hcurrent hdeferred accounting head hhead test available
        repair good bad hgood hbad sample n hstop hcorrect)
  exact bellman_firstEntryAt_of_zero_to_one input C .uncapped accounting policy.val.rule policy.val.legal
    sample (n + 1) hbefore hafter

set_option maxHeartbeats 800000 in
theorem bellmanHeadThen_wrong_firstEntry {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    FirstEntryAt input C .uncapped accounting
      (bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad))
      1 (n + 4) sample := by
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  have hbefore : (run input C .uncapped accounting policy.val.rule sample (n + 3)).cursor = 0 := by
    exact (congrArg (fun s : State I => s.cursor)
      (bellmanHeadThen_run_wrong_execute input C hearly hcurrent hdeferred accounting head hhead test available
        tool htool heligible good bad hgood hbad sample n hstop hwrong)).trans
      (bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)))
  have hafter : (run input C .uncapped accounting policy.val.rule sample (n + 4)).cursor = 1 := by
    exact congrArg (fun s : State I => s.cursor)
      (bellmanHeadThen_run_wrong_advance input C hearly hcurrent hdeferred accounting head hhead test available
        tool htool heligible good bad hgood hbad sample n hstop hwrong)
  exact bellman_firstEntryAt_of_zero_to_one input C .uncapped accounting policy.val.rule policy.val.legal
    sample (n + 3) hbefore hafter

set_option maxHeartbeats 1200000 in
theorem bellmanHeadThen_correct_run_view {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Seed)
    (bad : PolicyRule (I.freshSuffix 1) Seed) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head) :
    let rule := bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head repair good.val.rule bad)
    let before := (run input C .uncapped accounting rule sample (n + 2)).history
    ∀ k : ℕ, ReferenceSuffixView I 1 before
      (run input C .uncapped accounting rule sample (n + 2 + k))
      (run (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule
        (sample.1, referenceSuffixWorld input 1 sample.2) k) := by
  let after := bellmanPostHeadRaw input head repair good.val.rule bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good.val.rule bad good.val.measurable_rule hbad)
  let before := (run input C .uncapped accounting policy.val.rule sample (n + 2)).history
  have hentry := bellmanHeadThen_correct_firstEntry input C hearly hcurrent hdeferred accounting head hhead test available
    repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
  have hbeforeObs := bellmanEntry_observations_empty input 1 C accounting policy.val.rule policy.val.legal
    sample (n + 2) hentry
  have hbase0 := GuardLift.base_of_firstEntry input 1 C hearly accounting policy.val.rule policy.val.legal
    sample (n + 2) hentry available
  obtain ⟨_, _, hpStart⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 2)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hrAdvance : run input C .uncapped accounting policy.val.rule sample (n + 2) =
      record accounting written (.advance head) [.advanced head] (advanceLedger written head) 1 false :=
    bellmanHeadThen_run_correct_advance input C hearly hcurrent hdeferred accounting head hhead test available
      repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
  have hcomms : historyCommitments before = [] := by
    have hq := prefix_historyCommitments input C .uncapped accounting policy.val.rule sample.1 _ _ hpStart
    have hfield : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.commitments = [] := by
      rw [hrAdvance]
      exact (bellmanHeadWrittenState_empty_corrections input C hearly accounting head
        (input.truthAt sample.2) (worldTapes input sample.2 head) n _).1
    rw [hfield, List.map_nil] at hq
    exact hq
  have hused : historyUsed before = ∅ := by simp only [historyUsed, hcomms, List.map_nil, List.toFinset_nil]
  have hbase : GuardLift.Base I 1 before available available := by
    change GuardLift.Base I 1 before available (available \ historyUsed before) at hbase0
    simpa only [hused, Finset.sdiff_empty] using hbase0
  have hbeforeWritten : historyWritten before head ≠ none := by
    have hw := prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hpStart head
    have hfield : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.written head =
        some (test.rule.decision sample.1 (worldTapes input sample.2 head)) := by
      rw [hrAdvance]
      exact bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    have hsome : historyWritten before head = some (test.rule.decision sample.1 (worldTapes input sample.2 head)) :=
      hw.trans hfield
    rw [hsome]
    exact Option.some_ne_none _
  apply suffixRun_view_of_rule_lift_active input 1 C hearly accounting policy.val.rule policy.val.legal
    (currentRelaxedContract (I.freshSuffix 1)) rfl (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule good.val.legal
    sample before (n + 2) hbeforeObs
    (bellmanHeadThen_correct_initialView input C hearly hcurrent hdeferred accounting head hhead test available
      repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect)
  intro k view hactive
  let childSample : Seed × (input.freshSuffix 1).World := (sample.1, referenceSuffixWorld input 1 sample.2)
  obtain ⟨_, _, hpChild⟩ := run_has_prefix (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
    .uncapped (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule good.val.legal childSample k
  have hpost := bellmanPostHeadRaw_correct_actual_join input C hearly hcurrent hdeferred accounting head hhead test available
    repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
      (run (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule childSample k).history
  have hraw : bellmanHeadThenRaw input head test after sample.1
      (run input C .uncapped accounting policy.val.rule sample (n + 2 + k)).history =
      referenceSuffixActionLift I 1 (historyActions before).length
        (good.val.rule sample.1 (run (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule childSample k).history) := by
    rw [view.history]
    have hheadEarlier : head.val < 1 := by omega
    simp only [bellmanHeadThenRaw, historyWritten_referenceSuffixJoin_earlier 1 head hheadEarlier,
      hbeforeWritten, ↓reduceIte]
    exact hpost
  have hallow := GuardLift.replayAllowsAction_of_prefixes input 1 before available available hbase good
    sample.1 _ _ hpChild hactive
  change guardedReplayRule available (bellmanHeadThenRaw input head test after) sample.1
    (run input C .uncapped accounting policy.val.rule sample (n + 2 + k)).history = _
  simp only [guardedReplayRule, hraw]
  rw [view.history]
  exact ite_eq_left hallow

set_option maxHeartbeats 1200000 in
theorem bellmanHeadThen_wrong_run_view {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good : PolicyRule (I.freshSuffix 1) Seed) (hgood : MeasurableRule good)
    (bad : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) (available.erase tool) Seed)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let rule := bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad.val.rule)
    let before := (run input C .uncapped accounting rule sample (n + 4)).history
    ∀ k : ℕ, ReferenceSuffixView I 1 before
      (run input C .uncapped accounting rule sample (n + 4 + k))
      (run (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule
        (sample.1, referenceSuffixWorld input 1 sample.2) k) := by
  let after := bellmanPostHeadRaw input head (some tool) good bad.val.rule
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad.val.rule hgood bad.val.measurable_rule)
  let before := (run input C .uncapped accounting policy.val.rule sample (n + 4)).history
  have hentry := bellmanHeadThen_wrong_firstEntry input C hearly hcurrent hdeferred accounting head hhead test available
    tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
  have hbeforeObs := bellmanEntry_observations_empty input 1 C accounting policy.val.rule policy.val.legal
    sample (n + 4) hentry
  have hbase0 := GuardLift.base_of_firstEntry input 1 C hearly accounting policy.val.rule policy.val.legal
    sample (n + 4) hentry available
  obtain ⟨_, _, hpStart⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 4)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let executed := bellmanExecuteState accounting allocated head tool
  let handle : MismatchHandle I := ⟨head, written.ledger.writeSerial head⟩
  have hrAdvance : run input C .uncapped accounting policy.val.rule sample (n + 4) =
      record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false :=
    bellmanHeadThen_run_wrong_advance input C hearly hcurrent hdeferred accounting head hhead test available
      tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
  have hcomms : historyCommitments before = [(handle, tool)] := by
    change historyCommitments (run input C .uncapped accounting policy.val.rule sample (n + 4)).history = _
    rw [hrAdvance]
    exact (bellmanRepairedEntry_history_corrections input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)) tool).1
  have hused : historyUsed before = {tool} := by
    simp only [historyUsed, hcomms, List.map_cons, List.map_nil, List.toFinset_cons, List.toFinset_nil,
      Finset.insert_empty]
  have hbase : GuardLift.Base I 1 before available (available.erase tool) := by
    change GuardLift.Base I 1 before available (available \ historyUsed before) at hbase0
    simpa only [hused, Finset.sdiff_singleton_eq_erase] using hbase0
  have hbeforeWritten : historyWritten before head ≠ none := by
    have hw := prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hpStart head
    have hfield : (run input C .uncapped accounting policy.val.rule sample (n + 4)).ledger.written head =
        some (test.rule.decision sample.1 (worldTapes input sample.2 head)) := by
      rw [hrAdvance]
      change written.ledger.written head = some (test.rule.decision sample.1 (worldTapes input sample.2 head))
      exact bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    have hsome : historyWritten before head = some (test.rule.decision sample.1 (worldTapes input sample.2 head)) :=
      hw.trans hfield
    rw [hsome]
    exact Option.some_ne_none _
  apply suffixRun_view_of_rule_lift_active input 1 C hearly accounting policy.val.rule policy.val.legal
    (currentRelaxedContract (I.freshSuffix 1)) rfl (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule bad.val.legal
    sample before (n + 4) hbeforeObs
    (bellmanHeadThen_wrong_initialView input C hearly hcurrent hdeferred accounting head hhead test available
      tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong)
  intro k view hactive
  let childSample : Seed × (input.freshSuffix 1).World := (sample.1, referenceSuffixWorld input 1 sample.2)
  obtain ⟨_, _, hpChild⟩ := run_has_prefix (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
    .uncapped (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule bad.val.legal childSample k
  have hpost := bellmanPostHeadRaw_wrong_actual_join input C hearly hcurrent hdeferred accounting head hhead test available
    tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
      (run (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
        (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule childSample k).history
  have hraw : bellmanHeadThenRaw input head test after sample.1
      (run input C .uncapped accounting policy.val.rule sample (n + 4 + k)).history =
      referenceSuffixActionLift I 1 (historyActions before).length
        (bad.val.rule sample.1 (run (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule childSample k).history) := by
    rw [view.history]
    have hheadEarlier : head.val < 1 := by omega
    simp only [bellmanHeadThenRaw, historyWritten_referenceSuffixJoin_earlier 1 head hheadEarlier,
      hbeforeWritten, ↓reduceIte]
    exact hpost
  have hallow := GuardLift.replayAllowsAction_of_prefixes input 1 before available (available.erase tool) hbase bad
    sample.1 _ _ hpChild hactive
  change guardedReplayRule available (bellmanHeadThenRaw input head test after) sample.1
    (run input C .uncapped accounting policy.val.rule sample (n + 4 + k)).history = _
  simp only [guardedReplayRule, hraw]
  rw [view.history]
  exact ite_eq_left hallow

end PaperProofs.Common.Native
