module

public import PaperProofs.Common.NativeBellmanContinuationRun
public import PaperProofs.Common.NativeBellmanSuccessLift

/-! Actual pointwise observation-plus-one-failure bounds for the original
Bellman construction. Every continuation fact is obtained from the concrete
head branches and all-clock views, never from a risk or cost hypothesis. -/

@[expose] public section

open scoped ENNReal

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem bellmanHeadWrittenState_reviews_eq (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (head : I.Stage)
    (truth : I.Stage → Bool) (tape : (input.experiment head).Tape) (n : ℕ) (bit : Bool) :
    (bellmanHeadWrittenState input C accounting head truth tape n bit).ledger.reviews head = n := by
  simpa only [bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
    writeLedger] using headReviewState_reviews input accounting head truth tape n

theorem bellmanPrefix_observationBill_of_entry {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C .uncapped accounting rule)
    (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (sample : Seed × input.World)
    (start : ℕ) (hentry : FirstEntryAt input C .uncapped accounting rule 1 start sample)
    (hcount : (run input C .uncapped accounting rule sample start).ledger.reviews head =
      test.rule.stop sample.1 (worldTapes input sample.2 head)) :
    (run input C .uncapped accounting rule sample start).ledger.observationBill input.fees =
      (input.experiment head).observationCharge
        (test.rule.stop sample.1 (worldTapes input sample.2 head)) := by
  rw [firstEntry_one_prefix_observationBill input C accounting rule hlegal head hhead sample start hentry]
  have hport := firstEntry_one_head_written input C .uncapped accounting rule hlegal head hhead sample start hentry
  cases hw : (run input C .uncapped accounting rule sample start).ledger.written head with
  | none => exact (hport hw).elim
  | some bit =>
    rw [nativeHead_count_of_written input C accounting rule hlegal head hhead sample start bit hw, hcount]

set_option maxHeartbeats 1200000 in
theorem bellmanHeadThen_correct_penaltyCharge_le {Seed : Type*} [MeasurableSpace Seed]
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
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head)
    (penalty : ℝ≥0∞) :
    runPenaltyCharge input C .uncapped accounting
      (bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head repair good.val.rule bad)) penalty sample ≤
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
        runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule penalty
          (sample.1, referenceSuffixWorld input 1 sample.2) := by
  let after := bellmanPostHeadRaw input head repair good.val.rule bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good.val.rule bad good.val.measurable_rule hbad)
  let before := (run input C .uncapped accounting policy.val.rule sample (n + 2)).history
  have hentry := bellmanHeadThen_correct_firstEntry input C hearly hcurrent hdeferred accounting head hhead test available
    repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
  have hobs := bellmanEntry_observations_empty input 1 C accounting policy.val.rule policy.val.legal sample (n + 2) hentry
  have hbase := GuardLift.base_of_firstEntry input 1 C hearly accounting policy.val.rule policy.val.legal
    sample (n + 2) hentry available
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 2) =
      record accounting written (.advance head) [.advanced head] (advanceLedger written head) 1 false :=
    bellmanHeadThen_run_correct_advance input C hearly hcurrent hdeferred accounting head hhead test available
      repair good.val.rule bad good.val.measurable_rule hbad sample n hstop hcorrect
  obtain ⟨_, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 2)
  have hresolved : ∀ stage : I.Stage, stage.val < 1 →
      historyWritten before stage = some (input.truthAt sample.2 stage) ∨
        ∃ pair ∈ historyExecutions before, pair.1.stage = stage := by
    intro stage hs
    have heq : stage = head := Fin.ext (by omega)
    subst stage
    left
    have hw := prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hp head
    have hfield : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.written head =
        some (input.truthAt sample.2 head) := by
      rw [hr]
      exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
          (congrArg some hcorrect)
    exact hw.trans hfield
  have hcount : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.reviews head =
      test.rule.stop sample.1 (worldTapes input sample.2 head) := by
    rw [hr, hstop]
    exact bellmanHeadWrittenState_reviews_eq input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hfee := bellmanPrefix_observationBill_of_entry input C accounting policy.val.rule policy.val.legal
    head hhead test sample (n + 2) hentry hcount
  have hviews := bellmanHeadThen_correct_run_view input C hearly hcurrent hdeferred accounting head hhead test available
    repair good bad hbad sample n hstop hcorrect
  have hbound := suffixRun_penaltyCharge_le_prefix_add_child input 1 C hearly accounting policy.val.rule policy.val.legal
    (currentRelaxedContract (I.freshSuffix 1)) (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule good.val.legal
    sample before (n + 2) hobs hbase.written hresolved hviews penalty
  rw [hfee] at hbound
  exact hbound

set_option maxHeartbeats 1200000 in
theorem bellmanHeadThen_wrong_penaltyCharge_le {Seed : Type*} [MeasurableSpace Seed]
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
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head)
    (penalty : ℝ≥0∞) :
    runPenaltyCharge input C .uncapped accounting
      (bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad.val.rule)) penalty sample ≤
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
        runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule penalty
          (sample.1, referenceSuffixWorld input 1 sample.2) := by
  let after := bellmanPostHeadRaw input head (some tool) good bad.val.rule
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad.val.rule hgood bad.val.measurable_rule)
  let before := (run input C .uncapped accounting policy.val.rule sample (n + 4)).history
  have hentry := bellmanHeadThen_wrong_firstEntry input C hearly hcurrent hdeferred accounting head hhead test available
    tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
  have hobs := bellmanEntry_observations_empty input 1 C accounting policy.val.rule policy.val.legal sample (n + 4) hentry
  have hbase := GuardLift.base_of_firstEntry input 1 C hearly accounting policy.val.rule policy.val.legal
    sample (n + 4) hentry available
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let executed := bellmanExecuteState accounting allocated head tool
  let handle : MismatchHandle I := ⟨head, written.ledger.writeSerial head⟩
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 4) =
      record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false :=
    bellmanHeadThen_run_wrong_advance input C hearly hcurrent hdeferred accounting head hhead test available
      tool htool heligible good bad.val.rule hgood bad.val.measurable_rule sample n hstop hwrong
  have hexec : historyExecutions before = [(handle, tool)] := by
    change historyExecutions (run input C .uncapped accounting policy.val.rule sample (n + 4)).history = _
    rw [hr]
    exact (bellmanRepairedEntry_history_corrections input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)) tool).2
  have hresolved : ∀ stage : I.Stage, stage.val < 1 →
      historyWritten before stage = some (input.truthAt sample.2 stage) ∨
        ∃ pair ∈ historyExecutions before, pair.1.stage = stage := by
    intro stage hs
    have heq : stage = head := Fin.ext (by omega)
    subst stage
    right
    refine ⟨(handle, tool), ?_, rfl⟩
    rw [hexec]
    exact List.mem_singleton_self (handle, tool)
  have hcount : (run input C .uncapped accounting policy.val.rule sample (n + 4)).ledger.reviews head =
      test.rule.stop sample.1 (worldTapes input sample.2 head) := by
    rw [hr, hstop]
    change written.ledger.reviews head = n
    exact bellmanHeadWrittenState_reviews_eq input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hfee := bellmanPrefix_observationBill_of_entry input C accounting policy.val.rule policy.val.legal
    head hhead test sample (n + 4) hentry hcount
  have hviews := bellmanHeadThen_wrong_run_view input C hearly hcurrent hdeferred accounting head hhead test available
    tool htool heligible good hgood bad sample n hstop hwrong
  have hbound := suffixRun_penaltyCharge_le_prefix_add_child input 1 C hearly accounting policy.val.rule policy.val.legal
    (currentRelaxedContract (I.freshSuffix 1)) (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule bad.val.legal
    sample before (n + 4) hobs hbase.written hresolved hviews penalty
  rw [hfee] at hbound
  exact hbound

theorem bellmanHeadReviewState_reviews_other (input : StatisticalInput I)
    (accounting : NormalAccounting I) (head stage : I.Stage) (hne : stage ≠ head)
    (truth : I.Stage → Bool) (tape : (input.experiment head).Tape) (n : ℕ) :
    (headReviewState input accounting head truth tape n).ledger.reviews stage = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simpa only [headReviewState, record, reviewLedger, Function.update_of_ne hne] using ih

theorem bellmanHeadReviewState_observationBill (input : StatisticalInput I)
    (accounting : NormalAccounting I) (head : I.Stage) (truth : I.Stage → Bool)
    (tape : (input.experiment head).Tape) (n : ℕ) :
    (headReviewState input accounting head truth tape n).ledger.observationBill input.fees =
      (input.experiment head).observationCharge n := by
  classical
  unfold Ledger.observationBill
  rw [Finset.sum_eq_single head]
  · rw [headReviewState_reviews, ENat.toENNReal_coe, Statistics.BinaryExperiment.observationCharge_nat]
    rfl
  · intro stage _ hne
    rw [bellmanHeadReviewState_reviews_other input accounting head stage hne, ENat.toENNReal_zero, mul_zero]
  · intro hcontra
    exact (hcontra (Finset.mem_univ head)).elim

theorem bellmanRun_not_success_of_abandoned_halt {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed) (sample : Seed × input.World)
    (n : ℕ) (hhalt : (run input C mode accounting rule sample n).halted = true)
    (habandon : (run input C mode accounting rule sample n).ledger.abandoned = true) :
    ¬runSuccess input C mode accounting rule sample := by
  rintro ⟨k, hk, hs⟩
  have heq : run input C mode accounting rule sample k = run input C mode accounting rule sample n := by
    by_cases hkn : k ≤ n
    · obtain ⟨extra, hextra⟩ := Nat.exists_eq_add_of_le hkn
      have hx := run_after_halt input C mode accounting rule sample k hk extra
      rw [← hextra] at hx
      exact hx.symm
    · obtain ⟨extra, rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_ge hkn)
      exact run_after_halt input C mode accounting rule sample n hhalt extra
  rw [heq] at hs
  have hf := hs.2.1
  rw [habandon] at hf
  cases hf

set_option maxHeartbeats 1200000 in
theorem bellmanHeadThen_wrong_noTool_penaltyCharge_eq {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head)
    (penalty : ℝ≥0∞) :
    runPenaltyCharge input C .uncapped accounting
      (bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head none good bad)) penalty sample =
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) + penalty := by
  classical
  let after := bellmanPostHeadRaw input head none good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head none good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 2) = stopState written true :=
    bellmanHeadThen_run_wrong_noTool input C hearly hcurrent hdeferred accounting head hhead test available
      good bad hgood hbad sample n hstop hwrong
  have hhalt : (run input C .uncapped accounting policy.val.rule sample (n + 2)).halted = true := by
    rw [hr]
    rfl
  have habandon : (run input C .uncapped accounting policy.val.rule sample (n + 2)).ledger.abandoned = true := by
    rw [hr]
    rfl
  have hfailure := bellmanRun_not_success_of_abandoned_halt input C .uncapped accounting policy.val.rule
    sample (n + 2) hhalt habandon
  have hbill : runObservationBill input C .uncapped accounting policy.val.rule sample =
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) := by
    rw [runObservationBill_eq_prefix_add_future input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 2),
      futureObservationBill_of_halted input C .uncapped accounting policy.val.rule sample (n + 2) hhalt, add_zero, hr, hstop]
    simpa only [stopState, written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly,
      ↓reduceIte, writeLedger, Ledger.observationBill] using
      bellmanHeadReviewState_observationBill input accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n
  change runObservationBill input C .uncapped accounting policy.val.rule sample +
    (if runSuccess input C .uncapped accounting policy.val.rule sample then 0 else penalty) = _
  rw [hbill, ite_eq_right hfailure]

theorem bellmanHeadThen_someTool_penaltyCharge_le {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Seed)
    (bad : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) (available.erase tool) Seed)
    (sample : Seed × input.World) (penalty : ℝ≥0∞) :
    runPenaltyCharge input C .uncapped accounting
      (bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good.val.rule bad.val.rule)) penalty sample ≤
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
        (if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
          runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
            (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule penalty
            (sample.1, referenceSuffixWorld input 1 sample.2)
        else runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
          (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule penalty
          (sample.1, referenceSuffixWorld input 1 sample.2)) := by
  classical
  by_cases htop : test.rule.stop sample.1 (worldTapes input sample.2 head) = ⊤
  · simp only [htop, Statistics.BinaryExperiment.observationCharge_top, top_add, le_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  by_cases hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
  · rw [ite_eq_left hcorrect]
    exact bellmanHeadThen_correct_penaltyCharge_le input C hearly hcurrent hdeferred accounting head hhead test available
      (some tool) good bad.val.rule bad.val.measurable_rule sample n hn.symm hcorrect penalty
  · rw [ite_eq_right hcorrect]
    exact bellmanHeadThen_wrong_penaltyCharge_le input C hearly hcurrent hdeferred accounting head hhead test available
      tool htool heligible good.val.rule good.val.measurable_rule bad sample n hn.symm hcorrect penalty

theorem bellmanHeadThen_noTool_penaltyCharge_le {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Seed)
    (bad : PolicyRule (I.freshSuffix 1) Seed) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (penalty : ℝ≥0∞) :
    runPenaltyCharge input C .uncapped accounting
      (bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head none good.val.rule bad)) penalty sample ≤
      (input.experiment head).observationCharge (test.rule.stop sample.1 (worldTapes input sample.2 head)) +
        (if test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
          runPenaltyCharge (input.freshSuffix 1) (currentRelaxedContract (I.freshSuffix 1)) .uncapped
            (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule penalty
            (sample.1, referenceSuffixWorld input 1 sample.2)
        else penalty) := by
  classical
  by_cases htop : test.rule.stop sample.1 (worldTapes input sample.2 head) = ⊤
  · simp only [htop, Statistics.BinaryExperiment.observationCharge_top, top_add, le_top]
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp htop
  by_cases hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head
  · rw [ite_eq_left hcorrect]
    exact bellmanHeadThen_correct_penaltyCharge_le input C hearly hcurrent hdeferred accounting head hhead test available
      none good bad hbad sample n hn.symm hcorrect penalty
  · rw [ite_eq_right hcorrect]
    exact (bellmanHeadThen_wrong_noTool_penaltyCharge_eq input C hearly hcurrent hdeferred accounting head hhead test available
      good.val.rule bad good.val.measurable_rule hbad sample n hn.symm hcorrect penalty).le

end PaperProofs.Common.Native
