module

public import PaperProofs.Common.NativeBellmanUpper
public import PaperProofs.Common.NativeSuffixRunLift
public import Mathlib.Data.List.Basic

/-! Public-history identification for the actual two-continuation Bellman
controller. These are finite history facts, not assumptions on value or risk. -/

@[expose] public section

namespace PaperProofs.Common.Native

variable {I : Instance}

theorem freshStageLift_ne_earlier (first : ℕ) (head : I.Stage) (hhead : head.val < first)
    (stage : (I.freshSuffix first).Stage) : I.freshStageLift first stage ≠ head := by
  intro heq
  have hval := congrArg Fin.val heq
  change first + stage.val = head.val at hval
  omega

theorem historyWrite_referenceSuffixJoin_earlier (first : ℕ) (head : I.Stage)
    (hhead : head.val < first) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) :
    historyWrite (referenceSuffixHistoryJoin I first before after) head = historyWrite before head := by
  have hn : (referenceSuffixHistoryLift I first (historyActions before).length after).filterMap (eventWrite head) = [] := by
    induction after with
    | nil => rfl
    | cons event rest ih =>
      cases event <;> simp_all only [referenceSuffixHistoryLift, List.map_cons, List.filterMap_cons,
        referenceSuffixEventLift, eventWrite, freshStageLift_ne_earlier first head hhead, ↓reduceIte]
  simp only [historyWrite, referenceSuffixHistoryJoin, List.filterMap_append, hn, List.append_nil]

theorem historyReport_referenceSuffixJoin_earlier (first : ℕ) (head : I.Stage)
    (hhead : head.val < first) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) :
    historyReport (referenceSuffixHistoryJoin I first before after) head = historyReport before head := by
  have hn : (referenceSuffixHistoryLift I first (historyActions before).length after).filterMap (eventReport head) = [] := by
    induction after with
    | nil => rfl
    | cons event rest ih =>
      cases event <;> simp_all only [referenceSuffixHistoryLift, List.map_cons, List.filterMap_cons,
        referenceSuffixEventLift, eventReport, freshStageLift_ne_earlier first head hhead, ↓reduceIte]
  simp only [historyReport, referenceSuffixHistoryJoin, List.filterMap_append, hn, List.append_nil]

theorem historyWritten_referenceSuffixJoin_earlier (first : ℕ) (head : I.Stage)
    (hhead : head.val < first) (before : List (VisibleEvent I))
    (after : List (VisibleEvent (I.freshSuffix first))) :
    historyWritten (referenceSuffixHistoryJoin I first before after) head = historyWritten before head := by
  simp only [historyWritten, historyWrite_referenceSuffixJoin_earlier first head hhead]

theorem bellmanHeadCut_join (head : I.Stage) (pre : List (VisibleEvent I))
    (hn : VisibleEvent.advanced head ∉ pre) (after : List (VisibleEvent (I.freshSuffix 1))) :
    let before := pre ++ [.advanced head]
    let joined := referenceSuffixHistoryJoin I 1 before after
    joined.take (joined.idxOf (.advanced head) + 1) = before := by
  dsimp only
  have hm : VisibleEvent.advanced head ∈ pre ++ [.advanced head] := by simp
  rw [referenceSuffixHistoryJoin, List.idxOf_append_of_mem hm,
    List.idxOf_append_of_notMem hn]
  simp only [List.idxOf_cons_self, Nat.add_zero]
  have hlen : pre.length + 1 = (pre ++ [VisibleEvent.advanced head]).length := by simp
  rw [hlen]
  exact List.take_left

theorem bellmanPostHeadRaw_good_join {Seed : Type*} (input : StatisticalInput I)
    (head : I.Stage) (hhead : head.val = 0) (repair : Option I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed) (seed : Seed)
    (pre : List (VisibleEvent I)) (hnoAdvance : VisibleEvent.advanced head ∉ pre)
    (hcursor : historyCursor (pre ++ [.advanced head]) = 1)
    (hchoice : historyWritten (pre ++ [.advanced head]) head =
      (historyReport (pre ++ [.advanced head]) head).map Prod.fst)
    (after : List (VisibleEvent (I.freshSuffix 1))) :
    bellmanPostHeadRaw input head repair good bad seed
      (referenceSuffixHistoryJoin I 1 (pre ++ [.advanced head]) after) =
      referenceSuffixActionLift I 1 (historyActions (pre ++ [.advanced head])).length (good seed after) := by
  have hearly : head.val < 1 := by omega
  have hc : historyCursor (referenceSuffixHistoryJoin I 1 (pre ++ [.advanced head]) after) ≠ 0 := by
    rw [historyCursor_referenceSuffixJoin, hcursor]
    omega
  simp only [bellmanPostHeadRaw, hc, ↓reduceIte,
    bellmanHeadCut_join head pre hnoAdvance after,
    historyWritten_referenceSuffixJoin_earlier 1 head hearly,
    historyReport_referenceSuffixJoin_earlier 1 head hearly, hchoice, ↓reduceIte]
  exact bellmanLiftedAfter_join 1 (pre ++ [.advanced head]) good seed after

theorem bellmanPostHeadRaw_bad_join {Seed : Type*} (input : StatisticalInput I)
    (head : I.Stage) (hhead : head.val = 0) (repair : Option I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed) (seed : Seed)
    (pre : List (VisibleEvent I)) (hnoAdvance : VisibleEvent.advanced head ∉ pre)
    (hcursor : historyCursor (pre ++ [.advanced head]) = 1)
    (hchoice : historyWritten (pre ++ [.advanced head]) head ≠
      (historyReport (pre ++ [.advanced head]) head).map Prod.fst)
    (after : List (VisibleEvent (I.freshSuffix 1))) :
    bellmanPostHeadRaw input head repair good bad seed
      (referenceSuffixHistoryJoin I 1 (pre ++ [.advanced head]) after) =
      referenceSuffixActionLift I 1 (historyActions (pre ++ [.advanced head])).length (bad seed after) := by
  have hearly : head.val < 1 := by omega
  have hc : historyCursor (referenceSuffixHistoryJoin I 1 (pre ++ [.advanced head]) after) ≠ 0 := by
    rw [historyCursor_referenceSuffixJoin, hcursor]
    omega
  simp only [bellmanPostHeadRaw, hc, ↓reduceIte,
    bellmanHeadCut_join head pre hnoAdvance after,
    historyWritten_referenceSuffixJoin_earlier 1 head hearly,
    historyReport_referenceSuffixJoin_earlier 1 head hearly, hchoice, ↓reduceIte]
  exact bellmanLiftedAfter_join 1 (pre ++ [.advanced head]) bad seed after

theorem not_mem_advanced_of_historyCursor_zero (history : List (VisibleEvent I))
    (hcursor : historyCursor history = 0) (head : I.Stage) :
    VisibleEvent.advanced head ∉ history := by
  intro hm
  have hz : history.filterMap eventAdvance = [] := List.eq_nil_of_length_eq_zero hcursor
  have he : head ∈ history.filterMap eventAdvance :=
    List.mem_filterMap.mpr ⟨.advanced head, hm, rfl⟩
  rw [hz] at he
  cases he

theorem historyCursor_append_head_advance (history : List (VisibleEvent I)) (head : I.Stage) :
    historyCursor (history ++ [.advanced head]) = historyCursor history + 1 := by
  simp only [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance,
    List.filterMap_nil, List.length_append, List.length_cons, List.length_nil]

theorem historyWrite_append_head_advance (history : List (VisibleEvent I)) (head : I.Stage) :
    historyWrite (history ++ [.advanced head]) head = historyWrite history head := by
  simp only [historyWrite, List.filterMap_append, List.filterMap_cons, eventWrite,
    List.filterMap_nil, List.append_nil]

theorem historyWritten_append_head_advance (history : List (VisibleEvent I)) (head : I.Stage) :
    historyWritten (history ++ [.advanced head]) head = historyWritten history head := by
  simp only [historyWritten, historyWrite_append_head_advance]

theorem historyReport_append_head_advance (history : List (VisibleEvent I)) (head : I.Stage) :
    historyReport (history ++ [.advanced head]) head = historyReport history head := by
  simp only [historyReport, List.filterMap_append, List.filterMap_cons, eventReport,
    List.filterMap_nil, List.append_nil]

/-- All selector and prefix-cut facts are recovered from a real correct
head prefix; no raw action equality is assumed. -/
theorem bellmanPostHeadRaw_good_join_of_prefix {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {m : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes m s)
    (head : I.Stage) (hhead : head.val = 0) (repair : Option I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hcursor : s.cursor = 0) (hwritten : s.ledger.written head = some (s.ledger.truth head))
    (hreported : ∃ clock, s.ledger.reportTime head = some clock)
    (after : List (VisibleEvent (I.freshSuffix 1))) :
    bellmanPostHeadRaw input head repair good bad seed
      (referenceSuffixHistoryJoin I 1 (s.history ++ [.advanced head]) after) =
      referenceSuffixActionLift I 1 (historyActions (s.history ++ [.advanced head])).length (good seed after) := by
  have hc : historyCursor s.history = 0 :=
    (prefix_historyCursor input C mode accounting rule seed truth tapes hp).trans hcursor
  apply bellmanPostHeadRaw_good_join input head hhead repair good bad seed s.history
    (not_mem_advanced_of_historyCursor_zero s.history hc head)
  · rw [historyCursor_append_head_advance, hc]
  · obtain ⟨clock, ht⟩ := hreported
    rw [historyWritten_append_head_advance, historyReport_append_head_advance,
      prefix_historyWritten input C mode accounting rule seed truth tapes hp head,
      prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp head,
      hwritten, ht]
    rfl

/-- The same real-prefix derivation selects the wrong/repaired child. -/
theorem bellmanPostHeadRaw_bad_join_of_prefix {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {m : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes m s)
    (head : I.Stage) (hhead : head.val = 0) (repair : Option I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hcursor : s.cursor = 0) (hwritten : s.ledger.written head = some (!s.ledger.truth head))
    (hreported : ∃ clock, s.ledger.reportTime head = some clock)
    (after : List (VisibleEvent (I.freshSuffix 1))) :
    bellmanPostHeadRaw input head repair good bad seed
      (referenceSuffixHistoryJoin I 1 (s.history ++ [.advanced head]) after) =
      referenceSuffixActionLift I 1 (historyActions (s.history ++ [.advanced head])).length (bad seed after) := by
  have hc : historyCursor s.history = 0 :=
    (prefix_historyCursor input C mode accounting rule seed truth tapes hp).trans hcursor
  apply bellmanPostHeadRaw_bad_join input head hhead repair good bad seed s.history
    (not_mem_advanced_of_historyCursor_zero s.history hc head)
  · rw [historyCursor_append_head_advance, hc]
  · obtain ⟨clock, ht⟩ := hreported
    rw [historyWritten_append_head_advance, historyReport_append_head_advance,
      prefix_historyWritten input C mode accounting rule seed truth tapes hp head,
      prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp head,
      hwritten, ht]
    cases s.ledger.truth head <;> simp

/-- A real first-head prefix has not touched any future suffix port.
The final head-advance response changes none of these future queries. -/
theorem bellmanEntry_future_clean_of_prefix {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (mode : ResourceMode)
    (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {m : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes m s)
    (head : I.Stage) (hcursor : s.cursor = 0) (stage : (I.freshSuffix 1).Stage) :
    historyObservations (s.history ++ [.advanced head]) (I.freshStageLift 1 stage) = [] ∧
      historyWrite (s.history ++ [.advanced head]) (I.freshStageLift 1 stage) = none ∧
      historyReport (s.history ++ [.advanced head]) (I.freshStageLift 1 stage) = none := by
  let target := I.freshStageLift 1 stage
  have hfuture : s.cursor < target.val := by change s.cursor < 1 + stage.val; omega
  have hclean := prefix_future_port_clean input C mode accounting rule seed truth tapes hp target hfuture
  have hr := (prefix_cursorInvariant input C mode accounting rule seed truth tapes hp).future_reviews target hfuture
  have hlength := prefix_historyObservations_length_toNat input C mode accounting rule seed truth tapes hp target
  rw [hr, ENat.toNat_zero] at hlength
  have hobs : historyObservations s.history target = [] := List.eq_nil_of_length_eq_zero hlength
  have hw := prefix_historyWrite input C mode accounting rule seed truth tapes hp target
  rw [hclean.1] at hw
  have hreport := prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp target
  rw [hclean.2.1] at hreport
  simpa only [historyObservations, historyWrite, historyReport, List.filterMap_append,
    List.filterMap_cons, eventObservation, eventWrite, eventReport, List.filterMap_nil,
    List.append_nil] using (show historyObservations s.history target = [] ∧
      historyWrite s.history target = none ∧ historyReport s.history target = none from
    ⟨hobs, hw, hreport⟩)

/-- All old commitments and executions in a first-head prefix belong to
the head. This follows from genuine written ports and causal cleanliness,
not from a successful-path or controller-performance assumption. -/
theorem bellmanEntry_old_corrections_of_prefix {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    {m : ℕ} {s : State I} (hp : Prefix input C mode accounting rule seed truth tapes m s)
    (head : I.Stage) (hcursor : s.cursor = 0) :
    (∀ pair ∈ historyCommitments (s.history ++ [.advanced head]), pair.1.stage.val < 1) ∧
      (∀ pair ∈ historyExecutions (s.history ++ [.advanced head]), pair.1.stage.val < 1) := by
  have hframe : historyCommitments (s.history ++ [.advanced head]) = historyCommitments s.history ∧
      historyExecutions (s.history ++ [.advanced head]) = historyExecutions s.history := by
    simp only [historyCommitments, historyExecutions, List.filterMap_append, List.filterMap_cons,
      eventCommitment, eventExecution, List.filterMap_nil, List.append_nil, and_self]
  have hinv := prefix_invariant input C mode accounting rule seed truth tapes hp
  have hcausal := prefix_cursorInvariant input C mode accounting rule seed truth tapes hp
  constructor
  · intro pair hm
    rw [hframe.1, prefix_historyCommitments input C mode accounting rule seed truth tapes hp] at hm
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hm
    by_contra hn
    change ¬ a.handle.stage.val < 1 at hn
    have hf : s.cursor < a.handle.stage.val := by omega
    have hg := (hinv.commitment_genuine a ha).1
    rw [hcausal.future_written a.handle.stage hf] at hg
    cases hg
  · intro pair hm
    rw [hframe.2, prefix_historyExecutions input C mode accounting rule seed truth tapes hp] at hm
    obtain ⟨e, he, rfl⟩ := List.mem_map.mp hm
    by_contra hn
    change ¬ e.handle.stage.val < 1 at hn
    have hf : s.cursor < e.handle.stage.val := by omega
    have hg := (hinv.wellFormed.genuine e he).1
    rw [hcausal.future_written e.handle.stage hf] at hg
    cases hg

theorem headReviewHistory_empty_corrections (input : StatisticalInput I) (head : I.Stage)
    (tape : (input.experiment head).Tape) (n : ℕ) :
    historyCommitments (headReviewHistory input head tape n) = [] ∧
      historyExecutions (headReviewHistory input head tape n) = [] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih =>
    simpa only [headReviewHistory_succ, historyCommitments, historyExecutions, List.filterMap_append,
      List.filterMap_cons, eventCommitment, eventExecution, List.filterMap_nil, List.append_nil] using ih

theorem bellmanHeadWrittenState_history_corrections (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (head : I.Stage)
    (truth : I.Stage → Bool) (tape : (input.experiment head).Tape) (n : ℕ) (bit : Bool) :
    historyCommitments (bellmanHeadWrittenState input C accounting head truth tape n bit).history = [] ∧
      historyExecutions (bellmanHeadWrittenState input C accounting head truth tape n bit).history = [] := by
  simpa only [bellmanHeadWrittenState, record, writeResponses, hearly, ↓reduceIte,
    headReviewState_history, historyCommitments, historyExecutions, List.filterMap_append,
    List.filterMap_cons, eventCommitment, eventExecution, List.filterMap_nil, List.append_nil] using
    headReviewHistory_empty_corrections input head tape n

/-- The complete repaired head prefix contains precisely the selected old
tool in both correction logs; no suffix tool or obligation is hidden here. -/
theorem bellmanRepairedEntry_history_corrections (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (head : I.Stage)
    (truth : I.Stage → Bool) (tape : (input.experiment head).Tape) (n : ℕ) (bit : Bool)
    (tool : I.Tool) :
    let written := bellmanHeadWrittenState input C accounting head truth tape n bit
    let allocated := bellmanAllocateState accounting written head tool
    let executed := bellmanExecuteState accounting allocated head tool
    let before := (record accounting executed (.advance head) [.advanced head]
      (advanceLedger executed head) 1 false).history
    let handle : MismatchHandle I := ⟨head, written.ledger.writeSerial head⟩
    historyCommitments before = [(handle, tool)] ∧ historyExecutions before = [(handle, tool)] := by
  dsimp only
  have he := bellmanHeadWrittenState_history_corrections input C hearly accounting head truth tape n bit
  simpa only [bellmanExecuteState, bellmanAllocateState, record, allocateLedger,
    historyCommitments, historyExecutions, List.filterMap_append, List.filterMap_cons,
    eventCommitment, eventExecution, List.filterMap_nil, List.append_nil, List.nil_append] using
    (show historyCommitments (bellmanHeadWrittenState input C accounting head truth tape n bit).history ++
          [(⟨head, (bellmanHeadWrittenState input C accounting head truth tape n bit).ledger.writeSerial head⟩, tool)] =
          [(⟨head, (bellmanHeadWrittenState input C accounting head truth tape n bit).ledger.writeSerial head⟩, tool)] ∧
        historyExecutions (bellmanHeadWrittenState input C accounting head truth tape n bit).history ++
          [(⟨head, (bellmanHeadWrittenState input C accounting head truth tape n bit).ledger.writeSerial head⟩, tool)] =
          [(⟨head, (bellmanHeadWrittenState input C accounting head truth tape n bit).ledger.writeSerial head⟩, tool)] from by
      rw [he.1, he.2]
      exact ⟨rfl, rfl⟩)

theorem bellmanPostHeadRaw_correct_actual_join {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head)
    (afterHistory : List (VisibleEvent (I.freshSuffix 1))) :
    let rule := bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head repair good bad)
    let before := (run input C .uncapped accounting rule sample (n + 2)).history
    bellmanPostHeadRaw input head repair good bad sample.1
      (referenceSuffixHistoryJoin I 1 before afterHistory) =
      referenceSuffixActionLift I 1 (historyActions before).length (good sample.1 afterHistory) := by
  let after := bellmanPostHeadRaw input head repair good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 1) = written :=
    bellmanHeadThen_run_write input C accounting head hhead test available after sample n hstop
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 1)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head
    (input.truthAt sample.2) (worldTapes input sample.2 head) n
    (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : written.ledger.written head = some (written.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n _).trans (congrArg some hcorrect)
  have hreport : ∃ clock, written.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have hjoin := bellmanPostHeadRaw_good_join_of_prefix input C hearly .uncapped accounting policy.val.rule
    sample.1 _ _ hp head hhead repair good bad hc hw hreport afterHistory
  dsimp only
  rw [bellmanHeadThen_run_correct_advance input C hearly hcurrent hdeferred accounting head hhead test available
    repair good bad hgood hbad sample n hstop hcorrect]
  exact hjoin

set_option maxHeartbeats 800000 in
theorem bellmanPostHeadRaw_wrong_actual_join {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head)
    (afterHistory : List (VisibleEvent (I.freshSuffix 1))) :
    let rule := bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad)
    let before := (run input C .uncapped accounting rule sample (n + 4)).history
    bellmanPostHeadRaw input head (some tool) good bad sample.1
      (referenceSuffixHistoryJoin I 1 before afterHistory) =
      referenceSuffixActionLift I 1 (historyActions before).length (bad sample.1 afterHistory) := by
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let executed := bellmanExecuteState accounting allocated head tool
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 3) = executed :=
    bellmanHeadThen_run_wrong_execute input C hearly hcurrent hdeferred accounting head hhead test available
      tool htool heligible good bad hgood hbad sample n hstop hwrong
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 3)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : executed.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head
    (input.truthAt sample.2) (worldTapes input sample.2 head) n
    (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : executed.ledger.written head = some (!executed.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n _).trans (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, executed.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [executed, bellmanExecuteState, executeLedger, allocated, bellmanAllocateState, allocateLedger,
      written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have hjoin := bellmanPostHeadRaw_bad_join_of_prefix input C hearly .uncapped accounting policy.val.rule
    sample.1 _ _ hp head hhead (some tool) good bad hc hw hreport afterHistory
  dsimp only
  rw [bellmanHeadThen_run_wrong_advance input C hearly hcurrent hdeferred accounting head hhead test available
    tool htool heligible good bad hgood hbad sample n hstop hwrong]
  exact hjoin

/-- One actual cursor step from zero to one is the first entry, by the
already-proved native cursor monotonicity. No time-by-time classification
or freshness premise is required. -/
theorem bellman_firstEntryAt_of_zero_to_one {Seed : Type*} (input : StatisticalInput I)
    (C : Contract I) (mode : ResourceMode) (accounting : NormalAccounting I)
    (rule : PolicyRule I Seed) (hlegal : LegalRule input C mode accounting rule)
    (sample : Seed × input.World) (n : ℕ)
    (hbefore : (run input C mode accounting rule sample n).cursor = 0)
    (hafter : (run input C mode accounting rule sample (n + 1)).cursor = 1) :
    FirstEntryAt input C mode accounting rule 1 (n + 1) sample := by
  refine ⟨hafter, ?_⟩
  intro k hk heq
  have hle : k ≤ n := by omega
  have hc := run_cursor_monotone input C mode accounting rule hlegal sample hle
  change (run input C mode accounting rule sample k).cursor ≤
    (run input C mode accounting rule sample n).cursor at hc
  rw [heq, hbefore] at hc
  omega

end PaperProofs.Common.Native
