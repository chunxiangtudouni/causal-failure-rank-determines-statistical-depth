module

public import PaperProofs.Common.NativeHeadTest
public import PaperProofs.Common.ReferenceSuffixRun
public import PaperProofs.Common.HistorySuffixStep
public import PaperProofs.Common.NativeSuffixRunLift

/-!
Construction components for the ORIGINAL B08 upper inequality. Independent
continuations and local rules are selected from their existing full infima;
no near-optimal strategy oracle is assumed. Local actions read only the actual
private seed and public finite observations, retaining arbitrary non-MAP bits.
The Bellman upper equality itself is not asserted by the components below.
-/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native

open PaperProofs.Statistics PaperProofs.Structure

variable {I : Instance}

/-- Actual epsilon approximation of the original full-policy infimum, including
its private seed space and law. No optimal continuation oracle is supplied. -/
theorem exists_availablePenaltyObjective_near (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (penalty : ℝ≥0∞)
    (hpenalty : penalty ≠ ⊤) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (Seed : Type) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∃ (ν : Measure Seed) (_hν : IsProbabilityMeasure ν)
        (policy : AvailablePolicy input C accounting available Seed),
        penaltyObjective input C .uncapped accounting policy.val.rule ν penalty <
          availablePenaltyValue input C accounting available penalty + ENNReal.ofReal epsilon := by
  have hfinite : availablePenaltyValue input C accounting available penalty ≠ ⊤ := by
    intro ht
    exact hpenalty (top_le_iff.mp (ht ▸ availablePenaltyValue_le_penalty input C accounting available penalty))
  have hpositive : ENNReal.ofReal epsilon ≠ 0 := (ENNReal.ofReal_pos.mpr hepsilon).ne'
  have hnear := ENNReal.lt_add_right hfinite hpositive
  conv_lhs at hnear => unfold availablePenaltyValue
  simpa only [iInf_lt_iff] using hnear

/-- Actual epsilon approximation of the original local infimum, with arbitrary
seed law, non-MAP decisions and infinite-cost competitors retained. -/
theorem exists_localObjective_near (E : BinaryExperiment) (penalty : ℝ≥0∞)
    (hpenalty : penalty ≠ ⊤) (epsilon : ℝ) (hepsilon : 0 < epsilon) :
    ∃ (Seed : Type) (m : MeasurableSpace Seed),
      letI : MeasurableSpace Seed := m
      ∃ (ν : Measure Seed) (_hν : IsProbabilityMeasure ν) (test : E.AdmissibleRule Seed),
        E.bayesObjective ν test penalty < E.localValue penalty + ENNReal.ofReal epsilon := by
  have hpositive : ENNReal.ofReal epsilon ≠ 0 := (ENNReal.ofReal_pos.mpr hepsilon).ne'
  have hnear := ENNReal.lt_add_right (E.localValue_ne_top penalty hpenalty) hpositive
  conv_lhs at hnear => unfold BinaryExperiment.localValue
  simpa only [iInf_lt_iff] using hnear

/-- The bad continuation uses a genuine finite tool minimum, rather than an
oracle. The following policy selection is still from an independent infimum. -/
theorem exists_badPenaltyReal_minimizer (input : StatisticalInput I) (stage : I.Stage)
    (available : Finset I.Tool) (price : ℝ)
    (hnonempty : (I.eligible stage ∩ available).Nonempty) :
    ∃ tool ∈ I.eligible stage ∩ available,
      input.badPenaltyReal stage available price =
        input.healthyPenaltyReal (stage.val + 1) (available.erase tool) price := by
  classical
  obtain ⟨tool, htool, heq⟩ := Finset.exists_mem_eq_inf' hnonempty
    (fun tool => input.healthyPenaltyReal (stage.val + 1) (available.erase tool) price)
  refine ⟨tool, htool, ?_⟩
  simpa only [StatisticalInput.badPenaltyReal, hnonempty, ↓reduceDIte] using heq

/-- Complete only the existing finite observed head word, using the existing
fixed completion symbol beyond it. No future tape or truth enters the policy. -/
noncomputable def bellmanHeadTape (input : StatisticalInput I) (head : I.Stage)
    (history : List (VisibleEvent I)) : (input.experiment head).Tape := fun k =>
  let observations := historyObservations history head
  if hk : k < observations.length then
    if hv : observations[k] < (input.experiment head).alphabetSize then ⟨observations[k], hv⟩
    else (input.experiment head).completionSymbol
  else (input.experiment head).completionSymbol

noncomputable def bellmanHeadNext {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed) :
    PolicyRule I Seed := fun seed history =>
  let tape := bellmanHeadTape input head history
  if test.rule.stop seed tape ≤ (historyObservations history head).length then
    .write head (test.rule.decision seed tape) else .review head

theorem historyObservations_headReviewHistory (input : StatisticalInput I) (head : I.Stage)
    (tape : (input.experiment head).Tape) (n : ℕ) :
    historyObservations (headReviewHistory input head tape n) head =
      List.ofFn (fun k : Fin n => (tape k.val).val) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [headReviewHistory_succ]
    change (headReviewHistory input head tape n ++ [VisibleEvent.observation head (tape n).val]).filterMap
      (eventObservation head) = _
    rw [List.filterMap_append]
    simp only [List.filterMap_cons, eventObservation, ite_true, List.filterMap_nil]
    change historyObservations (headReviewHistory input head tape n) head ++ [(tape n).val] = _
    rw [ih, List.ofFn_succ_last]
    rfl

theorem bellmanHeadTape_headReviewHistory_prefix (input : StatisticalInput I) (head : I.Stage)
    (tape : (input.experiment head).Tape) (n k : ℕ) (hk : k < n) :
    tape k = bellmanHeadTape input head (headReviewHistory input head tape n) k := by
  unfold bellmanHeadTape
  rw [historyObservations_headReviewHistory]
  simp only [List.length_ofFn, hk, ↓reduceDIte, List.getElem_ofFn, (tape k).isLt]

theorem bellmanHeadNext_review {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (seed : Seed) (tape : (input.experiment head).Tape) (n : ℕ)
    (hbefore : (n : ℕ∞) < test.rule.stop seed tape) :
    bellmanHeadNext input head test seed (headReviewHistory input head tape n) = .review head := by
  let completed := bellmanHeadTape input head (headReviewHistory input head tape n)
  have hprefix : ∀ k < n, tape k = completed k := bellmanHeadTape_headReviewHistory_prefix input head tape n
  have hnot : ¬ test.rule.stop seed completed ≤ n := by
    intro hs
    exact (not_le_of_gt hbefore) ((test.rule.stopping seed tape _ n hprefix).mpr hs)
  simp only [bellmanHeadNext, historyObservations_headReviewHistory, List.length_ofFn]
  exact ite_eq_right hnot

theorem bellmanHeadNext_write {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (seed : Seed) (tape : (input.experiment head).Tape) (n : ℕ)
    (hstop : test.rule.stop seed tape = n) :
    bellmanHeadNext input head test seed (headReviewHistory input head tape n) =
      .write head (test.rule.decision seed tape) := by
  let completed := bellmanHeadTape input head (headReviewHistory input head tape n)
  have hprefix : ∀ k < n, tape k = completed k := bellmanHeadTape_headReviewHistory_prefix input head tape n
  have hcompleted := (input.experiment head).stopping_preserved_by_prefix test.rule seed tape
    completed n hstop hprefix
  have hdecision := test.rule.stoppedDecision seed tape completed
    n hstop hcompleted hprefix
  simp only [bellmanHeadNext, historyObservations_headReviewHistory, List.length_ofFn]
  change (if test.rule.stop seed completed ≤ n then Action.write head (test.rule.decision seed completed) else Action.review head) = _
  rw [hcompleted, ite_eq_left le_rfl, ← hdecision]

theorem measurable_bellmanHeadNext {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed) :
    MeasurableRule (bellmanHeadNext input head test) := by
  apply measurable_from_prod_countable_left
  intro history
  let tape := bellmanHeadTape input head history
  have hs : Measurable (fun seed : Seed => test.rule.stop seed tape) :=
    test.measurable_stop.comp (measurable_id.prodMk measurable_const)
  have hd : Measurable (fun seed : Seed => test.rule.decision seed tape) :=
    test.measurable_decision.comp (measurable_id.prodMk measurable_const)
  change Measurable (fun seed : Seed => if test.rule.stop seed tape ≤
    ((historyObservations history head).length : ℕ∞) then Action.write head (test.rule.decision seed tape) else Action.review head)
  have hset : MeasurableSet {seed : Seed | test.rule.stop seed tape ≤ ((historyObservations history head).length : ℕ∞)} :=
    hs (t := Set.Iic ((historyObservations history head).length : ℕ∞)) (Set.to_countable _).measurableSet
  exact Measurable.ite hset
    ((measurable_of_countable (fun bit => Action.write head bit)).comp hd) measurable_const

noncomputable def bellmanHeadThenRaw {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (after : PolicyRule I Seed) : PolicyRule I Seed := fun seed history =>
  if historyWritten history head = none then bellmanHeadNext input head test seed history else after seed history

noncomputable def bellmanHeadThenRule {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) : PolicyRule I Seed :=
  guardedReplayRule available (bellmanHeadThenRaw input head test after)

theorem measurable_bellmanHeadThenRule {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) (hafter : MeasurableRule after) :
    MeasurableRule (bellmanHeadThenRule input head test available after) := by
  apply measurable_guardedReplayRule
  apply measurable_from_prod_countable_left
  intro history
  dsimp only [bellmanHeadThenRaw]
  split_ifs
  · exact (measurable_bellmanHeadNext input head test).comp (measurable_id.prodMk measurable_const)
  · exact hafter.comp (measurable_id.prodMk measurable_const)

/-- A genuine legal available-tool policy with an arbitrary measurable next
controller. Public guards prove legality on ALL actual paths; the head-test
realization below proves they do not alter the intended test prefix. -/
noncomputable def bellmanHeadThenPolicy {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hdeferred : C.execution = .terminalBarrier) (accounting : NormalAccounting I)
    (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) (hafter : MeasurableRule after) :
    AvailablePolicy input C accounting available Seed :=
  ⟨{rule := bellmanHeadThenRule input head test available after
    measurable_rule := measurable_bellmanHeadThenRule input head test available after hafter
    legal := guardedReplayRule_legal input C hearly hdeferred accounting available _},
    guardedReplayRule_usesOnly input C accounting available _⟩

theorem historyCursor_headReviewHistory (input : StatisticalInput I) (head : I.Stage)
    (tape : (input.experiment head).Tape) (n : ℕ) :
    historyCursor (headReviewHistory input head tape n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [headReviewHistory_succ]
    simpa only [historyCursor, List.filterMap_append, List.filterMap_cons, eventAdvance,
      List.filterMap_nil, List.append_nil] using ih

theorem historyWritten_headReviewHistory (input : StatisticalInput I) (head : I.Stage)
    (tape : (input.experiment head).Tape) (n : ℕ) :
    historyWritten (headReviewHistory input head tape n) head = none := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [headReviewHistory_succ]
    simpa only [historyWritten, historyWrite, List.filterMap_append, List.filterMap_cons, eventWrite,
      List.filterMap_nil, List.append_nil] using ih

theorem bellmanHeadThenRule_headReviewHistory {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (after : PolicyRule I Seed) (seed : Seed) (tape : (input.experiment head).Tape) (n : ℕ) :
    bellmanHeadThenRule input head test available after seed (headReviewHistory input head tape n) =
      bellmanHeadNext input head test seed (headReviewHistory input head tape n) := by
  have hc := historyCursor_headReviewHistory input head tape n
  have hw := historyWritten_headReviewHistory input head tape n
  simp only [bellmanHeadThenRule, guardedReplayRule, bellmanHeadThenRaw, hw, ite_true]
  apply ite_eq_left
  unfold bellmanHeadNext
  dsimp only
  split_ifs <;> exact ⟨hc.trans hhead.symm, hw⟩

/-- The original local test's review prefixes are ACTUAL interpreter states,
not merely a decoded stopping label. This includes every finite prefix of an
infinite test and arbitrary non-MAP decisions. -/
theorem bellmanHeadThen_run_before {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (head : I.Stage) (hhead : head.val = 0) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) (sample : Seed × input.World) (n : ℕ)
    (hbound : (n : ℕ∞) ≤ test.rule.stop sample.1 (worldTapes input sample.2 head)) :
    run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample n =
      headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hnsucc : (n : ℕ∞) ≤ (n + 1 : ℕ∞) := by exact_mod_cast Nat.le_succ n
    have hn := hnsucc.trans hbound
    have hr := ih hn
    have hbefore : (n : ℕ∞) < test.rule.stop sample.1 (worldTapes input sample.2 head) :=
      lt_of_lt_of_le (by exact_mod_cast Nat.lt_succ_self n) hbound
    let s := headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n
    have ha : s.halted = false := headReviewState_active input accounting head _ _ n
    have hl : liveStage s head := ⟨ha, (headReviewState_cursor input accounting head _ _ n).trans hhead.symm⟩
    have hw : s.ledger.written head = none := congrFun (headReviewState_written input accounting head _ _ n) head
    have hc : s.ledger.reviews head = n := headReviewState_reviews input accounting head _ _ n
    have hcursor : s.cursor = 0 := headReviewState_cursor input accounting head _ _ n
    have hs : Step input C .uncapped accounting (worldTapes input sample.2) s (.review head)
        (headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) (n + 1)) := by
      have h := Step.review (input := input) (C := C) (mode := .uncapped) (accounting := accounting)
        (tapes := worldTapes input sample.2) s head hl hw (.inl rfl)
      rw [headReviewState]
      simpa only [hc, ENat.toNat_natCast, hcursor] using h
    apply run_succ_of_step input C .uncapped accounting _ sample n _
    · rw [hr]
      exact ha
    · rw [hr, headReviewState_history, bellmanHeadThenRule_headReviewHistory input head hhead,
        bellmanHeadNext_review input head test sample.1 _ n hbefore]
      exact hs

/-- Public inverse of the existing stage/serial lift. The serial subtraction
uses only the already-visible head action count. -/
def bellmanSuffixHandleLower (first clock : ℕ) (handle : MismatchHandle I)
    (hf : first ≤ handle.stage.val) : MismatchHandle (I.freshSuffix first) :=
  ⟨suffixStageOf first handle.stage hf, handle.writeSerial - clock⟩

def bellmanSuffixEventLower (first clock : ℕ) :
    VisibleEvent I → Option (VisibleEvent (I.freshSuffix first))
  | .observation stage symbol => if h : first ≤ stage.val then some (.observation (suffixStageOf first stage h) symbol) else none
  | .wrote stage bit serial => if h : first ≤ stage.val then some (.wrote (suffixStageOf first stage h) bit (serial - clock)) else none
  | .report stage truth serial => if h : first ≤ stage.val then some (.report (suffixStageOf first stage h) truth (serial - clock)) else none
  | .committed handle tool => if h : first ≤ handle.stage.val then some (.committed (bellmanSuffixHandleLower first clock handle h) tool) else none
  | .executed handle tool => if h : first ≤ handle.stage.val then some (.executed (bellmanSuffixHandleLower first clock handle h) tool) else none
  | .advanced stage => if h : first ≤ stage.val then some (.advanced (suffixStageOf first stage h)) else none
  | .stopped => some .stopped
  | .abandoned => some .abandoned

def bellmanSuffixHistoryLower (first clock : ℕ) (history : List (VisibleEvent I)) :
    List (VisibleEvent (I.freshSuffix first)) := history.filterMap (bellmanSuffixEventLower first clock)

theorem bellmanSuffixEventLower_lift (first clock : ℕ) (event : VisibleEvent (I.freshSuffix first)) :
    bellmanSuffixEventLower first clock (referenceSuffixEventLift I first clock event) = some event := by
  have hstage (stage : (I.freshSuffix first).Stage) : first ≤ (I.freshStageLift first stage).val := by
    change first ≤ first + stage.val
    omega
  cases event <;> simp [referenceSuffixEventLift, referenceSuffixHandleLift, bellmanSuffixEventLower,
    bellmanSuffixHandleLower, hstage, suffixStageOf_freshStageLift]

theorem bellmanSuffixHistoryLower_lift (first clock : ℕ) (history : List (VisibleEvent (I.freshSuffix first))) :
    bellmanSuffixHistoryLower first clock (referenceSuffixHistoryLift I first clock history) = history := by
  induction history with
  | nil => rfl
  | cons event history ih =>
    simp only [referenceSuffixHistoryLift, List.map_cons, bellmanSuffixHistoryLower, List.filterMap_cons,
      bellmanSuffixEventLower_lift] at ih ⊢
    exact congrArg (event :: ·) ih

/-- The actual fresh-child action is lifted from decoded public suffix history.
The head prefix is a public value supplied by the runtime history split. -/
def bellmanLiftedAfter {Seed : Type*} (first : ℕ) (before : List (VisibleEvent I))
    (child : PolicyRule (I.freshSuffix first) Seed) : PolicyRule I Seed := fun seed history =>
  referenceSuffixActionLift I first (historyActions before).length
    (child seed (bellmanSuffixHistoryLower first (historyActions before).length (history.drop before.length)))

theorem bellmanLiftedAfter_join {Seed : Type*} (first : ℕ) (before : List (VisibleEvent I))
    (child : PolicyRule (I.freshSuffix first) Seed) (seed : Seed)
    (history : List (VisibleEvent (I.freshSuffix first))) :
    bellmanLiftedAfter first before child seed (referenceSuffixHistoryJoin I first before history) =
      referenceSuffixActionLift I first (historyActions before).length (child seed history) := by
  simp only [bellmanLiftedAfter, referenceSuffixHistoryJoin, List.drop_left, bellmanSuffixHistoryLower_lift]

/-- The selected bad tool is allocated, genuinely executed, then followed by
advance. Correct reports advance directly. Past the head, the selected original
fresh-child rule runs through the existing stage/handle lift. -/
def bellmanPostHeadRaw {Seed : Type*} (_input : StatisticalInput I) (head : I.Stage)
    (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed) : PolicyRule I Seed :=
  fun seed history =>
    if historyCursor history = 0 then
      match historyWrite history head, historyReport history head with
      | some (bit, serial), some (truth, _) =>
        if bit = truth then .advance head else
          match repair with
          | none => .abandon
          | some tool =>
            let handle : MismatchHandle I := ⟨head, serial⟩
            if (handle, tool) ∈ historyCommitments history then
              if (handle, tool) ∈ historyExecutions history then .advance head else .execute handle tool
            else .allocate handle tool
      | _, _ => .abandon
    else
      let before := history.take (history.idxOf (.advanced head) + 1)
      let child := if historyWritten history head = (historyReport history head).map Prod.fst then good else bad
      bellmanLiftedAfter 1 before child seed history

/-! Real finite-stop write and the early-report branch. These lemmas use the
original interpreter and public responses, rather than a stopping label. -/

noncomputable def bellmanHeadWrittenState (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (head : I.Stage) (truth : I.Stage → Bool)
    (tape : (input.experiment head).Tape) (n : ℕ) (bit : Bool) : State I :=
  let s := headReviewState input accounting head truth tape n
  record accounting s (.write head bit) (writeResponses C s head bit)
    (reportedWriteLedger C s head bit) s.cursor false

theorem bellmanHeadThen_run_write {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (head : I.Stage) (hhead : head.val = 0) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n) :
    run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 1) =
      bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
        (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head)) := by
  have hr := bellmanHeadThen_run_before input C accounting head hhead test available after sample n (by rw [hstop])
  let s := headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n
  have ha : s.halted = false := headReviewState_active input accounting head _ _ n
  have hl : liveStage s head := ⟨ha, (headReviewState_cursor input accounting head _ _ n).trans hhead.symm⟩
  have hw : s.ledger.written head = none := congrFun (headReviewState_written input accounting head _ _ n) head
  apply run_succ_of_step input C .uncapped accounting _ sample n _
  · rw [hr]
    exact ha
  · rw [hr, headReviewState_history, bellmanHeadThenRule_headReviewHistory input head hhead,
      bellmanHeadNext_write input head test sample.1 _ n hstop]
    exact Step.write s head _ hl hw (.inl rfl)

theorem bellmanHeadWrittenState_cursor (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (head : I.Stage) (truth : I.Stage → Bool)
    (tape : (input.experiment head).Tape) (n : ℕ) (bit : Bool) :
    (bellmanHeadWrittenState input C accounting head truth tape n bit).cursor = 0 :=
  headReviewState_cursor input accounting head truth tape n

theorem bellmanHeadWrittenState_written (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (head : I.Stage)
    (truth : I.Stage → Bool) (tape : (input.experiment head).Tape) (n : ℕ) (bit : Bool) :
    (bellmanHeadWrittenState input C accounting head truth tape n bit).ledger.written head = some bit := by
  simp only [bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
    writeLedger, Function.update_self]

theorem measurable_bellmanPostHeadRaw {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (head : I.Stage) (repair : Option I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad) :
    MeasurableRule (bellmanPostHeadRaw input head repair good bad) := by
  apply measurable_from_prod_countable_left
  intro history
  by_cases hc : historyCursor history = 0
  · simp only [bellmanPostHeadRaw, hc, ↓reduceIte]
    cases hw : historyWrite history head with
    | none => exact measurable_const
    | some entry =>
      cases hr : historyReport history head with
      | none => exact measurable_const
      | some report =>
        dsimp only
        split_ifs
        · exact measurable_const
        · cases repair with
          | none => exact measurable_const
          | some tool =>
            dsimp only
            split_ifs <;> exact measurable_const
  · simp only [bellmanPostHeadRaw, hc, ↓reduceIte, bellmanLiftedAfter]
    split_ifs
    · exact (measurable_of_countable (referenceSuffixActionLift I 1
        (historyActions (history.take (history.idxOf (.advanced head) + 1))).length)).comp
        (hgood.comp (measurable_id.prodMk measurable_const))
    · exact (measurable_of_countable (referenceSuffixActionLift I 1
        (historyActions (history.take (history.idxOf (.advanced head) + 1))).length)).comp
        (hbad.comp (measurable_id.prodMk measurable_const))

/-- A measurable, all-path legal original comparator policy using the given
local test and actual continuation rules. No risk/cost property is assumed. -/
noncomputable def bellmanTwoContinuationPolicy {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hdeferred : C.execution = .terminalBarrier) (accounting : NormalAccounting I)
    (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (repair : Option I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad) :
    AvailablePolicy input C accounting available Seed :=
  bellmanHeadThenPolicy input C hearly hdeferred accounting head test available
    (bellmanPostHeadRaw input head repair good bad)
    (measurable_bellmanPostHeadRaw input head repair good bad hgood hbad)

theorem bellmanPostHeadRaw_correct_of_prefix {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {m : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes m s)
    (head : I.Stage) (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hcursor : s.cursor = 0) (hwritten : s.ledger.written head = some (s.ledger.truth head))
    (hreported : ∃ clock, s.ledger.reportTime head = some clock) :
    bellmanPostHeadRaw input head repair good bad seed s.history = .advance head := by
  have hc := prefix_historyCursor input C mode accounting rule seed truth tapes hp
  have hw := prefix_historyWrite input C mode accounting rule seed truth tapes hp head
  have hr := prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp head
  obtain ⟨clock, ht⟩ := hreported
  simp only [bellmanPostHeadRaw, hc, hcursor, ↓reduceIte, hw, hwritten, Option.map_some,
    hr, ht]

theorem bellmanHeadThen_run_correct_advance {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head) :
    let after := bellmanPostHeadRaw input head repair good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 2) =
      record accounting written (.advance head) [.advanced head] (advanceLedger written head) 1 false := by
  dsimp only
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
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head _ _ n _
  have hw : written.ledger.written head = some (written.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some hcorrect)
  have hreport : ∃ clock, written.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have hraw := bellmanPostHeadRaw_correct_of_prefix input C hearly .uncapped accounting policy.val.rule
    sample.1 _ _ hp head repair good bad hc hw hreport
  have hwriteVisible : historyWritten written.history head = written.ledger.written head :=
    prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hp head
  have hafter : bellmanHeadThenRaw input head test after sample.1 written.history = .advance head := by
    simp only [bellmanHeadThenRaw, hwriteVisible, hw, reduceCtorEq, ↓reduceIte]
    exact hraw
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) written (.advance head)
      (record accounting written (.advance head) [.advanced head] (advanceLedger written head) 1 false) := by
    have h := Step.advance (input := input) (C := C) (mode := .uncapped) (accounting := accounting)
      (tapes := worldTapes input sample.2) written head ⟨rfl, hc.trans hhead.symm⟩ (by rw [hw]; simp) (.inl rfl)
    simpa only [hc] using h
  have hguard := guardedReplayRule_eq_of_step input C hearly hcurrent .uncapped accounting
    policy.val.rule (bellmanHeadThenRaw input head test after) sample.1 _ _ hp available
    (by rw [hafter]; exact hs) (by intro handle tool heq; rw [hafter] at heq; cases heq)
  change run input C .uncapped accounting policy.val.rule sample (n + 1 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 1) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ written
      (guardedReplayRule available (bellmanHeadThenRaw input head test after) sample.1 written.history) _
    rw [hguard, hafter]
    exact hs

theorem headReviewState_empty_corrections (input : StatisticalInput I) (accounting : NormalAccounting I)
    (head : I.Stage) (truth : I.Stage → Bool) (tape : (input.experiment head).Tape) (n : ℕ) :
    (headReviewState input accounting head truth tape n).ledger.commitments = [] ∧
      (headReviewState input accounting head truth tape n).ledger.executions = [] := by
  induction n with
  | zero => exact ⟨rfl, rfl⟩
  | succ n ih => exact ih

theorem bellmanHeadWrittenState_empty_corrections (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (accounting : NormalAccounting I) (head : I.Stage)
    (truth : I.Stage → Bool) (tape : (input.experiment head).Tape) (n : ℕ) (bit : Bool) :
    (bellmanHeadWrittenState input C accounting head truth tape n bit).ledger.commitments = [] ∧
      (bellmanHeadWrittenState input C accounting head truth tape n bit).ledger.executions = [] := by
  simpa only [bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
    writeLedger] using headReviewState_empty_corrections input accounting head truth tape n

theorem bellmanPostHeadRaw_wrong_of_prefix {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {m : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes m s)
    (head : I.Stage) (tool : I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hcursor : s.cursor = 0) (hwritten : s.ledger.written head = some (!s.ledger.truth head))
    (hreported : ∃ clock, s.ledger.reportTime head = some clock) :
    let handle : MismatchHandle I := ⟨head, s.ledger.writeSerial head⟩
    bellmanPostHeadRaw input head (some tool) good bad seed s.history =
      if (handle, tool) ∈ s.ledger.commitments.map (fun a => (a.handle, a.tool)) then
        if (handle, tool) ∈ s.ledger.executions.map (fun e => (e.handle, e.tool)) then .advance head
        else .execute handle tool
      else .allocate handle tool := by
  have hc := prefix_historyCursor input C mode accounting rule seed truth tapes hp
  have hw := prefix_historyWrite input C mode accounting rule seed truth tapes hp head
  have hr := prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp head
  have ha := prefix_historyCommitments input C mode accounting rule seed truth tapes hp
  have he := prefix_historyExecutions input C mode accounting rule seed truth tapes hp
  obtain ⟨clock, ht⟩ := hreported
  have hwrong : (!s.ledger.truth head) ≠ s.ledger.truth head := by
    cases s.ledger.truth head <;> decide
  simp only [bellmanPostHeadRaw, hc, hcursor, ↓reduceIte, hw, hwritten, Option.map_some,
    hr, ht, hwrong, ha, he]

def bellmanAllocateState (accounting : NormalAccounting I) (s : State I) (head : I.Stage)
    (tool : I.Tool) : State I :=
  let handle : MismatchHandle I := ⟨head, s.ledger.writeSerial head⟩
  record accounting s (.allocate handle tool) [.committed handle tool]
    (allocateLedger s handle tool) s.cursor false

theorem bellmanHeadThen_run_wrong_allocate {Seed : Type*} [MeasurableSpace Seed]
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
    let after := bellmanPostHeadRaw input head (some tool) good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 2) =
      bellmanAllocateState accounting written head tool := by
  dsimp only
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let handle : MismatchHandle I := ⟨head, written.ledger.writeSerial head⟩
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 1) = written :=
    bellmanHeadThen_run_write input C accounting head hhead test available after sample n hstop
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 1)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head _ _ n _
  have hw : written.ledger.written head = some (!written.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, written.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have he : written.ledger.commitments = [] ∧ written.ledger.executions = [] :=
    bellmanHeadWrittenState_empty_corrections input C hearly accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hraw : after sample.1 written.history = .allocate handle tool := by
    have h := bellmanPostHeadRaw_wrong_of_prefix input C hearly .uncapped accounting policy.val.rule
      sample.1 _ _ hp head tool good bad hc hw hreport
    simpa only [he.1, List.map_nil, List.not_mem_nil, ↓reduceIte] using h
  have hwriteVisible : historyWritten written.history head = written.ledger.written head :=
    prefix_historyWritten input C .uncapped accounting policy.val.rule sample.1 _ _ hp head
  have hafter : bellmanHeadThenRaw input head test after sample.1 written.history = .allocate handle tool := by
    simp only [bellmanHeadThenRaw, hwriteVisible, hw, reduceCtorEq, ↓reduceIte]
    exact hraw
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) written (.allocate handle tool)
      (bellmanAllocateState accounting written head tool) := by
    apply Step.allocate written handle tool rfl ⟨hw, rfl, hreport⟩ heligible
    · simp only [he.1, List.not_mem_nil, false_implies, implies_true]
    · simp only [he.1, List.not_mem_nil, false_implies, implies_true]
    · exact fun _ => hc.trans hhead.symm
    · exact .inl rfl
  have hguard := guardedReplayRule_eq_of_step input C hearly hcurrent .uncapped accounting
    policy.val.rule (bellmanHeadThenRaw input head test after) sample.1 _ _ hp available
    (by rw [hafter]; exact hs) (by intro h t heq; rw [hafter] at heq; cases heq; exact htool)
  change run input C .uncapped accounting policy.val.rule sample (n + 1 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 1) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ written
      (guardedReplayRule available (bellmanHeadThenRaw input head test after) sample.1 written.history) _
    rw [hguard, hafter]
    exact hs

theorem bellmanHeadThenRule_after_step {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (accounting : NormalAccounting I)
    (head : I.Stage) (test : (input.experiment head).AdmissibleRule Seed)
    (available : Finset I.Tool) (after : PolicyRule I Seed) (seed : Seed)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input) {m : ℕ} {s next : State I}
    (hp : Prefix input C .uncapped accounting (bellmanHeadThenRule input head test available after) seed truth tapes m s)
    (hwritten : s.ledger.written head ≠ none) (action : Action I)
    (ha : after seed s.history = action) (hs : Step input C .uncapped accounting tapes s action next)
    (havailable : ∀ handle tool, action = .allocate handle tool → tool ∈ available) :
    bellmanHeadThenRule input head test available after seed s.history = action := by
  have hw := prefix_historyWritten input C .uncapped accounting _ seed truth tapes hp head
  have hraw : bellmanHeadThenRaw input head test after seed s.history = action := by
    simp only [bellmanHeadThenRaw, hw, hwritten, ↓reduceIte]
    exact ha
  have hg := guardedReplayRule_eq_of_step input C hearly hcurrent .uncapped accounting
    (bellmanHeadThenRule input head test available after) (bellmanHeadThenRaw input head test after)
    seed truth tapes hp available (by rw [hraw]; exact hs)
    (by intro handle tool hh; exact havailable handle tool (hraw.symm.trans hh))
  exact hg.trans hraw

def bellmanExecuteState (accounting : NormalAccounting I) (s : State I) (head : I.Stage)
    (tool : I.Tool) : State I :=
  let handle : MismatchHandle I := ⟨head, s.ledger.writeSerial head⟩
  record accounting s (.execute handle tool) [.executed handle tool]
    (executeLedger s handle tool) s.cursor false

theorem bellmanHeadThen_run_wrong_execute {Seed : Type*} [MeasurableSpace Seed]
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
    let after := bellmanPostHeadRaw input head (some tool) good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    let allocated := bellmanAllocateState accounting written head tool
    run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 3) =
      bellmanExecuteState accounting allocated head tool := by
  dsimp only
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let handle : MismatchHandle I := ⟨head, allocated.ledger.writeSerial head⟩
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 2) = allocated :=
    bellmanHeadThen_run_wrong_allocate input C hearly hcurrent hdeferred accounting head hhead test available
      tool htool heligible good bad hgood hbad sample n hstop hwrong
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 2)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : allocated.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : allocated.ledger.written head = some (!allocated.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, allocated.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [allocated, bellmanAllocateState, allocateLedger, written, bellmanHeadWrittenState, record,
      reportedWriteLedger, hearly, ↓reduceIte, writeLedger, Function.update_self]
  have he : written.ledger.commitments = [] ∧ written.ledger.executions = [] :=
    bellmanHeadWrittenState_empty_corrections input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hcomm : allocated.ledger.commitments = [⟨handle, tool, written.clock⟩] := by
    simp only [allocated, bellmanAllocateState, record, allocateLedger, he.1, List.nil_append, handle]
  have hexec : allocated.ledger.executions = [] := he.2
  have hraw : after sample.1 allocated.history = .execute handle tool := by
    have h := bellmanPostHeadRaw_wrong_of_prefix input C hearly .uncapped accounting policy.val.rule
      sample.1 _ _ hp head tool good bad hc hw hreport
    simpa [hcomm, hexec, handle] using h
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) allocated (.execute handle tool)
      (bellmanExecuteState accounting allocated head tool) := by
    apply Step.execute allocated handle tool rfl ⟨hw, rfl, hreport⟩ heligible
    · exact ⟨⟨handle, tool, written.clock⟩, by simp only [hcomm, List.mem_cons, List.not_mem_nil, or_false], rfl, rfl⟩
    · simp only [hexec, List.not_mem_nil, false_implies, implies_true]
    · simp only [hexec, List.not_mem_nil, false_implies, implies_true]
    · exact fun _ => hc.trans hhead.symm
    · exact .inl rfl
  have haction := bellmanHeadThenRule_after_step input C hearly hcurrent accounting head test available after
    sample.1 _ _ hp (by rw [hw]; simp) (.execute handle tool) hraw hs
    (by intro h t hh; cases hh)
  change run input C .uncapped accounting policy.val.rule sample (n + 2 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 2) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ allocated
      (bellmanHeadThenRule input head test available after sample.1 allocated.history)
      (bellmanExecuteState accounting allocated head tool)
    rw [haction]
    exact hs

theorem bellmanHeadThen_run_wrong_advance {Seed : Type*} [MeasurableSpace Seed]
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
    let after := bellmanPostHeadRaw input head (some tool) good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    let allocated := bellmanAllocateState accounting written head tool
    let executed := bellmanExecuteState accounting allocated head tool
    run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 4) =
      record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false := by
  dsimp only
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  let allocated := bellmanAllocateState accounting written head tool
  let executed := bellmanExecuteState accounting allocated head tool
  let handle : MismatchHandle I := ⟨head, executed.ledger.writeSerial head⟩
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 3) = executed :=
    bellmanHeadThen_run_wrong_execute input C hearly hcurrent hdeferred accounting head hhead test available
      tool htool heligible good bad hgood hbad sample n hstop hwrong
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 3)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : executed.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : executed.ledger.written head = some (!executed.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, executed.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [executed, bellmanExecuteState, executeLedger, allocated, bellmanAllocateState, allocateLedger,
      written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have he : written.ledger.commitments = [] ∧ written.ledger.executions = [] :=
    bellmanHeadWrittenState_empty_corrections input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hcomm : executed.ledger.commitments = [⟨handle, tool, written.clock⟩] := by
    simp only [executed, bellmanExecuteState, executeLedger, allocated, bellmanAllocateState,
      record, allocateLedger, he.1, List.nil_append, handle]
  have hexec : executed.ledger.executions = [⟨handle, tool, allocated.clock⟩] := by
    simp only [executed, bellmanExecuteState, record, executeLedger, allocated, bellmanAllocateState,
      allocateLedger, he.2, List.nil_append, handle]
  have hraw : after sample.1 executed.history = .advance head := by
    have h := bellmanPostHeadRaw_wrong_of_prefix input C hearly .uncapped accounting policy.val.rule
      sample.1 _ _ hp head tool good bad hc hw hreport
    simpa [hcomm, hexec, handle] using h
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) executed (.advance head)
      (record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false) := by
    have h := Step.advance (input := input) (C := C) (mode := .uncapped) (accounting := accounting)
      (tapes := worldTapes input sample.2) executed head ⟨rfl, hc.trans hhead.symm⟩ (by rw [hw]; simp) (.inl rfl)
    simpa only [hc] using h
  have haction := bellmanHeadThenRule_after_step input C hearly hcurrent accounting head test available after
    sample.1 _ _ hp (by rw [hw]; simp) (.advance head) hraw hs (by intro h t hh; cases hh)
  change run input C .uncapped accounting policy.val.rule sample (n + 3 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 3) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ executed
      (bellmanHeadThenRule input head test available after sample.1 executed.history)
      (record accounting executed (.advance head) [.advanced head] (advanceLedger executed head) 1 false)
    rw [haction]
    exact hs

theorem bellmanPostHeadRaw_wrong_noTool_of_prefix {Seed : Type*}
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (mode : ResourceMode) (accounting : NormalAccounting I) (rule : PolicyRule I Seed)
    (seed : Seed) (truth : I.Stage → Bool) (tapes : ReviewTapes input) {m : ℕ} {s : State I}
    (hp : Prefix input C mode accounting rule seed truth tapes m s)
    (head : I.Stage) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hcursor : s.cursor = 0) (hwritten : s.ledger.written head = some (!s.ledger.truth head))
    (hreported : ∃ clock, s.ledger.reportTime head = some clock) :
    bellmanPostHeadRaw input head none good bad seed s.history = .abandon := by
  have hc := prefix_historyCursor input C mode accounting rule seed truth tapes hp
  have hw := prefix_historyWrite input C mode accounting rule seed truth tapes hp head
  have hr := prefix_historyReport_early input C hearly mode accounting rule seed truth tapes hp head
  obtain ⟨clock, ht⟩ := hreported
  have hwrong : (!s.ledger.truth head) ≠ s.ledger.truth head := by
    cases s.ledger.truth head <;> decide
  simp only [bellmanPostHeadRaw, hc, hcursor, ↓reduceIte, hw, hwritten, Option.map_some,
    hr, ht, hwrong]

theorem bellmanHeadThen_run_wrong_noTool {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hwrong : test.rule.decision sample.1 (worldTapes input sample.2 head) ≠ input.truthAt sample.2 head) :
    let after := bellmanPostHeadRaw input head none good bad
    let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
    run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 2) =
      stopState written true := by
  dsimp only
  let after := bellmanPostHeadRaw input head none good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head none good bad hgood hbad)
  let written := bellmanHeadWrittenState input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hr : run input C .uncapped accounting policy.val.rule sample (n + 1) = written :=
    bellmanHeadThen_run_write input C accounting head hhead test available after sample n hstop
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 1)
  rw [hr] at hp
  have ht := prefix_truth input C .uncapped accounting policy.val.rule sample.1 _ _ hp
  have hc : written.cursor = 0 := bellmanHeadWrittenState_cursor input C accounting head (input.truthAt sample.2)
    (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))
  have hw : written.ledger.written head = some (!written.ledger.truth head) := by
    rw [ht]
    exact (bellmanHeadWrittenState_written input C hearly accounting head (input.truthAt sample.2)
      (worldTapes input sample.2 head) n (test.rule.decision sample.1 (worldTapes input sample.2 head))).trans
      (congrArg some (Bool.eq_not_iff.mpr hwrong))
  have hreport : ∃ clock, written.ledger.reportTime head = some clock := by
    refine ⟨(headReviewState input accounting head (input.truthAt sample.2) (worldTapes input sample.2 head) n).clock, ?_⟩
    simp only [written, bellmanHeadWrittenState, record, reportedWriteLedger, hearly, ↓reduceIte,
      writeLedger, Function.update_self]
  have hraw := bellmanPostHeadRaw_wrong_noTool_of_prefix input C hearly .uncapped accounting policy.val.rule
    sample.1 _ _ hp head good bad hc hw hreport
  have hs : Step input C .uncapped accounting (worldTapes input sample.2) written .abandon (stopState written true) :=
    Step.abandon written rfl
  have haction := bellmanHeadThenRule_after_step input C hearly hcurrent accounting head test available after
    sample.1 _ _ hp (by rw [hw]; simp) .abandon hraw hs (by intro h t hh; cases hh)
  change run input C .uncapped accounting policy.val.rule sample (n + 1 + 1) = _
  apply run_succ_of_step input C .uncapped accounting policy.val.rule sample (n + 1) _
  · rw [hr]
    rfl
  · rw [hr]
    change Step input C .uncapped accounting _ written
      (bellmanHeadThenRule input head test available after sample.1 written.history) (stopState written true)
    rw [haction]
    exact hs

/-- The actual correct branch provides the continuation initial view. The
clock is recovered from its real prefix, not assumed as an alignment field. -/
theorem bellmanHeadThen_correct_initialView {Seed : Type*} [MeasurableSpace Seed]
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (hcurrent : C.allocation = .currentWindow) (hdeferred : C.execution = .terminalBarrier)
    (accounting : NormalAccounting I) (head : I.Stage) (hhead : head.val = 0)
    (test : (input.experiment head).AdmissibleRule Seed) (available : Finset I.Tool)
    (repair : Option I.Tool) (good bad : PolicyRule (I.freshSuffix 1) Seed)
    (hgood : MeasurableRule good) (hbad : MeasurableRule bad)
    (sample : Seed × input.World) (n : ℕ)
    (hstop : test.rule.stop sample.1 (worldTapes input sample.2 head) = n)
    (hcorrect : test.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head) :
    let rule := bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head repair good bad)
    let parent := run input C .uncapped accounting rule sample (n + 2)
    ReferenceSuffixView I 1 parent.history parent
      (initial ((input.freshSuffix 1).truthAt (referenceSuffixWorld input 1 sample.2))) := by
  let after := bellmanPostHeadRaw input head repair good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head repair good bad hgood hbad)
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 2)
  have hr := bellmanHeadThen_run_correct_advance input C hearly hcurrent hdeferred accounting head hhead test available
    repair good bad hgood hbad sample n hstop hcorrect
  apply suffixInitialView_of_prefix input 1 C accounting policy.val.rule sample.1 _ _ hp
  · change (run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 2)).cursor = 1
    rw [hr]
    rfl
  · change (run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 2)).halted = false
    rw [hr]
    rfl

/-- The actual wrong/repaired branch likewise supplies the continuation
initial view after allocate, execute and advance. -/
theorem bellmanHeadThen_wrong_initialView {Seed : Type*} [MeasurableSpace Seed]
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
    let rule := bellmanHeadThenRule input head test available (bellmanPostHeadRaw input head (some tool) good bad)
    let parent := run input C .uncapped accounting rule sample (n + 4)
    ReferenceSuffixView I 1 parent.history parent
      (initial ((input.freshSuffix 1).truthAt (referenceSuffixWorld input 1 sample.2))) := by
  let after := bellmanPostHeadRaw input head (some tool) good bad
  let policy := bellmanHeadThenPolicy input C hearly hdeferred accounting head test available after
    (measurable_bellmanPostHeadRaw input head (some tool) good bad hgood hbad)
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting policy.val.rule policy.val.legal sample (n + 4)
  have hr := bellmanHeadThen_run_wrong_advance input C hearly hcurrent hdeferred accounting head hhead test available
    tool htool heligible good bad hgood hbad sample n hstop hwrong
  apply suffixInitialView_of_prefix input 1 C accounting policy.val.rule sample.1 _ _ hp
  · change (run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 4)).cursor = 1
    rw [hr]
    rfl
  · change (run input C .uncapped accounting (bellmanHeadThenRule input head test available after) sample (n + 4)).halted = false
    rw [hr]
    rfl

end PaperProofs.Common.Native
