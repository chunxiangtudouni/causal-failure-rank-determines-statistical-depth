module

public import Common.PSTR_ST_SelectorEntry_021

/-! All-clock actual-run transport to the child retaining the ambient fixed
selector. All responses and failed/nonterminating paths are preserved. No
termination, finite-bill or generic/TABLE equality is a premise. -/

@[expose] public section

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector

open PaperProofs.Statistics

variable {I : Instance}

theorem selectorSuffix_rule_of_prefixes  (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (selector : Certified I available) (budget risk : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (base : ReferenceReplayCache I) (hbase : ReferenceSuffixBase I first budget risk base)
    (hparseBase : replay selector.choose input available budget base.seen = some base)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (childC : Contract (I.freshSuffix first)) (hchildEarly : childC.reporting = .early)
    (childAccounting : NormalAccounting (I.freshSuffix first)) (seed : Unit)
    (truth : I.Stage → Bool) (tapes : ReviewTapes input)
    (childTruth : (I.freshSuffix first).Stage → Bool) (childTapes : ReviewTapes (input.freshSuffix first))
    {m n : ℕ} {parent : State I} {child : State (I.freshSuffix first)}
    (hp : Prefix input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) seed truth tapes m parent)
    (hc : Prefix (input.freshSuffix first) childC .uncapped childAccounting
      (MaxSelector.rule (restrict I selector.choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none) seed childTruth childTapes n child)
    (view : ReferenceSuffixView I first base.seen parent child) :
    MaxSelector.rule selector.choose input available budget none seed parent.history =
      referenceSuffixActionLift I first (historyActions base.seen).length
        (MaxSelector.rule (restrict I selector.choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none seed child.history) := by
  have hbpos : 0 < 2 * risk := by linarith [hbase.valid.1]
  have hbsmall : 2 * risk ≤ 1 / 2 := by linarith [hbase.valid.2]
  have hparent := rule_eq_candidate_of_prefix (selector := selector) input C hearly accounting available budget hbudget hsmall none seed truth tapes hp
  have hchild := rule_eq_candidate_of_prefix (selector := selector.restrict first (historyUsed base.seen)) (input.freshSuffix first) childC hchildEarly childAccounting
    (available \ historyUsed (I := I) base.seen) (2 * risk) hbpos hbsmall none seed childTruth childTapes hc
  obtain ⟨cache, haligned⟩ := prefix_stateAligned (selector := selector.restrict first (historyUsed base.seen)) (input.freshSuffix first) childC hchildEarly childAccounting
    (available \ historyUsed (I := I) base.seen) (2 * risk) hbpos hbsmall none seed childTruth childTapes hc
  have hcand := selectorSuffix_candidateAction selector.choose input first available budget risk base hbase
    hparseBase child.history cache haligned.parsed
  exact hparent.trans ((congrArg (candidate selector.choose input available budget none) view.history).trans
    (hcand.trans (congrArg (referenceSuffixActionLift I first (historyActions base.seen).length) hchild.symm)))

theorem selectorSuffix_run_view  (input : StatisticalInput I) (first : ℕ)
    (available : Finset I.Tool) (selector : Certified I available) (budget risk : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (base : ReferenceReplayCache I) (hbase : ReferenceSuffixBase I first budget risk base)
    (hparseBase : replay selector.choose input available budget base.seen = some base)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (childC : Contract (I.freshSuffix first)) (hchildEarly : childC.reporting = .early)
    (childAccounting : NormalAccounting (I.freshSuffix first)) (sample : Unit × input.World) (start : ℕ)
    (hstart : ReferenceSuffixView I first base.seen
      (run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample start)
      (initial ((input.freshSuffix first).truthAt (referenceSuffixWorld input first sample.2)))) :
    ∀ k : ℕ, ReferenceSuffixView I first base.seen
      (run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample (start + k))
      (run (input.freshSuffix first) childC .uncapped childAccounting
        (MaxSelector.rule (restrict I selector.choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none)
        (sample.1, referenceSuffixWorld input first sample.2) k) := by
  let rule : PolicyRule I Unit := MaxSelector.rule selector.choose input available budget none
  let childRule : PolicyRule (I.freshSuffix first) Unit :=
    MaxSelector.rule (restrict I selector.choose first (historyUsed base.seen)) (input.freshSuffix first) (available \ historyUsed (I := I) base.seen) (2 * risk) none
  let childSample : Unit × (input.freshSuffix first).World := (sample.1, referenceSuffixWorld input first sample.2)
  have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget none
  have hchildLegal := rule_uncapped_legal (restrict I selector.choose first (historyUsed base.seen)) (input.freshSuffix first) childC hchildEarly childAccounting
    (available \ historyUsed (I := I) base.seen) (2 * risk) none
  intro k
  induction k with
  | zero => simpa only [Nat.add_zero, run] using hstart
  | succ k ih =>
    change ReferenceSuffixView I first base.seen (run input C .uncapped accounting rule sample (start + (k + 1)))
      (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample (k + 1))
    by_cases hh : (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).halted = true
    · have hparentHalt : (run input C .uncapped accounting rule sample (start + k)).halted = true := ih.halted.trans hh
      rw [Nat.add_succ, run_succ_of_halted input C .uncapped accounting rule sample (start + k) hparentHalt,
        run_succ_of_halted (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k hh]
      exact ih
    · have hchildActive : (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).halted = false := Bool.eq_false_iff.mpr hh
      have hparentActive : (run input C .uncapped accounting rule sample (start + k)).halted = false := ih.halted.trans hchildActive
      obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting rule hlegal sample (start + k)
      obtain ⟨l, _, hc⟩ := run_has_prefix (input.freshSuffix first) childC .uncapped childAccounting childRule hchildLegal childSample k
      have ha := selectorSuffix_rule_of_prefixes input first available selector budget risk hbudget hsmall base hbase hparseBase
        C hearly accounting childC hchildEarly childAccounting sample.1 (input.truthAt sample.2) (worldTapes input sample.2)
        ((input.freshSuffix first).truthAt childSample.2) (worldTapes (input.freshSuffix first) childSample.2) hp hc ih
      obtain ⟨nextParent, hps⟩ := hlegal sample.1 (input.truthAt sample.2) (worldTapes input sample.2) m _ hp hparentActive
      obtain ⟨nextChild, hcs⟩ := hchildLegal sample.1 ((input.freshSuffix first).truthAt childSample.2)
        (worldTapes (input.freshSuffix first) childSample.2) l _ hc hchildActive
      have hpsLift := hps
      rw [ha] at hpsLift
      have hcounts := referenceSuffix_reviews_of_prefixes input first C accounting rule childC childAccounting childRule sample.1
        (input.truthAt sample.2) (worldTapes input sample.2) ((input.freshSuffix first).truthAt childSample.2)
        (worldTapes (input.freshSuffix first) childSample.2) hp hc base.seen ih hbase.observations
      have htruths : ∀ stage, (run input C .uncapped accounting rule sample (start + k)).ledger.truth (I.freshStageLift first stage) =
          (run (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k).ledger.truth stage := by
        intro stage
        calc
          _ = input.truthAt sample.2 (I.freshStageLift first stage) := congrFun (prefix_truth input C .uncapped accounting rule sample.1 _ _ hp) _
          _ = (input.freshSuffix first).truthAt childSample.2 stage := rfl
          _ = _ := (congrFun (prefix_truth (input.freshSuffix first) childC .uncapped childAccounting childRule sample.1 _ _ hc) stage).symm
      have hnext := referenceSuffix_step_view input first C childC hearly hchildEarly accounting childAccounting
        (worldTapes input sample.2) (worldTapes (input.freshSuffix first) childSample.2) base.seen ih hcounts htruths
        (fun stage index => (referenceSuffixWorld_letter input first sample.2 stage index).symm) hpsLift hcs
      rw [Nat.add_succ, run_succ_of_step input C .uncapped accounting rule sample (start + k) nextParent hparentActive hps,
        run_succ_of_step (input.freshSuffix first) childC .uncapped childAccounting childRule childSample k nextChild hchildActive hcs]
      exact hnext

/-- Full actual entry-to-fresh-suffix run transport, on EVERY sample and
EVERY returned-action clock, including failure, abandonment and infinite
review paths. The source view is obtained from actual Prefix alignment. -/
theorem selectorEntry_run_view  (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (sample : Unit × input.World) (stage : I.Stage) (history : List (VisibleEvent I))
    (hentry : entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample = some history) :
    ∃ (base : ReferenceReplayCache I) (risk : ℚ) (start : ℕ), base.seen = history ∧
      entryRisk selector.choose input available budget history = some risk ∧
      ReferenceSuffixBase I stage.val budget risk base ∧
      (run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample start).cursor = stage.val ∧
      (∀ k < start, (run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample k).cursor ≠ stage.val) ∧
      (run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample start).history = history ∧
      ∀ k : ℕ, ReferenceSuffixView I stage.val history
        (run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample (start + k))
        (run (input.freshSuffix stage.val) (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
          (zeroNormalAccounting (I.freshSuffix stage.val))
          (MaxSelector.rule (restrict I selector.choose stage.val (historyUsed history)) (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none)
          (sample.1, referenceSuffixWorld input stage.val sample.2) k) := by
  obtain ⟨base, risk, hparse, hseen, hrisk, hbase⟩ := entry_suffixBase input C hearly accounting available selector budget
    hbudget hsmall sample stage history hentry
  obtain ⟨start, hcursor, hbefore, hhistory⟩ :=
    (entryHistory_some_iff input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample history).mp hentry
  have hparseBase : replay selector.choose input available budget base.seen = some base := by rw [hseen]; exact hparse
  have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget none
  obtain ⟨m, _, hp⟩ := run_has_prefix input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) hlegal sample start
  obtain ⟨cache, haligned⟩ := prefix_stateAligned (selector := selector) input C hearly accounting available budget hbudget hsmall none
    sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp
  have hparsed : replay selector.choose input available budget history = some cache := by rw [← hhistory]; exact haligned.parsed
  have heq : cache = base := Option.some.inj (hparsed.symm.trans hparse)
  subst cache
  have hhalt : (run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample start).halted = false :=
    haligned.halted.symm.trans hbase.active
  have hclock : (run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample start).clock =
      (historyActions base.seen).length := by
    rw [← prefix_historyActions_length input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none)
      sample.1 (input.truthAt sample.2) (worldTapes input sample.2) hp, hhistory, hseen]
  have hstart : ReferenceSuffixView I stage.val base.seen
      (run input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample start)
      (initial ((input.freshSuffix stage.val).truthAt (referenceSuffixWorld input stage.val sample.2))) := by
    constructor
    · simpa only [initial, referenceSuffixHistoryJoin, referenceSuffixHistoryLift, List.map_nil, List.append_nil] using hhistory.trans hseen.symm
    · simpa only [initial, Nat.add_zero] using hcursor
    · simpa only [initial, Nat.add_zero] using hclock
    · exact hhalt
  refine ⟨base, risk, start, hseen, hrisk, hbase, hcursor, hbefore, hhistory, ?_⟩
  intro k
  simpa only [hseen] using selectorSuffix_run_view input stage.val available selector budget risk hbudget hsmall base hbase hparseBase
    C hearly accounting (currentRelaxedContract (I.freshSuffix stage.val)) rfl (zeroNormalAccounting (I.freshSuffix stage.val)) sample start hstart k


/-- Full remaining observation bill at a genuine entry equals the actual
inherited-selector child bill. No subtraction of infinite bills, success gate
or finite expectation premise is used. The original contract need only report
early, so this transport also covers non-current allocation contracts. -/
theorem selectorEntry_observationBill_eq_suffix (input : StatisticalInput I)
    (C : Contract I) (hearly : C.reporting = .early) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (selector : Certified I available)
    (budget : ℚ) (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (risk : ℚ)
    (hrisk : entryRisk selector.choose input available budget history = some risk)
    (sample : Unit × input.World)
    (hentry : entryHistory input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) stage sample = some history) :
    runRemainingObservationBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) stage.val sample =
      runObservationBill (input.freshSuffix stage.val)
        (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
        (zeroNormalAccounting (I.freshSuffix stage.val))
        (MaxSelector.rule (restrict I selector.choose stage.val (historyUsed history))
          (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none)
        (sample.1, input.restrictFreshWorld stage.val sample.2) := by
  obtain ⟨base, r, start, hseen, hr, hbase, _hc, _hb, _hh, views⟩ :=
    selectorEntry_run_view input C hearly accounting available selector budget hbudget hsmall
      sample stage history hentry
  have heq : r = risk := Option.some.inj (hr.symm.trans hrisk)
  subst r
  let childC := currentRelaxedContract (I.freshSuffix stage.val)
  let childAccounting := zeroNormalAccounting (I.freshSuffix stage.val)
  let childRule := MaxSelector.rule (restrict I selector.choose stage.val (historyUsed history))
    (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none
  have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget none
  have hchildLegal := rule_uncapped_legal (restrict I selector.choose stage.val (historyUsed history))
    (input.freshSuffix stage.val) childC rfl childAccounting
    (available \ historyUsed (I := I) history) (2 * risk) none
  have hobs : ∀ target : (I.freshSuffix stage.val).Stage,
      historyObservations history (I.freshStageLift stage.val target) = [] := by
    simpa only [hseen] using hbase.observations
  have hbill := referenceSuffix_observationBill_of_run_view input stage.val C accounting
    (MaxSelector.rule selector.choose input available budget none) hlegal childC childAccounting
    childRule hchildLegal sample history start hobs views
  simpa only [referenceSuffixWorld_eq_restrictFreshWorld] using hbill

end PaperProofs.Common.Native.PSTRStatistics.MaxSelector
