module

public import Common.PSTR_ST_SelectorIntegration_031
public import Common.PSTR_ST_SelectorCostSteps_027
public import Common.PSTR_ST_SelectorBranch_028

/-! Original-budget actual expected-fee recurrence with inherited selectors.
Every actual entry atom is charged, including zero mass, failed paths and
infinite bills. No finite-cost or performance premise is introduced. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Integration

open PaperProofs.Statistics

variable {I : Instance}

noncomputable def entryFreshObservationCost (input : StatisticalInput I)
    (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (stage : I.Stage) (history : List (VisibleEvent I)) : ℝ≥0∞ :=
  match entryRisk selector.choose input available budget history with
  | none => 0
  | some risk => expectedObservationBill (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix stage.val))
      (MaxSelector.rule (restrict I selector.choose stage.val (historyUsed history))
        (input.freshSuffix stage.val) (available \ historyUsed (I := I) history) (2 * risk) none)
      (Measure.dirac ())

theorem remainingObservationBill_eq_entryFreshCosts
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) stage.val sample
        ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (selectorEntryEvent input C accounting available selector budget stage history) *
          entryFreshObservationCost input available selector budget stage history := by
  have hrule : MeasurableRule (MaxSelector.rule selector.choose input available budget none) :=
    (policy selector.choose input C hearly accounting available budget none).measurable_rule
  rw [lintegral_eq_tsum_selectorEntry input C accounting available selector budget stage _
    (measurable_runRemainingObservationBill input C .uncapped accounting _
      hrule stage.val)
    (fun sample hs => runRemainingObservationBill_zero_of_no_entry input C .uncapped accounting _
      (rule_uncapped_legal selector.choose input C hearly accounting available budget none) sample stage hs)]
  apply tsum_congr
  intro history
  cases hrisk : entryRisk selector.choose input available budget history with
  | none =>
    have hE : selectorEntryEvent input C accounting available selector budget stage history = ∅ := by
      apply Set.eq_empty_iff_forall_notMem.mpr
      intro sample hs
      obtain ⟨_, risk, _, _, hr, _⟩ := entry_suffixBase input C hearly accounting available selector budget
        hbudget hsmall sample stage history hs
      rw [hrisk] at hr
      cases hr
    simp only [hE, Measure.restrict_empty, lintegral_zero_measure,
      entryFreshObservationCost, hrisk, measure_empty, mul_zero]
  | some risk =>
    simpa only [entryFreshObservationCost, hrisk] using
      selectorRemainingObservationBill_on_entry_eq_suffix input C hearly accounting available selector budget
        hbudget hsmall stage history risk hrisk

/-- A true one-stage global observation recurrence.  The successor term is
the sum of actual next-entry masses times actual fresh child costs, with
each child's original 2r budget and remaining available tools. -/
theorem remainingObservationBill_step_eq_entryFreshCosts
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (stage nextStage : I.Stage) (hnext : nextStage.val = stage.val + 1) :
    (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) stage.val sample
        ∂input.seededWorldLaw (Measure.dirac ())) =
      (∫⁻ sample, runStageObservationBill input C .uncapped accounting
        (MaxSelector.rule selector.choose input available budget none) stage sample
          ∂input.seededWorldLaw (Measure.dirac ())) +
      ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (selectorEntryEvent input C accounting available selector budget nextStage history) *
          entryFreshObservationCost input available selector budget nextStage history := by
  calc
    _ = (∫⁻ sample, runStageObservationBill input C .uncapped accounting
        (MaxSelector.rule selector.choose input available budget none) stage sample
          ∂input.seededWorldLaw (Measure.dirac ())) +
        ∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
          (MaxSelector.rule selector.choose input available budget none) (stage.val + 1) sample
            ∂input.seededWorldLaw (Measure.dirac ()) := by
      simp_rw [runRemainingObservationBill_step input C .uncapped accounting _ stage]
      exact lintegral_add_left (measurable_runStageObservationBill input C .uncapped accounting _
        (policy selector.choose input C hearly accounting available budget none).measurable_rule stage) _
    _ = _ := by
      rw [← hnext, remainingObservationBill_eq_entryFreshCosts input C hearly accounting available selector budget
        hbudget hsmall nextStage]

theorem expectedObservationBill_le_initial_add_entryFreshCosts
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first next : I.Stage) (hfirst : first.val = 0) (hnext : next.val = 1) :
    expectedObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
      referenceEntryLocalObservationPrice input available budget first [] +
      ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (selectorEntryEvent input C accounting available selector budget next history) *
          entryFreshObservationCost input available selector budget next history := by
  have hlegal := rule_uncapped_legal selector.choose input C hearly accounting available budget none
  have hzero (sample : Unit × input.World) :
      runRemainingObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) first.val sample =
        runObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) sample := by
    rw [hfirst]
    simpa only [runRemainingObservationBill, Nat.zero_le, ite_true] using
      (runObservationBill_eq_sum_stage input C .uncapped accounting _ hlegal sample).symm
  calc
    _ = ∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
        (MaxSelector.rule selector.choose input available budget none) first.val sample
          ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr (fun sample => (hzero sample).symm)
    _ = _ := remainingObservationBill_step_eq_entryFreshCosts input C hearly accounting available selector budget
      hbudget hsmall first next (by omega)
    _ ≤ _ := add_le_add (Fees.selectorInitialStageObservationBill_le_localPrice input C hearly accounting available selector budget
      hbudget hsmall first hfirst) le_rfl

theorem expectedBill_le_initial_add_entryFreshCosts_add_corrections
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first next : I.Stage) (hfirst : first.val = 0) (hnext : next.val = 1) :
    expectedBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
      (referenceEntryLocalObservationPrice input available budget first [] +
        ∑' history : List (VisibleEvent I),
          input.seededWorldLaw (Measure.dirac ()) (selectorEntryEvent input C accounting available selector budget next history) *
            entryFreshObservationCost input available selector budget next history) +
        (min I.stageCount I.toolCount : ℕ) * input.fees.maxCorrection := by
  exact (expectedBill_le_observation_add input C .uncapped accounting
    (policy selector.choose input C hearly accounting available budget none) (Measure.dirac ())).trans
      (add_le_add (expectedObservationBill_le_initial_add_entryFreshCosts input C hearly accounting available selector budget
        hbudget hsmall first next hfirst hnext) le_rfl)
noncomputable def nextEntryCostFunction (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available)
    (budget : ℚ) (stage : I.Stage) (sample : Unit × input.World) : ℝ≥0∞ :=
  match entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage sample with
  | none => 0
  | some history => entryFreshObservationCost input available selector budget stage history

theorem measurable_nextEntryCostFunction (input : StatisticalInput I)
    (C : Contract I) (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available)
    (budget : ℚ) (stage : I.Stage) :
    Measurable (nextEntryCostFunction input C accounting available selector budget stage) := by
  let price : Option (List (VisibleEvent I)) → ℝ≥0∞ := fun entry => match entry with
    | none => 0
    | some history => entryFreshObservationCost input available selector budget stage history
  change Measurable (price ∘ entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) stage)
  exact (measurable_of_countable price).comp
    (measurable_entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none)
      ((measurable_of_countable (fun history => MaxSelector.rule selector.choose input available budget none () history)).comp measurable_snd) stage)

theorem lintegral_nextEntryCostFunction
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2) (stage : I.Stage) :
    (∫⁻ sample, nextEntryCostFunction input C accounting available selector budget stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
      ∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
        (MaxSelector.rule selector.choose input available budget none) stage.val sample ∂input.seededWorldLaw (Measure.dirac ()) := by
  rw [remainingObservationBill_eq_entryFreshCosts input C hearly accounting available selector budget hbudget hsmall stage,
    lintegral_eq_tsum_selectorEntry input C accounting available selector budget stage _
      (measurable_nextEntryCostFunction input C accounting available selector budget stage)
      (fun sample hs => by simp only [nextEntryCostFunction, hs])]
  apply tsum_congr
  intro history
  have heq := setLIntegral_congr_fun (μ := input.seededWorldLaw (Measure.dirac ()))
    (measurableSet_selectorEntryEvent input C accounting available selector budget stage history)
    (fun sample (hs : sample ∈ selectorEntryEvent input C accounting available selector budget stage history) =>
      show nextEntryCostFunction input C accounting available selector budget stage sample =
        entryFreshObservationCost input available selector budget stage history by
          simp only [nextEntryCostFunction, show entryHistory input C .uncapped accounting
            (MaxSelector.rule selector.choose input available budget none) stage sample = some history from hs])
  rw [heq, setLIntegral_const, mul_comm]


end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.Integration
