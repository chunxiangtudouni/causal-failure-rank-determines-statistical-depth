module

public import PaperProofs.Common.PSTR_ST_SelectorCostRecurrence_032
public import PaperProofs.Common.PSTR_ST_SelectorWriteError_030

/-! Actual first-stage fee recurrence compressed to the TWO fixed inherited
children. Bad fees are charged only on a genuine ordinary write error; the
no-tool branch does not create a continuation. Infinite bills are retained. -/

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PaperProofs.Common.Native.PSTRStatistics.MaxSelector.BranchCost

open PaperProofs.Statistics

variable {I : Instance}

noncomputable def rawObservationCost (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (stage : I.Stage) (pastUsed : Finset I.Tool) (budget : ℚ) : ℝ≥0∞ :=
  expectedObservationBill (input.freshSuffix stage.val)
    (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
    (zeroNormalAccounting (I.freshSuffix stage.val))
    (MaxSelector.rule (restrict I selector.choose stage.val pastUsed) (input.freshSuffix stage.val)
      (available \ pastUsed) budget none) (Measure.dirac ())

noncomputable def goodObservationCost (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (stage : I.Stage) (budget : ℚ) : ℝ≥0∞ :=
  expectedObservationBill (input.freshSuffix stage.val)
    (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
    (zeroNormalAccounting (I.freshSuffix stage.val))
    (MaxSelector.rule (restrict I selector.choose stage.val ∅) (input.freshSuffix stage.val)
      available budget none) (Measure.dirac ())

noncomputable def badObservationCost (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (stage : I.Stage) (tool : I.Tool) (budget : ℚ) : ℝ≥0∞ :=
  expectedObservationBill (input.freshSuffix stage.val)
    (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
    (zeroNormalAccounting (I.freshSuffix stage.val))
    (MaxSelector.rule (restrict I selector.choose stage.val {tool}) (input.freshSuffix stage.val)
      (available.erase tool) budget none) (Measure.dirac ())

theorem rawObservationCost_good (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (stage : I.Stage) (budget : ℚ) :
    rawObservationCost input available selector stage ∅ budget =
      goodObservationCost input available selector stage budget := by
  exact congrArg (fun remaining : Finset I.Tool =>
    expectedObservationBill (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix stage.val))
      (MaxSelector.rule (restrict I selector.choose stage.val ∅) (input.freshSuffix stage.val)
        remaining budget none) (Measure.dirac ())) (Finset.sdiff_empty)

theorem rawObservationCost_bad (input : StatisticalInput I) (available : Finset I.Tool)
    (selector : Certified I available) (stage : I.Stage) (tool : I.Tool) (budget : ℚ) :
    rawObservationCost input available selector stage {tool} budget =
      badObservationCost input available selector stage tool budget := by
  exact congrArg (fun remaining : Finset I.Tool =>
    expectedObservationBill (input.freshSuffix stage.val)
      (currentRelaxedContract (I.freshSuffix stage.val)) .uncapped
      (zeroNormalAccounting (I.freshSuffix stage.val))
      (MaxSelector.rule (restrict I selector.choose stage.val {tool}) (input.freshSuffix stage.val)
        remaining budget none) (Measure.dirac ())) (Finset.sdiff_singleton_eq_erase tool available)

theorem nextEntryCostFunction_finiteBad_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (depth : ℕ+) (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth))
    (tool : I.Tool) (hpick : selector.choose first ∅ = some tool)
    (sample : Unit × input.World) :
    Integration.nextEntryCostFunction input C accounting available selector budget nextStage sample ≤
      goodObservationCost input available selector nextStage (budget / 2) +
        (Branch.selectorStageWriteError input C accounting available selector budget first).indicator
          (fun _ => badObservationCost input available selector nextStage tool
            (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val))) sample := by
  cases hentry : entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) nextStage sample with
  | none => simp only [Integration.nextEntryCostFunction, hentry]; exact bot_le
  | some history =>
    obtain ⟨error, risk, _, hrisk, hstep, hused, herr⟩ := Branch.selectorInitialNextEntry_children input C hearly accounting
      available selector budget hbudget hsmall first nextStage hfirst hnext (.finiteBad depth) hkind sample history hentry
    have hrisk' : entryRisk selector.choose input available budget history = some risk := hrisk
    cases error with
    | false =>
      have hr : risk = budget / 2 / 2 := Option.some.inj hstep
      have hu : historyUsed history = ∅ := hused
      have htwo : 2 * (budget / 2 / 2) = budget / 2 := by ring
      simp only [Integration.nextEntryCostFunction, hentry, Integration.entryFreshObservationCost, hrisk', hu, hr, htwo]
      apply le_add_right
      exact le_of_eq (rawObservationCost_good input available selector nextStage (budget / 2))
    | true =>
      have hr : risk = controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val) :=
        Option.some.inj hstep
      obtain ⟨picked, hselected, hu⟩ := hused
      have ht : picked = tool := Option.some.inj (hselected.symm.trans hpick)
      subst picked
      rw [Set.indicator_of_mem (herr rfl)]
      simp only [Integration.nextEntryCostFunction, hentry, Integration.entryFreshObservationCost, hrisk', hu, hr]
      apply le_add_left
      exact le_of_eq (rawObservationCost_bad input available selector nextStage tool
        (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val)))

theorem expectedObservationBill_finiteBad_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (depth : ℕ+) (hkind : referenceAvailableRankCase I available first ∅ = some (.finiteBad depth))
    (tool : I.Tool) (hpick : selector.choose first ∅ = some tool) :
    expectedObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
      referenceEntryLocalObservationPrice input available budget first [] +
        (goodObservationCost input available selector nextStage (budget / 2) +
          ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) *
            badObservationCost input available selector nextStage tool
              (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val))) := by
  let μ := input.seededWorldLaw (Measure.dirac ())
  let E := Branch.selectorStageWriteError input C accounting available selector budget first
  let good := goodObservationCost input available selector nextStage (budget / 2)
  let bad := badObservationCost input available selector nextStage tool
    (2 * controllerBadRisk (budget / 2) (controllerTarget (budget / 2) depth.val))
  have hE : MeasurableSet E := WriteError.measurableSet_selectorStageWriteError input C accounting available selector budget first
  have ht : referenceAvailableEntryTarget input available budget [] =
      some (controllerTarget (budget / 2) depth.val) :=
    referenceAvailableEntryTarget_initial input available budget hbudget hsmall first hfirst (.finiteBad depth) hkind
  have he : μ E ≤ ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) :=
    WriteError.selectorFirstStageWriteError_le input C hearly accounting available selector budget
      hbudget hsmall first hfirst _ ht
  have hfuture : (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) nextStage.val sample ∂μ) ≤
        good + ENNReal.ofReal (controllerTarget (budget / 2) depth.val : ℝ) * bad := by
    rw [← Integration.lintegral_nextEntryCostFunction input C hearly accounting available selector budget hbudget hsmall nextStage]
    calc
      _ ≤ ∫⁻ sample, good + E.indicator (fun _ => bad) sample ∂μ :=
        lintegral_mono (nextEntryCostFunction_finiteBad_le input C hearly accounting available selector budget
          hbudget hsmall first nextStage hfirst hnext depth hkind tool hpick)
      _ = good + bad * μ E := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_indicator_const hE]
      _ ≤ _ := add_le_add le_rfl (by simpa only [mul_comm] using mul_le_mul' (le_refl bad) he)
  calc
    _ ≤ referenceEntryLocalObservationPrice input available budget first [] +
        (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
          (MaxSelector.rule selector.choose input available budget none) nextStage.val sample ∂μ) := by
      rw [Integration.remainingObservationBill_eq_entryFreshCosts input C hearly accounting available selector budget hbudget hsmall nextStage]
      exact Integration.expectedObservationBill_le_initial_add_entryFreshCosts input C hearly accounting available selector budget
        hbudget hsmall first nextStage hfirst hnext
    _ ≤ _ := add_le_add le_rfl hfuture

theorem nextEntryCostFunction_noTool_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (hkind : referenceAvailableRankCase I available first ∅ = some .noTool)
    (sample : Unit × input.World) :
    Integration.nextEntryCostFunction input C accounting available selector budget nextStage sample ≤
      goodObservationCost input available selector nextStage (budget / 2) := by
  cases hentry : entryHistory input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) nextStage sample with
  | none => simp only [Integration.nextEntryCostFunction, hentry]; exact bot_le
  | some history =>
    obtain ⟨error, risk, _, hrisk, hstep, hused, _⟩ := Branch.selectorInitialNextEntry_children input C hearly accounting
      available selector budget hbudget hsmall first nextStage hfirst hnext .noTool hkind sample history hentry
    have hrisk' : entryRisk selector.choose input available budget history = some risk := hrisk
    cases error with
    | true => cases hstep
    | false =>
      have hr : risk = budget / 2 / 2 := Option.some.inj hstep
      have hu : historyUsed history = ∅ := hused
      have htwo : 2 * (budget / 2 / 2) = budget / 2 := by ring
      simp only [Integration.nextEntryCostFunction, hentry, Integration.entryFreshObservationCost, hrisk', hu, hr, htwo]
      exact le_of_eq (rawObservationCost_good input available selector nextStage (budget / 2))

theorem expectedObservationBill_noTool_le
    (input : StatisticalInput I) (C : Contract I) (hearly : C.reporting = .early)
    (accounting : NormalAccounting I) (available : Finset I.Tool) (selector : Certified I available) (budget : ℚ)
    (hbudget : 0 < budget) (hsmall : budget ≤ 1 / 2)
    (first nextStage : I.Stage) (hfirst : first.val = 0) (hnext : nextStage.val = 1)
    (hkind : referenceAvailableRankCase I available first ∅ = some .noTool) :
    expectedObservationBill input C .uncapped accounting (MaxSelector.rule selector.choose input available budget none) (Measure.dirac ()) ≤
      referenceEntryLocalObservationPrice input available budget first [] +
        goodObservationCost input available selector nextStage (budget / 2) := by
  let μ := input.seededWorldLaw (Measure.dirac ())
  have hfuture : (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
      (MaxSelector.rule selector.choose input available budget none) nextStage.val sample ∂μ) ≤
        goodObservationCost input available selector nextStage (budget / 2) := by
    rw [← Integration.lintegral_nextEntryCostFunction input C hearly accounting available selector budget hbudget hsmall nextStage]
    apply (lintegral_mono (nextEntryCostFunction_noTool_le input C hearly accounting available selector budget
      hbudget hsmall first nextStage hfirst hnext hkind)).trans
    simp only [lintegral_const, measure_univ, mul_one, le_refl]
  calc
    _ ≤ referenceEntryLocalObservationPrice input available budget first [] +
        (∫⁻ sample, runRemainingObservationBill input C .uncapped accounting
          (MaxSelector.rule selector.choose input available budget none) nextStage.val sample ∂μ) := by
      rw [Integration.remainingObservationBill_eq_entryFreshCosts input C hearly accounting available selector budget hbudget hsmall nextStage]
      exact Integration.expectedObservationBill_le_initial_add_entryFreshCosts input C hearly accounting available selector budget
        hbudget hsmall first nextStage hfirst hnext
    _ ≤ _ := add_le_add le_rfl hfuture


end PaperProofs.Common.Native.PSTRStatistics.MaxSelector.BranchCost
