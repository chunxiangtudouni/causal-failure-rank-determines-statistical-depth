module

public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_001
public import PaperProofs.Retained.PDROC_RetainedEnvelopeRun_EntryLaw_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2000000

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics
open MeasureTheory
open scoped ENNReal

namespace PDROC.RetainedEnvelopeRun

variable {I : Instance}

theorem measurableSet_stageEntryEvent (input : StatisticalInput I) (C : Contract I)
    (accounting : NormalAccounting I) (budget : ℚ) (stage : I.Stage)
    (history : List (VisibleEvent I)) :
    MeasurableSet (stageEntryEvent input C accounting budget stage history) :=
  (measurable_entryHistory input C .uncapped accounting (retainedRule input budget none)
    (measurable_of_countable _) stage) (measurableSet_singleton (some history))

theorem stageObservationBill_on_entry_le (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I)) (p : ℚ)
    (target : PRetRiskMassFlow.entryTarget I budget stage history = some p) :
    (∫⁻ sample in stageEntryEvent input C accounting budget stage history,
      runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
      input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
        (input.experiment stage).bayesObservationCharge (Measure.dirac ()) ((input.experiment stage).posteriorSPRT p) := by
  calc
    _ ≤ ∫⁻ sample in stageEntryEvent input C accounting budget stage history,
        (input.experiment stage).observationCharge
          ((input.experiment stage).posteriorThresholdStop p (sample.2 stage).2)
        ∂input.seededWorldLaw (Measure.dirac ()) := by
      apply setLIntegral_mono' (measurableSet_stageEntryEvent input C accounting budget stage history)
      intro sample entered
      have bound := stageObservationBill_le_entryCharge input C hretained accounting budget positive small stage sample
      change entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history at entered
      simpa only [entrySampleBound, entered, target] using bound
    _ = _ := EntryLaw.lintegral_on_entry_posteriorObservationCharge input C .uncapped accounting
      (idealPolicy input C hretained accounting budget) stage history p

theorem stageObservationBill_on_entry_none (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2)
    (stage : I.Stage) (history : List (VisibleEvent I))
    (target : PRetRiskMassFlow.entryTarget I budget stage history = none) :
    (∫⁻ sample in stageEntryEvent input C accounting budget stage history,
      runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) = 0 := by
  apply setLIntegral_eq_zero (measurableSet_stageEntryEvent input C accounting budget stage history)
  intro sample entered
  exact stageObservationBill_zero_of_entry_none input C hretained accounting budget positive small
    stage history sample entered target

/-- The genuine first-entry target determines this analysis price. It is
the original posteriorSPRT Bayes charge, with None retaining zero charge. -/
noncomputable def entryObservationPrice (input : StatisticalInput I) (budget : ℚ)
    (stage : I.Stage) (history : List (VisibleEvent I)) : ℝ≥0∞ :=
  match PRetRiskMassFlow.entryTarget I budget stage history with
  | none => 0
  | some p => (input.experiment stage).bayesObservationCharge (Measure.dirac ())
      ((input.experiment stage).posteriorSPRT p)

theorem lintegral_stageBill_eq_tsum_entry (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2) (stage : I.Stage) :
    (∫⁻ sample, runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ∫⁻ sample in stageEntryEvent input C accounting budget stage history,
        runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample
        ∂input.seededWorldLaw (Measure.dirac ()) := by
  classical
  let f := runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage
  have hf : Measurable f := measurable_runStageObservationBill input C .uncapped accounting
    (retainedRule input budget none) (measurable_of_countable _) stage
  have hsplit : ∀ sample, f sample = ∑' history : List (VisibleEvent I),
      (stageEntryEvent input C accounting budget stage history).indicator f sample := by
    intro sample
    cases entered : entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample with
    | none =>
      rw [show f sample = 0 from stageObservationBill_zero_of_no_entry input C hretained accounting
        budget positive small stage sample entered]
      symm
      calc
        _ = ∑' _history : List (VisibleEvent I), (0 : ℝ≥0∞) := by
          apply tsum_congr
          intro history
          apply Set.indicator_of_notMem
          intro member
          have impossible := entered.symm.trans member
          cases impossible
        _ = 0 := tsum_zero
    | some history =>
      symm
      calc
        _ = (stageEntryEvent input C accounting budget stage history).indicator f sample := by
          apply tsum_eq_single history
          intro other different
          apply Set.indicator_of_notMem
          intro member
          exact different (Option.some.inj (member.symm.trans entered))
        _ = f sample := Set.indicator_of_mem (show sample ∈ stageEntryEvent input C accounting budget stage history from entered) f
  calc
    _ = ∫⁻ sample, ∑' history : List (VisibleEvent I),
        (stageEntryEvent input C accounting budget stage history).indicator f sample
        ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr hsplit
    _ = ∑' history : List (VisibleEvent I), ∫⁻ sample,
        (stageEntryEvent input C accounting budget stage history).indicator f sample
        ∂input.seededWorldLaw (Measure.dirac ()) :=
      lintegral_tsum (fun history => (hf.indicator (measurableSet_stageEntryEvent input C accounting budget stage history)).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro history
      exact lintegral_indicator (measurableSet_stageEntryEvent input C accounting budget stage history) f

theorem expected_stageBill_le_entryPrices (input : StatisticalInput I) (C : Contract I)
    (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I)
    (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1 / 2) (stage : I.Stage) :
    (∫⁻ sample, runStageObservationBill input C .uncapped accounting (retainedRule input budget none) stage sample
      ∂input.seededWorldLaw (Measure.dirac ())) ≤
      ∑' history : List (VisibleEvent I),
        input.seededWorldLaw (Measure.dirac ()) (stageEntryEvent input C accounting budget stage history) *
          entryObservationPrice input budget stage history := by
  rw [lintegral_stageBill_eq_tsum_entry input C hretained accounting budget positive small stage]
  apply ENNReal.tsum_le_tsum
  intro history
  cases target : PRetRiskMassFlow.entryTarget I budget stage history with
  | none =>
    rw [stageObservationBill_on_entry_none input C hretained accounting budget positive small stage history target]
    exact bot_le
  | some p =>
    simpa only [entryObservationPrice, target] using
      stageObservationBill_on_entry_le input C hretained accounting budget positive small stage history p target

end PDROC.RetainedEnvelopeRun
