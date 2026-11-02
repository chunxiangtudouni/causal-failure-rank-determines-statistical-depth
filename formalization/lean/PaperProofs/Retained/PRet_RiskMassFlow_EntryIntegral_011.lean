module

public import PaperProofs.Retained.PRet_RiskMassFlow_Events_008

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

theorem lintegral_eq_tsum_entry (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) (f : Unit × input.World → ℝ≥0∞) (measurable : Measurable f)
    (zero : ∀ sample, entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = none → f sample = 0) :
    (∫⁻ sample, f sample ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ∫⁻ sample in entryEvent input C accounting budget stage history,
        f sample ∂input.seededWorldLaw (Measure.dirac ()) := by
  classical
  have split : ∀ sample, f sample = ∑' history : List (VisibleEvent I),
      (entryEvent input C accounting budget stage history).indicator f sample := by
    intro sample
    cases entered : entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample with
    | none =>
      rw [zero sample entered]
      symm
      calc
        _ = ∑' _history : List (VisibleEvent I), (0 : ℝ≥0∞) := by
          apply tsum_congr
          intro history
          apply Set.indicator_of_notMem
          intro recorded
          have impossible := entered.symm.trans recorded
          cases impossible
        _ = 0 := tsum_zero
    | some history =>
      symm
      calc
        _ = (entryEvent input C accounting budget stage history).indicator f sample := by
          apply tsum_eq_single history
          intro other unequal
          apply Set.indicator_of_notMem
          intro recorded
          exact unequal (Option.some.inj (recorded.symm.trans entered))
        _ = f sample := Set.indicator_of_mem (show sample ∈ entryEvent input C accounting budget stage history from entered) f
  calc
    _ = ∫⁻ sample, ∑' history : List (VisibleEvent I), (entryEvent input C accounting budget stage history).indicator f sample
        ∂input.seededWorldLaw (Measure.dirac ()) := lintegral_congr split
    _ = ∑' history : List (VisibleEvent I), ∫⁻ sample, (entryEvent input C accounting budget stage history).indicator f sample
        ∂input.seededWorldLaw (Measure.dirac ()) :=
      lintegral_tsum (fun history => (measurable.indicator (measurableSet_entryEvent input C accounting budget stage history)).aemeasurable)
    _ = _ := by
      apply tsum_congr
      intro history
      exact lintegral_indicator (measurableSet_entryEvent input C accounting budget stage history) f

theorem fatalMass_eq_tsum_entry (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) :
    input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage) =
      ∑' history : List (VisibleEvent I), input.seededWorldLaw (Measure.dirac ())
        (fatal input C accounting budget stage ∩ entryEvent input C accounting budget stage history) := by
  classical
  let failed := fatal input C accounting budget stage
  have hfailed : MeasurableSet failed := measurableSet_fatal input C accounting budget stage
  have zero : ∀ sample : Unit × input.World,
      entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = none →
        failed.indicator (fun _ => (1 : ℝ≥0∞)) sample = 0 := by
    intro sample absent
    apply Set.indicator_of_notMem
    intro member
    have kind := member.2
    change (entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample).bind
      (entryKind I budget stage) = some .noTool at kind
    rw [absent] at kind
    cases kind
  have integral := lintegral_eq_tsum_entry input C accounting budget stage (failed.indicator (fun _ => (1 : ℝ≥0∞)))
    (measurable_const.indicator hfailed) zero
  simpa only [lintegral_indicator_const hfailed,one_mul,Measure.restrict_apply hfailed] using integral

theorem currentBudgetMass_eq_tsum_entry (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (budget : ℚ) (stage : I.Stage) :
    (∫⁻ sample, entryBudgetPotential input C accounting budget stage sample ∂input.seededWorldLaw (Measure.dirac ())) =
      ∑' history : List (VisibleEvent I), ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ) *
        input.seededWorldLaw (Measure.dirac ()) (entryEvent input C accounting budget stage history) := by
  rw [lintegral_eq_tsum_entry input C accounting budget stage _
    (measurable_entryBudgetPotential input C accounting budget stage)
    (fun sample absent => by simp only [entryBudgetPotential,absent])]
  apply tsum_congr
  intro history
  calc
    _ = ∫⁻ _sample in entryEvent input C accounting budget stage history,
        ENNReal.ofReal ((entryRisk I budget stage history).getD 0 : ℝ) ∂input.seededWorldLaw (Measure.dirac ()) := by
      apply setLIntegral_congr_fun (measurableSet_entryEvent input C accounting budget stage history)
      intro sample entered
      simp only [entryBudgetPotential,show entryHistory input C .uncapped accounting (retainedRule input budget none) stage sample = some history from entered]
    _ = _ := setLIntegral_const _ _

end PRetRiskMassFlow
