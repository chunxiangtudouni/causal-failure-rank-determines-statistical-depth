module

public import PaperProofs.Retained.PRet_RiskMassFlow_FailureCover_017
public import PaperProofs.Retained.PRet_RiskMassFlow_Telescope_014
public import PaperProofs.Retained.PDROC_RetainedReturn_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Retained PaperProofs.Statistics MeasureTheory
open scoped ENNReal

namespace PRetRiskMassFlow

variable {I : Instance}

theorem idealRisk_le_half (input : StatisticalInput I) (C : Contract I) (hretained : C.IsEarlyRetained)
    (accounting : NormalAccounting I) (budget : ℚ) (positive : 0 < budget) (small : budget ≤ 1/2) :
    risk input C .uncapped accounting (idealPolicy input C hretained accounting budget).rule (Measure.dirac ()) ≤
      ENNReal.ofReal ((budget : ℝ)/2) := by
  have nontermination : input.seededWorldLaw (Measure.dirac ()) {sample : Unit × input.World |
      ¬∃ n,(run input C .uncapped accounting (retainedRule input budget none) sample n).halted = true} = 0 := by
    exact PDROC.RetainedReturn.idealPolicy_nontermination_measure_zero input C hretained accounting budget positive small
  have riskSum : risk input C .uncapped accounting (retainedRule input budget none) (Measure.dirac ()) ≤
      ∑ stage : I.Stage,input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage) := by
    calc
      _ ≤ input.seededWorldLaw (Measure.dirac ())
          ({sample : Unit × input.World | ¬∃ n,(run input C .uncapped accounting (retainedRule input budget none) sample n).halted = true} ∪
            ⋃ stage : I.Stage,fatal input C accounting budget stage) :=
        measure_mono (failure_subset_nontermination_union_fatal input C hretained accounting budget positive small)
      _ ≤ input.seededWorldLaw (Measure.dirac ()) {sample : Unit × input.World |
          ¬∃ n,(run input C .uncapped accounting (retainedRule input budget none) sample n).halted = true} +
          input.seededWorldLaw (Measure.dirac ()) (⋃ stage : I.Stage,fatal input C accounting budget stage) := measure_union_le _ _
      _ ≤ 0 + ∑ stage : I.Stage,input.seededWorldLaw (Measure.dirac ()) (fatal input C accounting budget stage) := by
        rw [nontermination]
        simpa only [zero_add,tsum_fintype] using
          (measure_iUnion_le (μ := input.seededWorldLaw (Measure.dirac ())) (fun stage : I.Stage => fatal input C accounting budget stage))
      _ = _ := zero_add _
  exact riskSum.trans (fatalMass_sum_le_half input C hretained accounting budget positive small)

/-- EXACT first conjunct of the unchanged original ReferenceRiskAndCost.
The independent full expected-bill asymptotic conjunct remains its owner's
task and is not asserted by this theorem. -/
theorem referenceRiskAndCost_risk (input : StatisticalInput I) :
    ∀ (C : Contract I) (hretained : C.IsEarlyRetained) (accounting : NormalAccounting I) (budget : ℚ),
      0 < budget → budget ≤ 1/2 → risk input C .uncapped accounting
        (idealPolicy input C hretained accounting budget).rule (Measure.dirac ()) ≤ ENNReal.ofReal ((budget : ℝ)/2) := by
  intro C hretained accounting budget positive small
  exact idealRisk_le_half input C hretained accounting budget positive small

end PRetRiskMassFlow
