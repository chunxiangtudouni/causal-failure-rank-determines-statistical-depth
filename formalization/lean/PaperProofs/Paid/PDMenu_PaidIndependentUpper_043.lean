module

public import PaperProofs.Paid.PDMenu_PaidHeadExpectation_020
public import PaperProofs.Paid.PDMenu_PaidIndependentPolicy_040

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open BellmanPrivateSeeds BellmanExpectation

variable {I : Instance} {Local Good Bad : Type*}
  [MeasurableSpace Local] [MeasurableSpace Good] [MeasurableSpace Bad]

theorem paidIndependentPolicy_someTool_upper (input : StatisticalInput I)
    (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract _)
      (zeroNormalAccounting _) available Good)
    (bad : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract _)
      (zeroNormalAccounting _) (available.erase tool) Bad) (penalty : ℝ≥0∞) :
    paidPenaltyValue input (paidRelaxedContract I) (zeroNormalAccounting I) penalty ≤
      (input.experiment head).bayesObservationCharge localLaw test +
        ((localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
          paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract _) (zeroNormalAccounting _)
            good.val.rule goodLaw penalty +
        (input.experiment head).bayesError localLaw test *
          (ENNReal.ofReal (input.fees.correction head tool : ℝ) +
            paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract _) (zeroNormalAccounting _)
              bad.val.rule badLaw penalty)) := by
  let parent := paidIndependentPolicy input head available (some tool) test good (available.erase tool) bad
  exact (paidPenaltyValue_le_policy_any_seed input (paidRelaxedContract I) (zeroNormalAccounting I)
    penalty parent.val (combinedLaw localLaw goodLaw badLaw)).trans
      (paidSomeTool_objective_le input (paidRelaxedContract I) rfl rfl rfl (zeroNormalAccounting I)
        head hhead localLaw goodLaw badLaw test available tool htool heligible good bad penalty)

theorem paidIndependentPolicy_noTool_upper (input : StatisticalInput I)
    (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw]
    (test : (input.experiment head).AdmissibleRule Local) (available : Finset I.Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract _)
      (zeroNormalAccounting _) available Good) (penalty : ℝ≥0∞) :
    paidPenaltyValue input (paidRelaxedContract I) (zeroNormalAccounting I) penalty ≤
      (input.experiment head).bayesObservationCharge localLaw test +
        ((localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
          paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract _) (zeroNormalAccounting _)
            good.val.rule goodLaw penalty +
        (input.experiment head).bayesError localLaw test * penalty) := by
  let bad : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract _)
      (zeroNormalAccounting _) available Unit :=
    ⟨abandonPolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1)) .uncapped
      (zeroNormalAccounting (I.freshSuffix 1)) Unit,
      abandonPolicy_usesOnly (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
        (zeroNormalAccounting (I.freshSuffix 1)) available Unit⟩
  let badLaw : Measure Unit := Measure.dirac ()
  let : IsProbabilityMeasure badLaw := by dsimp only [badLaw]; infer_instance
  let parent := paidIndependentPolicy input head available none test good available bad
  let bad' := pullbackAvailable (input.freshSuffix 1) _ _ available bad
    (badSeed (Local := Local) (Good := Good)) measurable_badSeed
  exact (paidPenaltyValue_le_policy_any_seed input (paidRelaxedContract I) (zeroNormalAccounting I)
    penalty parent.val (combinedLaw localLaw goodLaw badLaw)).trans
      (paidNoTool_objective_le input (paidRelaxedContract I) rfl rfl rfl (zeroNormalAccounting I)
        head hhead localLaw goodLaw badLaw test available good bad'.val.rule bad'.val.measurable_rule penalty)

end PDMenu


