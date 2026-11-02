module

public import PaperProofs.Paid.PDMenu_SuffixActualCharge_008
public import PaperProofs.Common.NativeBellmanExpectation

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Paid
open BellmanPrivateSeeds BellmanExpectation

attribute [local instance] Classical.propDecidable

variable {I : Instance}
variable {Local Good Bad : Type*} [MeasurableSpace Local] [MeasurableSpace Good] [MeasurableSpace Bad]

theorem runPaidPenaltyCharge_pullbackAvailable {Large Small : Type*}
    [MeasurableSpace Large] [MeasurableSpace Small]
    (input : StatisticalInput I) (C : Contract I) (accounting : NormalAccounting I)
    (available : Finset I.Tool) (policy : AvailablePolicy input C accounting available Small)
    (f : Large → Small) (hf : Measurable f) (penalty : ℝ≥0∞) (sample : Large × input.World) :
    runPaidPenaltyCharge input C accounting
      (pullbackAvailable input C accounting available policy f hf).val.rule penalty sample =
      runPaidPenaltyCharge input C accounting policy.val.rule penalty (f sample.1, sample.2) := by
  simp only [runPaidPenaltyCharge, runActualBill, run_pullbackAvailable, runSuccess_pullbackAvailable]

theorem selectedPaidPolicyCharges_integral (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local)
    (goodAvailable badAvailable : Finset (I.freshSuffix 1).Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) goodAvailable Good)
    (bad : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) badAvailable Bad) (penalty : ℝ≥0∞) :
    (∫⁻ sample, if (pullbackTest (input.experiment head) test localSeed measurable_localSeed).rule.decision
        sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
        runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1))
          (pullbackAvailable (input.freshSuffix 1) _ _ goodAvailable good goodSeed measurable_goodSeed).val.rule
          penalty (sample.1, referenceSuffixWorld input 1 sample.2)
      else runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
        (zeroNormalAccounting (I.freshSuffix 1))
        (pullbackAvailable (input.freshSuffix 1) _ _ badAvailable bad badSeed measurable_badSeed).val.rule
        penalty (sample.1, referenceSuffixWorld input 1 sample.2)
      ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw)) =
      (localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
        paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw penalty +
      (input.experiment head).bayesError localLaw test *
        paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule badLaw penalty := by
  simp only [runPaidPenaltyCharge_pullbackAvailable]
  rw [paidPenaltyObjective_eq_lintegral _ _ _ _ good.val.measurable_rule,
    paidPenaltyObjective_eq_lintegral _ _ _ _ bad.val.measurable_rule,
    ← wrongMass_eq_bayesError input head localLaw test]
  exact selectedTestBranches_integral input head hhead localLaw goodLaw badLaw test
    _ (measurable_runPaidPenaltyCharge _ _ _ _ good.val.measurable_rule penalty)
    _ (measurable_runPaidPenaltyCharge _ _ _ _ bad.val.measurable_rule penalty)


end PDMenu
