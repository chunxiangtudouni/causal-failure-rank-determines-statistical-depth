module

public import PaperProofs.Paid.PDMenu_PaidHeadPointwise_019
public import PaperProofs.Paid.PDMenu_PaidBranchExpectation_017

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

theorem selectedPaidPolicyCharges_withFee_integral (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local)
    (goodAvailable badAvailable : Finset (I.freshSuffix 1).Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) goodAvailable Good)
    (bad : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) badAvailable Bad) (fee penalty : ℝ≥0∞) :
    (∫⁻ sample, if (pullbackTest (input.experiment head) test localSeed measurable_localSeed).rule.decision
        sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
        runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1))
          (pullbackAvailable (input.freshSuffix 1) _ _ goodAvailable good goodSeed measurable_goodSeed).val.rule
          penalty (sample.1, referenceSuffixWorld input 1 sample.2)
      else fee + runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
        (zeroNormalAccounting (I.freshSuffix 1))
        (pullbackAvailable (input.freshSuffix 1) _ _ badAvailable bad badSeed measurable_badSeed).val.rule
        penalty (sample.1, referenceSuffixWorld input 1 sample.2)
      ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw)) =
      (localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
        paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw penalty +
      (input.experiment head).bayesError localLaw test *
        (fee + paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule badLaw penalty) := by
  simp only [runPaidPenaltyCharge_pullbackAvailable]
  rw [paidPenaltyObjective_eq_lintegral _ _ _ _ good.val.measurable_rule,
    paidPenaltyObjective_eq_lintegral _ _ _ _ bad.val.measurable_rule,
    ← wrongMass_eq_bayesError input head localLaw test]
  have h := selectedTestBranches_integral input head hhead localLaw goodLaw badLaw test
    (runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule penalty)
    (measurable_runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule good.val.measurable_rule penalty)
    (fun sample => fee + runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule penalty sample)
    (measurable_const.add (measurable_runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule bad.val.measurable_rule penalty))
  simpa only [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
    StatisticalInput.seededWorldLaw] using h

theorem selectedPaidGoodOrPenalty_integral (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local)
    (goodAvailable : Finset (I.freshSuffix 1).Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) goodAvailable Good) (penalty : ℝ≥0∞) :
    (∫⁻ sample, if (pullbackTest (input.experiment head) test localSeed measurable_localSeed).rule.decision
        sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
        runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1))
          (pullbackAvailable (input.freshSuffix 1) _ _ goodAvailable good goodSeed measurable_goodSeed).val.rule
          penalty (sample.1, referenceSuffixWorld input 1 sample.2)
      else penalty ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw)) =
      (localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
        paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw penalty +
      (input.experiment head).bayesError localLaw test * penalty := by
  simp only [runPaidPenaltyCharge_pullbackAvailable]
  rw [paidPenaltyObjective_eq_lintegral _ _ _ _ good.val.measurable_rule,
    ← wrongMass_eq_bayesError input head localLaw test]
  have h := selectedTestBranches_integral input head hhead localLaw goodLaw badLaw test
    (runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule penalty)
    (measurable_runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule good.val.measurable_rule penalty)
    (fun _ => penalty) measurable_const
  simpa only [lintegral_const, measure_univ, mul_one, StatisticalInput.seededWorldLaw] using h

theorem paidSomeTool_objective_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (hpayment : C.execution = .currentWindow) (accounting : NormalAccounting I)
    (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local) (available : Finset I.Tool)
    (tool : I.Tool) (htool : tool ∈ available) (heligible : tool ∈ I.eligible head)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Good)
    (bad : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) (available.erase tool) Bad) (penalty : ℝ≥0∞) :
    let test' := pullbackTest (input.experiment head) test
      (localSeed (Good := Good) (Bad := Bad)) measurable_localSeed
    let good' := pullbackAvailable (input.freshSuffix 1) _ _ available good
      (goodSeed (Local := Local) (Bad := Bad)) measurable_goodSeed
    let bad' := pullbackAvailable (input.freshSuffix 1) _ _ (available.erase tool) bad
      (badSeed (Local := Local) (Good := Good)) measurable_badSeed
    paidPenaltyObjective input C accounting
      (paidHeadThenRule input head test' available
        (bellmanPostHeadRaw input head (some tool) good'.val.rule bad'.val.rule))
      (combinedLaw localLaw goodLaw badLaw) penalty ≤
      (input.experiment head).bayesObservationCharge localLaw test +
        ((localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
          paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
            (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw penalty +
        (input.experiment head).bayesError localLaw test *
          (ENNReal.ofReal (input.fees.correction head tool : ℝ) +
          paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
            (zeroNormalAccounting (I.freshSuffix 1)) bad.val.rule badLaw penalty)) := by
  intro test' good' bad'
  let after := bellmanPostHeadRaw input head (some tool) good'.val.rule bad'.val.rule
  have hafter : MeasurableRule after :=
    measurable_bellmanPostHeadRaw input head (some tool) good'.val.rule bad'.val.rule
      good'.val.measurable_rule bad'.val.measurable_rule
  have hobs : Measurable (fun sample : CombinedSeed Local Good Bad × input.World =>
      (input.experiment head).observationCharge (test'.rule.stop sample.1 (worldTapes input sample.2 head))) :=
    (measurable_of_countable (input.experiment head).observationCharge).comp
      (test'.measurable_stop.comp
        (measurable_fst.prodMk (((measurable_pi_apply head).comp measurable_snd).snd)))
  change paidPenaltyObjective input C accounting (paidHeadThenRule input head test' available after)
    (combinedLaw localLaw goodLaw badLaw) penalty ≤ _
  apply (paidPenaltyObjective_eq_lintegral input C accounting (paidHeadThenRule input head test' available after)
    (paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test' available after hafter).val.measurable_rule
    (combinedLaw localLaw goodLaw badLaw) penalty).trans_le
  calc
    _ ≤ ∫⁻ sample, (input.experiment head).observationCharge
          (test'.rule.stop sample.1 (worldTapes input sample.2 head)) +
        (if test'.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
          runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
            (zeroNormalAccounting (I.freshSuffix 1)) good'.val.rule penalty
            (sample.1, referenceSuffixWorld input 1 sample.2)
        else ENNReal.ofReal (input.fees.correction head tool : ℝ) + runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
          (zeroNormalAccounting (I.freshSuffix 1)) bad'.val.rule penalty
          (sample.1, referenceSuffixWorld input 1 sample.2))
        ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw) := by
      apply lintegral_mono
      intro sample
      exact paidHeadThen_someTool_penaltyCharge_le input C hearly hcurrent hpayment accounting
        head hhead test' available tool htool heligible good' bad' sample penalty
    _ = _ := by
      rw [lintegral_add_left hobs, headObservation_integral input head localLaw goodLaw badLaw test]
      congr 1
      exact selectedPaidPolicyCharges_withFee_integral input head hhead localLaw goodLaw badLaw test
        available (available.erase tool) good bad (ENNReal.ofReal (input.fees.correction head tool : ℝ)) penalty

theorem paidNoTool_objective_le (input : StatisticalInput I) (C : Contract I)
    (hearly : C.reporting = .early) (hcurrent : C.allocation = .currentWindow)
    (hpayment : C.execution = .currentWindow) (accounting : NormalAccounting I)
    (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local) (available : Finset I.Tool)
    (good : AvailablePolicy (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
      (zeroNormalAccounting (I.freshSuffix 1)) available Good)
    (bad : PolicyRule (I.freshSuffix 1) (CombinedSeed Local Good Bad))
    (hbad : MeasurableRule bad) (penalty : ℝ≥0∞) :
    let test' := pullbackTest (input.experiment head) test
      (localSeed (Good := Good) (Bad := Bad)) measurable_localSeed
    let good' := pullbackAvailable (input.freshSuffix 1) _ _ available good
      (goodSeed (Local := Local) (Bad := Bad)) measurable_goodSeed
    paidPenaltyObjective input C accounting
      (paidHeadThenRule input head test' available
        (bellmanPostHeadRaw input head none good'.val.rule bad))
      (combinedLaw localLaw goodLaw badLaw) penalty ≤
      (input.experiment head).bayesObservationCharge localLaw test +
        ((localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
          paidPenaltyObjective (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
            (zeroNormalAccounting (I.freshSuffix 1)) good.val.rule goodLaw penalty +
        (input.experiment head).bayesError localLaw test * penalty) := by
  intro test' good'
  let after := bellmanPostHeadRaw input head none good'.val.rule bad
  have hafter : MeasurableRule after :=
    measurable_bellmanPostHeadRaw input head none good'.val.rule bad good'.val.measurable_rule hbad
  have hobs : Measurable (fun sample : CombinedSeed Local Good Bad × input.World =>
      (input.experiment head).observationCharge (test'.rule.stop sample.1 (worldTapes input sample.2 head))) :=
    (measurable_of_countable (input.experiment head).observationCharge).comp
      (test'.measurable_stop.comp
        (measurable_fst.prodMk (((measurable_pi_apply head).comp measurable_snd).snd)))
  change paidPenaltyObjective input C accounting (paidHeadThenRule input head test' available after)
    (combinedLaw localLaw goodLaw badLaw) penalty ≤ _
  apply (paidPenaltyObjective_eq_lintegral input C accounting (paidHeadThenRule input head test' available after)
    (paidHeadThenPolicy input C ⟨⟨hearly, hcurrent⟩, hpayment⟩ accounting head test' available after hafter).val.measurable_rule
    (combinedLaw localLaw goodLaw badLaw) penalty).trans_le
  calc
    _ ≤ ∫⁻ sample, (input.experiment head).observationCharge
          (test'.rule.stop sample.1 (worldTapes input sample.2 head)) +
        (if test'.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
          runPaidPenaltyCharge (input.freshSuffix 1) (paidRelaxedContract (I.freshSuffix 1))
            (zeroNormalAccounting (I.freshSuffix 1)) good'.val.rule penalty
            (sample.1, referenceSuffixWorld input 1 sample.2)
        else penalty) ∂input.seededWorldLaw (combinedLaw localLaw goodLaw badLaw) := by
      apply lintegral_mono
      intro sample
      exact paidHeadThen_noTool_penaltyCharge_le input C hearly hcurrent hpayment accounting
        head hhead test' available good' bad hbad sample penalty
    _ = _ := by
      rw [lintegral_add_left hobs, headObservation_integral input head localLaw goodLaw badLaw test]
      congr 1
      exact selectedPaidGoodOrPenalty_integral input head hhead localLaw goodLaw badLaw test available good penalty


end PDMenu
