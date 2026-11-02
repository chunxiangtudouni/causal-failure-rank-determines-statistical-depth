module

public import PaperProofs.Retained.PRet_FreshIndependentPolicy_112
public import PaperProofs.Common.NativeBellmanExpectation
public import PaperProofs.Common.NativeBellmanFiniteStop

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFreshExpectation113

open Common Common.Native MeasureTheory PRetAmbientComparator073 PRetJointCharges075
open PRetFreshIndependentPolicy112 BellmanPrivateSeeds BellmanExpectation
open scoped ENNReal

variable {I Ambient : Instance} {Local Good Bad : Type*}
variable [MeasurableSpace Local] [MeasurableSpace Good] [MeasurableSpace Bad]

/-- Tonelli assembly of the REAL three-seed retained-aware Policy.
Finite local stopping is DERIVED from its finite local objective; child
charges and failed/nonreturn paths may remain infinite. -/
theorem independent_objective_upper (input : StatisticalInput I) (head : I.Stage) (hhead : head.val = 0)
    (localLaw : Measure Local) (goodLaw : Measure Good) (badLaw : Measure Bad)
    [IsProbabilityMeasure localLaw] [IsProbabilityMeasure goodLaw] [IsProbabilityMeasure badLaw]
    (test : (input.experiment head).AdmissibleRule Local)
    (good : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1)) Good)
    (bad : Policy (input.freshSuffix 1) (freshContract (I.freshSuffix 1)) .uncapped (zeroNormalAccounting (I.freshSuffix 1)) Bad)
    (embed : I.Stage → Ambient.Stage) (old : Finset Ambient.Stage)
    (testPrice penalty : ENNReal) (hfinite : (input.experiment head).bayesObjective localLaw test testPrice ≠ ⊤) :
    jointObjective input embed old (independentPolicy input head test good bad).rule (combinedLaw localLaw goodLaw badLaw) penalty ≤
      (input.experiment head).bayesObservationCharge localLaw test +
        (localLaw.prod (input.stageLaw head)) (headCorrectGate input head test) *
          jointObjective (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) old good.rule goodLaw penalty +
        (input.experiment head).bayesError localLaw test *
          jointObjective (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) (insert (embed head) old) bad.rule badLaw penalty := by
  classical
  let ν := combinedLaw localLaw goodLaw badLaw
  let test' := pullbackTest (Large := CombinedSeed Local Good Bad) (input.experiment head) test localSeed measurable_localSeed
  let policy := independentPolicy input head test good bad
  let obs := fun sample : CombinedSeed Local Good Bad × input.World => (input.experiment head).observationCharge
    (test'.rule.stop sample.1 (worldTapes input sample.2 head))
  let goodCost := jointCharge (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) old good.rule penalty
  let badCost := jointCharge (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) (insert (embed head) old) bad.rule penalty
  let selected := fun sample : CombinedSeed Local Good Bad × input.World =>
    if test'.rule.decision sample.1 (worldTapes input sample.2 head) = input.truthAt sample.2 head then
      goodCost (goodSeed sample.1, referenceSuffixWorld input 1 sample.2)
    else badCost (badSeed sample.1, referenceSuffixWorld input 1 sample.2)
  have hfinite' : (input.experiment head).bayesObjective ν test' testPrice ≠ ⊤ := by
    rw [localObjective_combinedLaw localLaw goodLaw badLaw]
    exact hfinite
  have hstop := localTest_exists_stop_seededWorld input head ν test' testPrice hfinite'
  have hpoint : ∀ᵐ sample ∂input.seededWorldLaw ν,
      jointCharge input embed old policy.rule penalty sample ≤ obs sample + selected sample := by
    filter_upwards [hstop] with sample hs
    obtain ⟨n, hn⟩ := hs
    exact PRetFreshIndependentPolicy112.charge_at_testStop input head hhead test good bad embed old sample n hn penalty
  have hmObs : Measurable obs := (measurable_of_countable (input.experiment head).observationCharge).comp
    (test'.measurable_stop.comp (measurable_fst.prodMk (((measurable_pi_apply head).comp measurable_snd).snd)))
  have hmGood : Measurable goodCost := measurable_jointCharge _ _ _ _ good.measurable_rule penalty
  have hmBad : Measurable badCost := measurable_jointCharge _ _ _ _ bad.measurable_rule penalty
  have hbranches := selectedTestBranches_integral input head hhead localLaw goodLaw badLaw test goodCost hmGood badCost hmBad
  have hgoodIntegral : (∫⁻ child, goodCost child ∂goodLaw.prod (input.freshSuffix 1).worldLaw) =
      jointObjective (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) old good.rule goodLaw penalty :=
    (jointObjective_eq_lintegral _ _ _ _ good.measurable_rule goodLaw penalty).symm
  have hbadIntegral : (∫⁻ child, badCost child ∂badLaw.prod (input.freshSuffix 1).worldLaw) =
      jointObjective (input.freshSuffix 1) (fun stage => embed (I.freshStageLift 1 stage)) (insert (embed head) old) bad.rule badLaw penalty :=
    (jointObjective_eq_lintegral _ _ _ _ bad.measurable_rule badLaw penalty).symm
  rw [hgoodIntegral, hbadIntegral, wrongMass_eq_bayesError input head localLaw test] at hbranches
  change (∫⁻ sample, selected sample ∂input.seededWorldLaw ν) = _ at hbranches
  have hobsIntegral : (∫⁻ sample, obs sample ∂input.seededWorldLaw ν) =
      (input.experiment head).bayesObservationCharge localLaw test :=
    headObservation_integral input head localLaw goodLaw badLaw test
  change jointObjective input embed old policy.rule ν penalty ≤ _
  rw [jointObjective_eq_lintegral _ _ _ _ policy.measurable_rule]
  calc
    _ ≤ ∫⁻ sample, obs sample + selected sample ∂input.seededWorldLaw ν := lintegral_mono_ae hpoint
    _ = (∫⁻ sample, obs sample ∂input.seededWorldLaw ν) + ∫⁻ sample, selected sample ∂input.seededWorldLaw ν :=
      lintegral_add_left hmObs _
    _ = _ := by
      rw [hobsIntegral, hbranches, add_assoc]

end PaperProofs.Retained.PRetFreshExpectation113
