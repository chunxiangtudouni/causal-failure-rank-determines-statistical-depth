module

public import PaperProofs.Star.PStar_StageProduct_011
public import PaperProofs.Common.NativeHeadTest

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Star.PStarLocalWorld012

open Common Common.Native Statistics MeasureTheory
open scoped ENNReal BigOperators

variable {I : Instance}

noncomputable def localError (input : StatisticalInput I) (stage : I.Stage)
    (test : (input.experiment stage).AdmissibleRule Unit) (localSample : input.StageSample stage) : ℝ≥0∞ :=
  if test.rule.decision () localSample.2 ≠ localSample.1 then 1 else 0

theorem measurable_localError (input : StatisticalInput I) (stage : I.Stage)
    (test : (input.experiment stage).AdmissibleRule Unit) : Measurable (localError input stage test) := by
  classical
  apply Measurable.ite _ measurable_const measurable_const
  exact (measurableSet_eq_fun
    (test.measurable_decision.comp (measurable_const.prodMk measurable_snd)) measurable_fst).compl

noncomputable def localCharge (input : StatisticalInput I) (stage : I.Stage)
    (test : (input.experiment stage).AdmissibleRule Unit) (localSample : input.StageSample stage) : ℝ≥0∞ :=
  (input.experiment stage).observationCharge (test.rule.stop () localSample.2)

theorem measurable_localCharge (input : StatisticalInput I) (stage : I.Stage)
    (test : (input.experiment stage).AdmissibleRule Unit) : Measurable (localCharge input stage test) :=
  (measurable_of_countable (input.experiment stage).observationCharge).comp
    (test.measurable_stop.comp (measurable_const.prodMk measurable_snd))

theorem lintegral_localCoordinate (input : StatisticalInput I) (stage : I.Stage)
    (f : input.StageSample stage → ℝ≥0∞) (measurable : Measurable f) :
    (∫⁻ sample : Unit × input.World, f (sample.2 stage) ∂input.seededWorldLaw (Measure.dirac ())) =
      ∫⁻ localSample, f localSample ∂input.stageLaw stage := by
  have worldMeasurable := measurable.comp (measurable_pi_apply stage)
  rw [StatisticalInput.seededWorldLaw]
  calc
    _ = ∫⁻ _seed : Unit, ∫⁻ world : input.World, f (world stage) ∂input.worldLaw ∂Measure.dirac () :=
      lintegral_prod (fun sample : Unit × input.World => f (sample.2 stage))
        (worldMeasurable.comp measurable_snd).aemeasurable
    _ = ∫⁻ world : input.World, f (world stage) ∂input.worldLaw := by
      simp only [lintegral_const, measure_univ, mul_one]
    _ = _ := by
      rw [← lintegral_map measurable (measurable_pi_apply stage), input.worldLaw_coordinate]

theorem lintegral_localError (input : StatisticalInput I) (stage : I.Stage)
    (test : (input.experiment stage).AdmissibleRule Unit) :
    (∫⁻ localSample, localError input stage test localSample ∂input.stageLaw stage) =
      (input.experiment stage).bayesError (Measure.dirac ()) test := by
  rw [← lintegral_localCoordinate input stage _ (measurable_localError input stage test),
    bayesError_eq_seededWorld_integral]
  apply lintegral_congr
  intro sample
  cases sample.1
  rfl

theorem lintegral_localCharge (input : StatisticalInput I) (stage : I.Stage)
    (test : (input.experiment stage).AdmissibleRule Unit) :
    (∫⁻ localSample, localCharge input stage test localSample ∂input.stageLaw stage) =
      (input.experiment stage).bayesObservationCharge (Measure.dirac ()) test := by
  rw [← lintegral_localCoordinate input stage _ (measurable_localCharge input stage test),
    bayesObservationCharge_eq_seededWorld_integral]
  apply lintegral_congr
  intro sample
  cases sample.1
  rfl

set_option backward.isDefEq.respectTransparency.types false in
theorem realTarget_localError_le (P : PaperProofs.Star.Parameters) (order : Order)
    (stage : (starInstance P.tools order).Stage) (target : ℝ) (positive : 0 < target)
    (half : target < 1 / 2) :
    (∫⁻ localSample, localError (P.input order) stage
      (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel target)) localSample
      ∂(P.input order).stageLaw stage) ≤ ENNReal.ofReal target := by
  rw [lintegral_localError]
  change P.channel.experiment.bayesError (Measure.dirac ()) _ ≤ _
  calc
    _ ≤ ∑ truth : Bool, P.channel.experiment.priorMass truth * ENNReal.ofReal target := by
      apply Finset.sum_le_sum
      intro truth _member
      exact mul_le_mul' le_rfl (PStarLR.realTarget_test_performance P.channel positive half truth).2.1
    _ = _ := by rw [← Finset.sum_mul, P.channel.experiment.priorMass_sum, one_mul]

set_option backward.isDefEq.respectTransparency.types false in
theorem realTarget_localCharge_le (P : PaperProofs.Star.Parameters) (order : Order)
    (stage : (starInstance P.tools order).Stage) (target : ℝ) (positive : 0 < target)
    (half : target < 1 / 2) :
    (∫⁻ localSample, localCharge (P.input order) stage
      (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel target)) localSample
      ∂(P.input order).stageLaw stage) ≤
        ENNReal.ofReal (P.channel.a * (Real.log (1 / target) + P.channel.h)) := by
  rw [lintegral_localCharge]
  change P.channel.experiment.bayesObservationCharge (Measure.dirac ()) _ ≤ _
  calc
    _ ≤ ∑ truth : Bool, P.channel.experiment.priorMass truth *
        ENNReal.ofReal (P.channel.a * (Real.log (1 / target) + P.channel.h)) := by
      apply Finset.sum_le_sum
      intro truth _member
      exact mul_le_mul' le_rfl (PStarLR.realTarget_test_performance P.channel positive half truth).2.2
    _ = _ := by rw [← Finset.sum_mul, P.channel.experiment.priorMass_sum, one_mul]

end PaperProofs.Star.PStarLocalWorld012

