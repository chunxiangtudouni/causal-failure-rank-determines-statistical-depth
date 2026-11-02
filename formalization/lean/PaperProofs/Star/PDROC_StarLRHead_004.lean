module

public import PaperProofs.Star.PDROC_StarLRHead_002
public import PaperProofs.Common.NativeHeadBayes

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Common.Native PaperProofs.Star

namespace PDROC.StarLRHead

noncomputable def referenceHeadTest (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ) :
    P.channel.experiment.AdmissibleRule Unit :=
  nativeHeadTest (P.input order) (firstStage P.tools order)
    (P.starReferenceRule order .lateRetained r none)
    (P.measurable_starReferenceRule order .lateRetained r none)

theorem referenceHeadTest_stop (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (seed : Unit) (tape : P.channel.experiment.Tape) :
    (referenceHeadTest P order r).rule.stop seed tape =
      (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)).rule.stop seed tape := by
  cases seed
  exact (reference_head_stop P order r tape).trans (PStarLR.realPosteriorStop_eq_hitting P.channel r tape)

theorem referenceHeadTest_expectedSamples (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (truth : Bool) :
    P.channel.experiment.expectedSamples (Measure.dirac ()) (referenceHeadTest P order r) truth =
      P.channel.experiment.expectedSamples (Measure.dirac ())
        (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)) truth := by
  unfold PaperProofs.Statistics.BinaryExperiment.expectedSamples
  apply lintegral_congr
  intro sample
  exact congrArg PaperProofs.Statistics.BinaryExperiment.sampleCountENNReal
    (referenceHeadTest_stop P order r sample.1 sample.2)

theorem referenceHeadTest_expectedCharge (P : PaperProofs.Star.Parameters) (order : Order) (r : ℝ)
    (truth : Bool) :
    P.channel.experiment.expectedObservationCharge (Measure.dirac ()) (referenceHeadTest P order r) truth =
      P.channel.experiment.expectedObservationCharge (Measure.dirac ())
        (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)) truth := by
  unfold PaperProofs.Statistics.BinaryExperiment.expectedObservationCharge
  apply lintegral_congr
  intro sample
  exact congrArg P.channel.experiment.observationCharge (referenceHeadTest_stop P order r sample.1 sample.2)

theorem referenceHeadTest_conditionalError (P : PaperProofs.Star.Parameters) (order : Order) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (truth : Bool) :
    P.channel.experiment.conditionalError (Measure.dirac ()) (referenceHeadTest P order r) truth =
      P.channel.experiment.conditionalError (Measure.dirac ())
        (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)) truth := by
  unfold PaperProofs.Statistics.BinaryExperiment.conditionalError
  apply measure_congr
  have finite := P.channel.experiment.expectedSamples_finite_stop (Measure.dirac ())
    (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)) truth
    (PStarLR.realTarget_test_performance P.channel hr hrhalf truth).1
  filter_upwards [finite] with sample finiteStop
  obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp finiteStop
  have realStop : realPosteriorStop P.channel.experiment r sample.2 = n := by
    cases sample.1
    exact (PStarLR.realPosteriorStop_eq_hitting P.channel r sample.2).trans hn.symm
  change ((referenceHeadTest P order r).rule.decision sample.1 sample.2 ≠ truth) = _
  cases sample.1
  rw [show (referenceHeadTest P order r).rule.decision () sample.2 =
      (P.channel.symmetricHittingTest (PStarLR.realTargetIndex P.channel r)).rule.decision () sample.2 from
    reference_head_decision P order r sample.2 n realStop]

theorem referenceHeadTest_performance (P : PaperProofs.Star.Parameters) (order : Order) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (truth : Bool) :
    P.channel.experiment.expectedSamples (Measure.dirac ()) (referenceHeadTest P order r) truth ≠ ⊤ ∧
      P.channel.experiment.conditionalError (Measure.dirac ()) (referenceHeadTest P order r) truth ≤ ENNReal.ofReal r ∧
      P.channel.experiment.expectedObservationCharge (Measure.dirac ()) (referenceHeadTest P order r) truth ≤
        ENNReal.ofReal (P.channel.a * (Real.log (1/r) + P.channel.h)) := by
  rw [referenceHeadTest_expectedSamples, referenceHeadTest_conditionalError P order hr hrhalf,
    referenceHeadTest_expectedCharge]
  exact PStarLR.realTarget_test_performance P.channel hr hrhalf truth

end PDROC.StarLRHead
