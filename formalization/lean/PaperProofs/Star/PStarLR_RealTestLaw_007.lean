module

public import PaperProofs.Star.PStarLR_RealThreshold_004

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Statistics PaperProofs.Statistics.BinarySymmetric PaperProofs.Star

namespace PStarLR

theorem realTarget_test_decision (channel : BinarySymmetric.Parameters) (r : ℝ)
    (tape : channel.experiment.Tape) (n : ℕ)
    (stop : realPosteriorStop channel.experiment r tape = n) :
    (channel.symmetricHittingTest (realTargetIndex channel r)).rule.decision () tape =
      decide (0 ≤ channel.experiment.logOddsScore tape n) := by
  have originalStop : (channel.symmetricHittingTest (realTargetIndex channel r)).rule.stop () tape = n :=
    (realPosteriorStop_eq_hitting channel r tape).symm.trans stop
  exact (channel.experiment.posteriorSPRT_isPosteriorThresholdRule
    (channel.endpointError (realTargetIndex channel r))).2 tape n originalStop

theorem realTarget_test_performance (channel : BinarySymmetric.Parameters) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) (truth : Bool) :
    channel.experiment.expectedSamples (Measure.dirac ())
        (channel.symmetricHittingTest (realTargetIndex channel r)) truth ≠ ⊤ ∧
      channel.experiment.conditionalError (Measure.dirac ())
        (channel.symmetricHittingTest (realTargetIndex channel r)) truth ≤ ENNReal.ofReal r ∧
      channel.experiment.expectedObservationCharge (Measure.dirac ())
        (channel.symmetricHittingTest (realTargetIndex channel r)) truth ≤
          ENNReal.ofReal (channel.a * (Real.log (1/r) + channel.h)) := by
  have positive := realTargetIndex_pos channel hr hrhalf
  refine ⟨channel.symmetricHittingTest_expectedSamples_finite _ truth, ?_, ?_⟩
  · rw [channel.symmetricHitting_conditionalError_eq _ positive truth]
    exact ENNReal.ofReal_le_ofReal (realTargetIndex_endpoint_le channel hr hrhalf)
  · rw [channel.symmetricHitting_expectedCharge_eq _ positive truth]
    exact ENNReal.ofReal_le_ofReal (realTargetIndex_charge_le channel hr hrhalf)

end PStarLR
