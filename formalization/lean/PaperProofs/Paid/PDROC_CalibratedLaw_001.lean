module

public import PaperProofs.Paid.PDROC_EndpointFinal_001
public import PaperProofs.Paid.PDMenu_MenuAnalysisEndpoint_086

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open MeasureTheory
open PaperProofs.Common PaperProofs.Paid PaperProofs.Statistics
open scoped ENNReal

namespace PDROC.CalibratedLaw

/-- A probability law on Boolean decisions is determined by its error
probability for the fixed actual truth. Seeds are unrestricted measurable
types; this is a law identity, not just equality of Bayes errors. -/
theorem decisionLaw_eq_of_conditionalError_eq
    {Seed Seed' : Type*} [MeasurableSpace Seed] [MeasurableSpace Seed']
    (E : BinaryExperiment) (ν : Measure Seed) (ν' : Measure Seed')
    [IsProbabilityMeasure ν] [IsProbabilityMeasure ν']
    (test : E.AdmissibleRule Seed) (test' : E.AdmissibleRule Seed') (truth : Bool)
    (error : E.conditionalError ν test truth = E.conditionalError ν' test' truth) :
    E.decisionLaw ν test truth = E.decisionLaw ν' test' truth := by
  apply Measure.ext_of_singleton
  intro bit
  cases truth <;> cases bit
  · simpa only [E.decisionLaw_false_false] using congrArg (fun p : ℝ≥0∞ => 1 - p) error
  · simpa only [E.decisionLaw_false_true] using error
  · simpa only [E.decisionLaw_true_false] using error
  · simpa only [E.decisionLaw_true_true] using congrArg (fun p : ℝ≥0∞ => 1 - p) error

theorem calibrated_conditionalError (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) (truth : Bool) :
    P.experiment.conditionalError (P.calibrationSeedLaw level) (P.calibratedTest level) truth =
      ENNReal.ofReal (P.binarySymmetric.endpointError level : ℝ) := by
  obtain ⟨zeroError, _zeroStop, _zeroCharge, positive⟩ := PDROC.exactCalibrationClaims P
  by_cases zero : level = 0
  · subst level
    exact zeroError truth
  · obtain ⟨_weight0, _weight1, _clip, error, _stop, _charge, _four⟩ :=
      positive level (by omega) valid
    exact error truth

/-- Local calibrated and original endpoint decisions have exactly the
same law under each actual truth, including the original level-zero fair bit. -/
theorem calibrated_decisionLaw (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) (truth : Bool) :
    P.experiment.decisionLaw (P.calibrationSeedLaw level) (P.calibratedTest level) truth =
      P.experiment.decisionLaw BinarySymmetric.Parameters.fairGuessLaw
        (PDMenu.menuAnalysisTest P level) truth := by
  apply decisionLaw_eq_of_conditionalError_eq
  exact (calibrated_conditionalError P level valid truth).trans
    (PDMenu.menuAnalysisTest_conditionalError P level truth).symm

/-- The original calibrated test is pathwise bounded, without any
probabilistic performance hypothesis. -/
theorem calibrated_stop_ne_top (P : Parameters) (level : ℕ)
    (seed : Bool × Bool) (tape : P.experiment.Tape) :
    (P.calibratedTest level).rule.stop seed tape ≠ ⊤ :=
  ne_top_of_le_ne_top (ENat.natCast_ne_top _) (PDMenu.calibratedTest_stop_le P level (seed, tape))

/-- The proved D24 local charge bound at every stored valid level,
including level0 with exactly zero observations. -/
theorem calibrated_conditionalCharge_le_four (P : Parameters) (level : ℕ)
    (valid : level ≤ P.certificate.M) (truth : Bool) :
    P.experiment.expectedObservationCharge (P.calibrationSeedLaw level) (P.calibratedTest level) truth ≤
      4 * ENNReal.ofReal (P.binarySymmetric.endpointCharge level : ℝ) := by
  change P.binarySymmetric.experiment.expectedObservationCharge
    (P.calibrationSeedLaw level) (P.calibratedTest level) truth ≤ _
  obtain ⟨_zeroError, _zeroStop, zeroCharge, positive⟩ := PDROC.exactCalibrationClaims P
  by_cases zero : level = 0
  · subst level
    rw [zeroCharge truth, P.binarySymmetric.endpointCharge_zero]
    norm_num
  · obtain ⟨_weight0, _weight1, _clip, _error, _stop, charge, four⟩ :=
      positive level (by omega) valid
    have castFour : (P.binarySymmetric.endpointCharge (level + 1) : ℝ) ≤
        4 * (P.binarySymmetric.endpointCharge level : ℝ) := by exact_mod_cast four
    calc
      _ ≤ ENNReal.ofReal (P.binarySymmetric.endpointCharge (level + 1) : ℝ) := charge truth
      _ ≤ ENNReal.ofReal (4 * (P.binarySymmetric.endpointCharge level : ℝ)) := ENNReal.ofReal_le_ofReal castFour
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num)]; norm_num

end PDROC.CalibratedLaw
