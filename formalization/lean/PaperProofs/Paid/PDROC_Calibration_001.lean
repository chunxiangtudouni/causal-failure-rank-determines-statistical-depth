module

public import PaperProofs.Paid.PDMenu_CalibratedBasics_010
public import PaperProofs.Statistics.PDROC_Mixture_001
public import PaperProofs.Paid.PDROC_Surrogate_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Statistics PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

theorem calibration_observationCharge_mono (E : BinaryExperiment) {s t : ℕ∞}
    (h : s ≤ t) : E.observationCharge s ≤ E.observationCharge t := by
  by_cases ht : t = ⊤
  · simp [ht]
  · have hs : s ≠ ⊤ := ne_top_of_le_ne_top ht h
    rw [BinaryExperiment.observationCharge, ite_eq_right hs,
      BinaryExperiment.observationCharge, ite_eq_right ht]
    exact mul_le_mul' le_rfl (by exact_mod_cast ENat.toNat_le_toNat h ht)

/-- The original Q cap is pointwise below its original level-(m+1)
posterior threshold, including tapes whose threshold stop is infinity. -/
theorem calibration_cappedStop_le_threshold (P : PaperProofs.Paid.Parameters) (m : ℕ)
    (tape : P.binarySymmetric.experiment.Tape) :
    P.cappedStop m tape ≤ P.binarySymmetric.experiment.posteriorThresholdStop
      (P.binarySymmetric.endpointError (m + 1)) tape :=
  min_le_left _ _

theorem calibration_capped_expectedCharge_le (P : PaperProofs.Paid.Parameters) (m : ℕ) (x : Bool) :
    P.binarySymmetric.experiment.expectedObservationCharge fairGuessLaw (P.cappedTest m) x ≤
      ENNReal.ofReal (P.binarySymmetric.endpointCharge (m + 1) : ℝ) := by
  have hpoint (sample : Bool × P.binarySymmetric.experiment.Tape) :
      P.binarySymmetric.experiment.observationCharge ((P.cappedTest m).rule.stop sample.1 sample.2) ≤
        P.binarySymmetric.experiment.observationCharge
          ((P.binarySymmetric.hittingTestOnBool (m + 1)).rule.stop sample.1 sample.2) := by
    apply calibration_observationCharge_mono
    exact calibration_cappedStop_le_threshold P m sample.2
  calc
    _ ≤ P.binarySymmetric.experiment.expectedObservationCharge fairGuessLaw
        (P.binarySymmetric.hittingTestOnBool (m + 1)) x := lintegral_mono hpoint
    _ = _ := (hittingTestOnBool_expectedCharge P.binarySymmetric (m + 1) x).trans
      (P.binarySymmetric.symmetricHitting_expectedCharge_eq (m + 1) (by omega) x)

/-- The actual original two-coin law integrates its capped branch with
weight clipped omega and its mutually exclusive blind branch with zero cost. -/
theorem calibratedTest_expectedCharge_mix (P : PaperProofs.Paid.Parameters) (m : ℕ)
    (hm : m ≠ 0) (x : Bool) :
    P.binarySymmetric.experiment.expectedObservationCharge (P.calibrationSeedLaw m) (P.calibratedTest m) x =
      ENNReal.ofReal (P.clippedCalibrationWeight m).val *
        P.binarySymmetric.experiment.expectedObservationCharge fairGuessLaw (P.cappedTest m) x := by
  have hf : Measurable (fun sample : (Bool × Bool) × P.binarySymmetric.experiment.Tape =>
      P.binarySymmetric.experiment.observationCharge ((P.calibratedTest m).rule.stop sample.1 sample.2)) :=
    (measurable_of_countable P.binarySymmetric.experiment.observationCharge).comp
      (P.calibratedTest m).measurable_stop
  simpa only [BinaryExperiment.expectedObservationCharge, PaperProofs.Paid.Parameters.calibrationSeedLaw,
    adjacentMixtureSeedLaw, PaperProofs.Paid.Parameters.calibratedTest, hm, ite_false,
    ↓reduceIte, Bool.false_eq_true, fairGuessTest, BinaryExperiment.observationCharge_zero,
    lintegral_zero, mul_zero, add_zero] using
    lintegral_initialMixture P.binarySymmetric (P.clippedCalibrationWeight m) x _ hf

/-- P-only D24 charge bound; no D23 tail/error result, valid-index
qualification or expectation finiteness hypothesis is required. -/
theorem calibratedTest_expectedCharge_le (P : PaperProofs.Paid.Parameters) (m : ℕ) (x : Bool) :
    P.binarySymmetric.experiment.expectedObservationCharge (P.calibrationSeedLaw m) (P.calibratedTest m) x ≤
      ENNReal.ofReal (P.binarySymmetric.endpointCharge (m + 1) : ℝ) := by
  by_cases hm : m = 0
  · subst m
    rw [PDMenu.calibratedTest_zero_expectedCharge]
    exact zero_le
  · rw [calibratedTest_expectedCharge_mix P m hm x]
    have hw : ENNReal.ofReal (P.clippedCalibrationWeight m).val ≤ 1 := by
      rw [← ENNReal.ofReal_one]
      exact ENNReal.ofReal_le_ofReal (P.clippedCalibrationWeight m).property.2
    exact (mul_le_of_le_one_left' hw).trans (calibration_capped_expectedCharge_le P m x)

theorem calibratedTest_expectedCharge_le_four (P : PaperProofs.Paid.Parameters) (m : ℕ)
    (hm : 1 ≤ m) (x : Bool) :
    P.binarySymmetric.experiment.expectedObservationCharge (P.calibrationSeedLaw m) (P.calibratedTest m) x ≤
      ENNReal.ofReal (4 * (P.binarySymmetric.endpointCharge m : ℝ)) := by
  apply (calibratedTest_expectedCharge_le P m x).trans
  apply ENNReal.ofReal_le_ofReal
  exact_mod_cast endpointCharge_succ_le_four P.binarySymmetric m hm

end PDROC
