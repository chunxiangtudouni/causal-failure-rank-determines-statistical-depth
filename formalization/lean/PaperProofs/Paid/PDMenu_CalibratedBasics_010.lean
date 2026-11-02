module

public import PaperProofs.Paid.PDMenu_CalibrationMarks_005

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal

namespace PDMenu

open PaperProofs PaperProofs.Paid PaperProofs.Paid.Parameters

theorem calibratedTest_zero_stop (P : Parameters) (sample : (Bool × Bool) × P.binarySymmetric.experiment.Tape) :
    (P.calibratedTest 0).rule.stop sample.1 sample.2 = 0 := by
  simp [calibratedTest, Statistics.BinarySymmetric.Parameters.fairGuessTest]

theorem calibratedTest_zero_decision (P : Parameters) (sample : (Bool × Bool) × P.binarySymmetric.experiment.Tape) :
    (P.calibratedTest 0).rule.decision sample.1 sample.2 = sample.1.2 := by
  simp [calibratedTest, Statistics.BinarySymmetric.Parameters.fairGuessTest]

theorem calibratedTest_stop_le (P : Parameters) (m : ℕ)
    (sample : (Bool × Bool) × P.binarySymmetric.experiment.Tape) :
    (P.calibratedTest m).rule.stop sample.1 sample.2 ≤ P.certificate.Q := by
  by_cases hm : m = 0
  · subst m
    rw [calibratedTest_zero_stop]
    exact zero_le
  · cases hmark : sample.1.1
    · simp [calibratedTest, hmark, Statistics.BinarySymmetric.Parameters.fairGuessTest]
    · simpa only [calibratedTest, hm, ite_false, hmark, ite_true, cappedTest] using P.cappedStop_le m sample.2

theorem calibratedTest_zero_conditionalError (P : Parameters) (x : Bool) :
    P.binarySymmetric.experiment.conditionalError (P.calibrationSeedLaw 0) (P.calibratedTest 0) x =
      ENNReal.ofReal (P.binarySymmetric.endpointError 0 : ℝ) := by
  have hevent : {sample : (Bool × Bool) × P.binarySymmetric.experiment.Tape |
      (P.calibratedTest 0).rule.decision sample.1 sample.2 ≠ x} =
      (Set.univ ×ˢ {bit : Bool | bit ≠ x}) ×ˢ Set.univ := by
    ext sample
    simp only [calibratedTest_zero_decision, Set.mem_ofPred_eq, Set.mem_prod, Set.mem_univ, true_and, and_true]
  unfold Statistics.BinaryExperiment.conditionalError Statistics.BinaryExperiment.conditionalLaw
  rw [hevent]
  simp only [calibrationSeedLaw, Measure.prod_prod, measure_univ, one_mul, mul_one,
    P.binarySymmetric.endpointError_zero]
  cases x <;> norm_num [Statistics.BinarySymmetric.Parameters.fairGuessLaw,
    Statistics.BinarySymmetric.Parameters.rocCoinLaw]

theorem calibratedTest_zero_expectedCharge (P : Parameters) (x : Bool) :
    P.binarySymmetric.experiment.expectedObservationCharge (P.calibrationSeedLaw 0) (P.calibratedTest 0) x = 0 := by
  unfold Statistics.BinaryExperiment.expectedObservationCharge
  simp only [calibratedTest_zero_stop, Statistics.BinaryExperiment.observationCharge]
  simp

end PDMenu
