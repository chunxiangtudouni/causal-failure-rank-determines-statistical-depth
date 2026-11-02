module

public import PaperProofs.Paid.PDROC_Calibration_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Statistics PaperProofs.Paid
open PaperProofs.Statistics.BinarySymmetric.Parameters

namespace PDROC

theorem calibrationWeight_bounds_of_lt (P : PaperProofs.Paid.Parameters) (m : ℕ)
    (hm : 1 ≤ m) (hq : P.cappedError m < P.binarySymmetric.endpointError m) :
    0 ≤ P.calibrationWeight m ∧ P.calibrationWeight m ≤ 1 := by
  have hp := P.binarySymmetric.endpointError_lt_half hm
  have hd : 0 < (1 / 2 : ℚ) - P.cappedError m := by linarith
  unfold PaperProofs.Paid.Parameters.calibrationWeight
  exact ⟨div_nonneg (by linarith) hd.le, (div_le_one hd).mpr (by linarith)⟩

theorem clippedCalibrationWeight_eq_of_bounds (P : PaperProofs.Paid.Parameters) (m : ℕ)
    (hw0 : 0 ≤ P.calibrationWeight m) (hw1 : P.calibrationWeight m ≤ 1) :
    (P.clippedCalibrationWeight m).val = (P.calibrationWeight m : ℝ) := by
  have h0 : 0 ≤ (P.calibrationWeight m : ℝ) := by exact_mod_cast hw0
  have h1 : (P.calibrationWeight m : ℝ) ≤ 1 := by exact_mod_cast hw1
  change max 0 (min 1 (P.calibrationWeight m : ℝ)) = _
  rw [min_eq_right h1, max_eq_right h0]

theorem calibrationWeight_error_interpolation (P : PaperProofs.Paid.Parameters) (m : ℕ)
    (hm : 1 ≤ m) (hq : P.cappedError m < P.binarySymmetric.endpointError m) :
    P.calibrationWeight m * P.cappedError m + (1 - P.calibrationWeight m) * (1 / 2) =
      P.binarySymmetric.endpointError m := by
  have hp := P.binarySymmetric.endpointError_lt_half hm
  have hd : (1 / 2 : ℚ) - P.cappedError m ≠ 0 := ne_of_gt (by linarith)
  have hw : P.calibrationWeight m * ((1 / 2 : ℚ) - P.cappedError m) =
      (1 / 2 : ℚ) - P.binarySymmetric.endpointError m := div_mul_cancel₀ _ hd
  nlinarith only [hw]

/-- Exact error under the original independent mark/tie law, separately
for arbitrary actual truth x. No DP/error hypothesis enters this mixture identity. -/
theorem calibratedTest_conditionalError_mix (P : PaperProofs.Paid.Parameters) (m : ℕ)
    (hm : m ≠ 0) (x : Bool) :
    P.binarySymmetric.experiment.conditionalError (P.calibrationSeedLaw m) (P.calibratedTest m) x =
      ENNReal.ofReal (P.clippedCalibrationWeight m).val *
        P.binarySymmetric.experiment.conditionalError fairGuessLaw (P.cappedTest m) x +
      ENNReal.ofReal (1 - (P.clippedCalibrationWeight m).val) * ENNReal.ofReal (1 / 2 : ℝ) := by
  let A : Set ((Bool × Bool) × P.binarySymmetric.experiment.Tape) :=
    {sample | (P.calibratedTest m).rule.decision sample.1 sample.2 ≠ x}
  have hA : MeasurableSet A :=
    ((P.calibratedTest m).measurable_decision (measurableSet_singleton x)).compl
  let f : (Bool × Bool) × P.binarySymmetric.experiment.Tape → ℝ≥0∞ := A.indicator 1
  have hf : Measurable f := measurable_const.indicator hA
  have hT : (fun sample : Bool × P.binarySymmetric.experiment.Tape => f ((true, sample.1), sample.2)) =
      {sample : Bool × P.binarySymmetric.experiment.Tape |
        (P.cappedTest m).rule.decision sample.1 sample.2 ≠ x}.indicator 1 := by
    funext sample
    simp [f, A, Set.indicator, PaperProofs.Paid.Parameters.calibratedTest, hm]
  have hF : (fun sample : Bool × P.binarySymmetric.experiment.Tape => f ((false, sample.1), sample.2)) =
      {sample : Bool × P.binarySymmetric.experiment.Tape |
        (P.binarySymmetric.fairGuessTest).rule.decision sample.1 sample.2 ≠ x}.indicator 1 := by
    funext sample
    simp [f, A, Set.indicator, PaperProofs.Paid.Parameters.calibratedTest]
  have hEc : MeasurableSet {sample : Bool × P.binarySymmetric.experiment.Tape |
      (P.cappedTest m).rule.decision sample.1 sample.2 ≠ x} :=
    ((P.cappedTest m).measurable_decision (measurableSet_singleton x)).compl
  have hEf : MeasurableSet {sample : Bool × P.binarySymmetric.experiment.Tape |
      (P.binarySymmetric.fairGuessTest).rule.decision sample.1 sample.2 ≠ x} :=
    ((P.binarySymmetric.fairGuessTest).measurable_decision (measurableSet_singleton x)).compl
  have h := lintegral_initialMixture P.binarySymmetric (P.clippedCalibrationWeight m) x f hf
  rw [hT, hF] at h
  rw [lintegral_indicator_one hA, lintegral_indicator_one hEc, lintegral_indicator_one hEf] at h
  change P.binarySymmetric.experiment.conditionalError (P.calibrationSeedLaw m) (P.calibratedTest m) x =
    ENNReal.ofReal (P.clippedCalibrationWeight m).val *
      P.binarySymmetric.experiment.conditionalError fairGuessLaw (P.cappedTest m) x +
    ENNReal.ofReal (1 - (P.clippedCalibrationWeight m).val) *
      P.binarySymmetric.experiment.conditionalError fairGuessLaw P.binarySymmetric.fairGuessTest x at h
  rw [P.binarySymmetric.fairGuess_conditionalError] at h
  exact h

/-- Once the original D23 capped-error law and strict room hold, clipping
is inactive and both actual truth-conditional calibrated errors equal p_m. -/
theorem calibratedTest_conditionalError_exact_of_capped (P : PaperProofs.Paid.Parameters) (m : ℕ)
    (hm : 1 ≤ m) (hq0 : 0 ≤ P.cappedError m)
    (hq : P.cappedError m < P.binarySymmetric.endpointError m)
    (herror : ∀ x : Bool, P.binarySymmetric.experiment.conditionalError fairGuessLaw (P.cappedTest m) x =
      ENNReal.ofReal (P.cappedError m : ℝ)) (x : Bool) :
    P.binarySymmetric.experiment.conditionalError (P.calibrationSeedLaw m) (P.calibratedTest m) x =
      ENNReal.ofReal (P.binarySymmetric.endpointError m : ℝ) := by
  obtain ⟨hw0, hw1⟩ := calibrationWeight_bounds_of_lt P m hm hq
  have hclip := clippedCalibrationWeight_eq_of_bounds P m hw0 hw1
  have h0 : 0 ≤ (P.calibrationWeight m : ℝ) := by exact_mod_cast hw0
  have h1 : (P.calibrationWeight m : ℝ) ≤ 1 := by exact_mod_cast hw1
  have hqr : 0 ≤ (P.cappedError m : ℝ) := by exact_mod_cast hq0
  rw [calibratedTest_conditionalError_mix P m (by omega) x, herror x, hclip,
    ← ENNReal.ofReal_mul h0, ← ENNReal.ofReal_mul (sub_nonneg.mpr h1),
    ← ENNReal.ofReal_add (mul_nonneg h0 hqr) (mul_nonneg (sub_nonneg.mpr h1) (by norm_num))]
  congr 1
  have hinterp := congrArg (fun value : ℚ => (value : ℝ))
    (calibrationWeight_error_interpolation P m hm hq)
  push_cast at hinterp ⊢
  exact hinterp

/-- This is a conditional assembly from exactly the original D23 target.
It is not an unconditional proof of D24 until actual D23 is supplied. -/
theorem exactCalibrationClaims_of_boundedEndpointClaims (P : PaperProofs.Paid.Parameters)
    (h23 : P.BoundedEndpointClaims) : P.ExactCalibrationClaims := by
  refine ⟨PDMenu.calibratedTest_zero_conditionalError P,
    PDMenu.calibratedTest_zero_stop P, PDMenu.calibratedTest_zero_expectedCharge P, ?_⟩
  intro m hm hM
  obtain ⟨_htail, _hE, _hexp, _hpow, herror, hq0, _hlogistic, _hqbound, _hgap, hq⟩ := h23 m hm hM
  obtain ⟨hw0, hw1⟩ := calibrationWeight_bounds_of_lt P m hm hq
  exact ⟨hw0, hw1, clippedCalibrationWeight_eq_of_bounds P m hw0 hw1,
    calibratedTest_conditionalError_exact_of_capped P m hm hq0 hq herror,
    PDMenu.calibratedTest_stop_le P m, calibratedTest_expectedCharge_le P m,
    endpointCharge_succ_le_four P.binarySymmetric m hm⟩

end PDROC
