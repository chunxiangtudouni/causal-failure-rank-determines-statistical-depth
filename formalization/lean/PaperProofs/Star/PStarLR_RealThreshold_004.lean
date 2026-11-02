module

public import PaperProofs.Star.Claims
public import PaperProofs.Statistics.SymmetricHittingExact

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open MeasureTheory
open scoped ENNReal
open PaperProofs.Statistics PaperProofs.Statistics.BinarySymmetric PaperProofs.Star

namespace PStarLR

noncomputable def realTargetIndex (channel : BinarySymmetric.Parameters) (r : ℝ) : ℕ :=
  ⌈Real.log ((1-r)/r) / channel.h⌉₊

theorem realTargetIndex_score_iff (channel : BinarySymmetric.Parameters) (r : ℝ)
    (tape : channel.experiment.Tape) (n : ℕ) :
    Real.log ((1-r)/r) ≤ |channel.experiment.logOddsScore tape n| ↔
      realTargetIndex channel r ≤ (channel.signedSum tape n).natAbs := by
  rw [channel.abs_logOddsScore_eq]
  rw [realTargetIndex, Nat.ceil_le]
  rw [div_le_iff₀ channel.h_pos, mul_comm channel.h ((channel.signedSum tape n).natAbs : ℝ)]

theorem realPosteriorStop_eq_hitting (channel : BinarySymmetric.Parameters) (r : ℝ)
    (tape : channel.experiment.Tape) :
    realPosteriorStop channel.experiment r tape =
      (channel.symmetricHittingTest (realTargetIndex channel r)).rule.stop () tape := by
  change sInf {t : ℕ∞ | ∃ n : ℕ, t = n ∧ Real.log ((1-r)/r) ≤
      |channel.experiment.logOddsScore tape n|} =
    channel.experiment.posteriorThresholdStop (channel.endpointError (realTargetIndex channel r)) tape
  unfold BinaryExperiment.posteriorThresholdStop
  congr 1
  ext t
  apply exists_congr
  intro n
  apply and_congr_right
  intro _
  have hright : Real.log ((1-(channel.endpointError (realTargetIndex channel r) : ℝ))/
      (channel.endpointError (realTargetIndex channel r) : ℝ)) ≤
      |channel.experiment.logOddsScore tape n| ↔
      realTargetIndex channel r ≤ (channel.signedSum tape n).natAbs := by
    rw [channel.endpointThreshold, channel.abs_logOddsScore_eq,
      mul_comm (realTargetIndex channel r : ℝ) channel.h,
      mul_le_mul_iff_right₀ channel.h_pos, Nat.cast_le]
  exact (realTargetIndex_score_iff channel r tape n).trans hright.symm

theorem real_log_threshold_pos {r : ℝ} (hr : 0 < r) (hrhalf : r < 1/2) :
    0 < Real.log ((1-r)/r) := by
  apply Real.log_pos
  exact (one_lt_div hr).mpr (by linarith)

theorem realTargetIndex_pos (channel : BinarySymmetric.Parameters) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) : 1 ≤ realTargetIndex channel r := by
  exact Nat.one_le_ceil_iff.mpr (div_pos (real_log_threshold_pos hr hrhalf) channel.h_pos)

theorem realTargetIndex_threshold (channel : BinarySymmetric.Parameters) (r : ℝ) :
    Real.log ((1-r)/r) ≤ (realTargetIndex channel r : ℝ) * channel.h := by
  exact (div_le_iff₀ channel.h_pos).mp (Nat.le_ceil _)

theorem realTargetIndex_endpoint_le (channel : BinarySymmetric.Parameters) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    (channel.endpointError (realTargetIndex channel r) : ℝ) ≤ r := by
  let p : ℝ := channel.endpointError (realTargetIndex channel r)
  have hp : 0 < p := by
    dsimp only [p]
    exact_mod_cast channel.endpointError_pos (realTargetIndex channel r)
  have hphalf : p ≤ 1/2 := by
    have hh := (Rat.cast_le (K := ℝ)).mpr (channel.endpointError_le_half (realTargetIndex channel r))
    norm_num only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat] at hh
    exact hh
  have hlog : Real.log ((1-r)/r) ≤ Real.log ((1-p)/p) := by
    rw [show Real.log ((1-p)/p) = (realTargetIndex channel r : ℝ)*channel.h from
      channel.endpointThreshold (realTargetIndex channel r)]
    exact realTargetIndex_threshold channel r
  have hratio : (1-r)/r ≤ (1-p)/p := (Real.log_le_log_iff
    (div_pos (by linarith) hr) (div_pos (by linarith) hp)).mp hlog
  have hcross := (div_le_div_iff₀ hr hp).mp hratio
  change p ≤ r
  nlinarith only [hcross]

theorem realTargetIndex_charge_le (channel : BinarySymmetric.Parameters) {r : ℝ}
    (hr : 0 < r) (hrhalf : r < 1/2) :
    (channel.endpointCharge (realTargetIndex channel r) : ℝ) ≤
      channel.a * (Real.log (1/r) + channel.h) := by
  have hlogpos := real_log_threshold_pos hr hrhalf
  have hceil := Nat.ceil_lt_add_one (div_nonneg hlogpos.le channel.h_pos.le)
  change (realTargetIndex channel r : ℝ) < Real.log ((1-r)/r)/channel.h + 1 at hceil
  have hheight : (realTargetIndex channel r : ℝ)*channel.h ≤ Real.log ((1-r)/r)+channel.h := by
    have hh := mul_lt_mul_of_pos_right hceil channel.h_pos
    rw [add_mul, div_mul_cancel₀ _ channel.h_pos.ne', one_mul] at hh
    exact hh.le
  have hlogle : Real.log ((1-r)/r) ≤ Real.log (1/r) := by
    apply Real.log_le_log (div_pos (by linarith) hr)
    exact div_le_div_of_nonneg_right (by linarith) hr.le
  rw [channel.endpointCharge_eq_information, BinarySymmetric.phiReal, channel.endpointThreshold]
  have hp : 0 ≤ (channel.endpointError (realTargetIndex channel r) : ℝ) := by
    exact_mod_cast (channel.endpointError_pos (realTargetIndex channel r)).le
  have hm : 0 ≤ (realTargetIndex channel r : ℝ)*channel.h := mul_nonneg (Nat.cast_nonneg _) channel.h_pos.le
  apply mul_le_mul_of_nonneg_left _ channel.a_pos.le
  calc
    (1-2*(channel.endpointError (realTargetIndex channel r) : ℝ)) *
        ((realTargetIndex channel r : ℝ)*channel.h) ≤
      (realTargetIndex channel r : ℝ)*channel.h := by nlinarith only [mul_nonneg hp hm]
    _ ≤ Real.log ((1-r)/r)+channel.h := hheight
    _ ≤ Real.log (1/r)+channel.h := add_le_add hlogle le_rfl

end PStarLR
