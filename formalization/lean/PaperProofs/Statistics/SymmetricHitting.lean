module

public import PaperProofs.Statistics.BSCInformation
public import PaperProofs.Statistics.PosteriorSPRT

/-! Real symmetric integer-boundary experiments of paid-proofs.tex:71--106.
The test is the already constructed causal/measurable posterior SPRT.
Its performance identities are separate propositions, never test fields. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory

namespace PaperProofs.Statistics.BinarySymmetric.Parameters

def endpointError (P : Parameters) (m : ℕ) : ℚ := 1 / (1 + P.odds ^ m)

theorem endpointError_pos (P : Parameters) (m : ℕ) : 0 < P.endpointError m :=
  one_div_pos.mpr (add_pos zero_lt_one (pow_pos (zero_lt_one.trans P.odds_gt_one) m))

theorem endpointError_le_half (P : Parameters) (m : ℕ) : P.endpointError m ≤ 1 / 2 := by
  have hp : 1 ≤ P.odds ^ m := one_le_pow₀ P.odds_gt_one.le
  exact (div_le_div_iff₀ (by linarith : (0 : ℚ) < 1 + P.odds ^ m) (by norm_num)).mpr (by linarith)

theorem endpointError_lt_half (P : Parameters) {m : ℕ} (hm : 1 ≤ m) : P.endpointError m < 1 / 2 := by
  have hp : 1 < P.odds ^ m := one_lt_pow₀ P.odds_gt_one (by omega)
  exact (div_lt_div_iff₀ (by linarith : (0 : ℚ) < 1 + P.odds ^ m) (by norm_num)).mpr (by linarith)

@[simp] theorem endpointError_zero (P : Parameters) : P.endpointError 0 = 1 / 2 := by
  norm_num [endpointError]

theorem endpoint_error_odds (P : Parameters) (m : ℕ) :
    (1 - P.endpointError m) / P.endpointError m = P.odds ^ m := by
  have hd : 1 + P.odds ^ m ≠ 0 := ne_of_gt
    (add_pos zero_lt_one (pow_pos (zero_lt_one.trans P.odds_gt_one) m))
  unfold endpointError
  field_simp
  ring

theorem endpointThreshold (P : Parameters) (m : ℕ) :
    Real.log ((1 - (P.endpointError m : ℝ)) / (P.endpointError m : ℝ)) = (m : ℝ) * P.h := by
  have hr : (1 - (P.endpointError m : ℝ)) / (P.endpointError m : ℝ) = (P.odds : ℝ) ^ m := by
    exact_mod_cast P.endpoint_error_odds m
  rw [hr, Real.log_pow]
  rfl

def endpointMeanCount (P : Parameters) (m : ℕ) : ℚ :=
  (m : ℚ) * (1 - 2 * P.endpointError m) / (2 * P.gamma)

/-- Local review charge C_m; C_0 here is zero review charge, not the
independent normal full-run charge from NormalCharges. -/
def endpointCharge (P : Parameters) (m : ℕ) : ℚ := P.reviewFee * P.endpointMeanCount m

theorem endpointCharge_formula (P : Parameters) (m : ℕ) :
    P.endpointCharge m = P.reviewFee * (m : ℚ) / (2 * P.gamma) * (1 - 2 * P.endpointError m) := by
  unfold endpointCharge endpointMeanCount
  ring

theorem endpointMeanCount_nonneg (P : Parameters) (m : ℕ) : 0 ≤ P.endpointMeanCount m := by
  exact div_nonneg (mul_nonneg (Nat.cast_nonneg _) (by linarith [P.endpointError_le_half m]))
    (mul_pos (by norm_num) P.gamma_pos).le

theorem endpointCharge_nonneg (P : Parameters) (m : ℕ) : 0 ≤ P.endpointCharge m :=
  mul_nonneg P.reviewFee_pos.le (P.endpointMeanCount_nonneg m)

@[simp] theorem endpointMeanCount_zero (P : Parameters) : P.endpointMeanCount 0 = 0 := by
  norm_num [endpointMeanCount]

@[simp] theorem endpointCharge_zero (P : Parameters) : P.endpointCharge 0 = 0 := by
  simp only [endpointCharge, endpointMeanCount_zero, mul_zero]

theorem endpointCharge_eq_information (P : Parameters) (m : ℕ) :
    (P.endpointCharge m : ℝ) = P.a * phiReal (P.endpointError m : ℝ) := by
  rw [phiReal, P.endpointThreshold]
  unfold endpointCharge endpointMeanCount a kappa
  push_cast
  have hg : (P.gamma : ℝ) ≠ 0 := by exact_mod_cast P.gamma_pos.ne'
  field_simp [hg, P.h_pos.ne']

theorem endpointChargeENN_eq_information (P : Parameters) (m : ℕ) :
    ENNReal.ofReal (P.endpointCharge m : ℝ) = ENNReal.ofReal P.a * phi (P.endpointError m : ℝ) := by
  have hp : 0 < (P.endpointError m : ℝ) := by exact_mod_cast P.endpointError_pos m
  rw [phi_of_pos hp, ← ENNReal.ofReal_mul P.a_pos.le, P.endpointCharge_eq_information]

/-- The unrounded integer signed walk on the actual review tape. -/
def signedSum (P : Parameters) (tape : P.experiment.Tape) (n : ℕ) : ℤ :=
  ∑ k ∈ Finset.range n, if (tape k).val = 1 then 1 else -1

@[simp] theorem signedSum_zero (P : Parameters) (tape : P.experiment.Tape) : P.signedSum tape 0 = 0 := by
  simp [signedSum]

theorem signedSum_succ (P : Parameters) (tape : P.experiment.Tape) (n : ℕ) :
    P.signedSum tape (n + 1) = P.signedSum tape n + if (tape n).val = 1 then 1 else -1 := by
  simp only [signedSum, Finset.sum_range_succ]

theorem channelReal_formula (P : Parameters) (x : Bool) (y : Fin 2) :
    P.experiment.channelReal x y =
      if y.val = (if x then 1 else 0) then (1 / 2 : ℝ) + (P.gamma : ℝ)
      else (1 / 2 : ℝ) - (P.gamma : ℝ) := by
  unfold BinaryExperiment.channelReal
  rw [P.channel_formula]
  split_ifs <;> push_cast <;> rfl

theorem logIncrement_eq_signed (P : Parameters) (y : Fin 2) :
    Real.log (P.experiment.channelReal true y / P.experiment.channelReal false y) =
      P.h * (if y.val = 1 then 1 else -1 : ℤ) := by
  have hm : 0 < (1 / 2 : ℝ) - (P.gamma : ℝ) := by
    have hg := (Rat.cast_le (K := ℝ)).mpr P.gamma_le_quarter
    norm_num at hg
    linarith
  have hp : 0 < (1 / 2 : ℝ) + (P.gamma : ℝ) := by
    have hg : 0 < (P.gamma : ℝ) := by exact_mod_cast P.gamma_pos
    linarith
  have hratio : ((1 / 2 : ℝ) + (P.gamma : ℝ)) / (1 / 2 - (P.gamma : ℝ)) = (P.odds : ℝ) := by
    simp only [odds, Rat.cast_div, Rat.cast_add, Rat.cast_sub, Rat.cast_mul, Rat.cast_one, Rat.cast_ofNat]
    field_simp
  have hforward : Real.log (((1 / 2 : ℝ) + (P.gamma : ℝ)) / (1 / 2 - (P.gamma : ℝ))) = P.h := by
    rw [hratio]; rfl
  have hreverse : Real.log (((1 / 2 : ℝ) - (P.gamma : ℝ)) / (1 / 2 + (P.gamma : ℝ))) = -P.h := by
    rw [Real.log_div hm.ne' hp.ne', h, ← hratio, Real.log_div hp.ne' hm.ne']
    ring
  have hy : y.val = 0 ∨ y.val = 1 := by omega
  rcases hy with hy | hy
  · simpa [P.channelReal_formula, hy] using hreverse
  · simpa [P.channelReal_formula, hy] using hforward

theorem logOddsScore_eq_signed (P : Parameters) (tape : P.experiment.Tape) (n : ℕ) :
    P.experiment.logOddsScore tape n = P.h * (P.signedSum tape n : ℝ) := by
  induction n with
  | zero =>
    rw [P.experiment.logOddsScore_zero, P.signedSum_zero]
    norm_num [BinaryExperiment.priorReal, P.prior_eq_half]
  | succ n ih =>
    have hs : Real.log (P.experiment.channelReal true (tape n) / P.experiment.channelReal false (tape n)) =
        P.h * (if (tape n).val = 1 then 1 else -1 : ℤ) := P.logIncrement_eq_signed (tape n)
    rw [P.experiment.logOddsScore_succ, ih, P.signedSum_succ, hs]
    push_cast
    ring

theorem abs_logOddsScore_eq (P : Parameters) (tape : P.experiment.Tape) (n : ℕ) :
    |P.experiment.logOddsScore tape n| = P.h * ((P.signedSum tape n).natAbs : ℝ) := by
  rw [P.logOddsScore_eq_signed, abs_mul, abs_of_pos P.h_pos, Nat.cast_natAbs, Int.cast_abs]

/-- Actual stopping time and stopped MAP decision from the original tape. -/
noncomputable def symmetricHittingTest (P : Parameters) (m : ℕ) : P.experiment.AdmissibleRule Unit :=
  P.experiment.posteriorSPRT (P.endpointError m)

theorem symmetricHittingTest_stop_le_iff (P : Parameters) (m : ℕ) (tape : P.experiment.Tape) (n : ℕ) :
    (P.symmetricHittingTest m).rule.stop () tape ≤ n ↔
      ∃ k ≤ n, m ≤ (P.signedSum tape k).natAbs := by
  change P.experiment.posteriorThresholdStop (P.endpointError m) tape ≤ n ↔ _
  rw [P.experiment.posteriorThresholdStop_le_iff]
  apply exists_congr
  intro k
  apply and_congr_right
  intro _
  rw [P.endpointThreshold, P.abs_logOddsScore_eq]
  constructor
  · intro h
    have hr : (m : ℝ) ≤ ((P.signedSum tape k).natAbs : ℝ) := by nlinarith [P.h_pos]
    exact_mod_cast hr
  · intro h
    have hr : (m : ℝ) ≤ ((P.signedSum tape k).natAbs : ℝ) := by exact_mod_cast h
    nlinarith [P.h_pos]

theorem signedSum_natAbs_succ_le (P : Parameters) (tape : P.experiment.Tape) (n : ℕ) :
    (P.signedSum tape (n + 1)).natAbs ≤ (P.signedSum tape n).natAbs + 1 := by
  rw [P.signedSum_succ]
  calc
    _ ≤ (P.signedSum tape n).natAbs + (if (tape n).val = 1 then (1 : ℤ) else -1).natAbs :=
      Int.natAbs_add_le _ _
    _ = _ := by split_ifs <;> norm_num

/-- At every finite first exit, the walk is exactly at +m or -m. This
rules out overshoot and verifies the original symmetric hitting test. -/
theorem symmetricHittingTest_hits_exact (P : Parameters) (m : ℕ) (hm : 1 ≤ m)
    (tape : P.experiment.Tape) (n : ℕ)
    (hstop : (P.symmetricHittingTest m).rule.stop () tape = n) :
    (P.signedSum tape n).natAbs = m := by
  have hhit : m ≤ (P.signedSum tape n).natAbs := by
    obtain ⟨k, hkn, hk⟩ := (P.symmetricHittingTest_stop_le_iff m tape n).mp (by rw [hstop])
    have hnk : n ≤ k := by
      have hle := (P.symmetricHittingTest_stop_le_iff m tape k).mpr ⟨k, le_rfl, hk⟩
      rw [hstop] at hle
      exact ENat.natCast_le_natCast.mp hle
    simpa only [Nat.le_antisymm hkn hnk] using hk
  cases n with
  | zero => simp only [P.signedSum_zero, Int.natAbs_zero] at hhit; omega
  | succ n =>
    have hbefore : (P.signedSum tape n).natAbs < m := by
      apply Nat.lt_of_not_ge
      intro h
      have hle := (P.symmetricHittingTest_stop_le_iff m tape n).mpr ⟨n, le_rfl, h⟩
      rw [hstop] at hle
      have hn := ENat.natCast_le_natCast.mp hle
      omega
    have hupper := P.signedSum_natAbs_succ_le tape n
    omega

theorem symmetricHittingTest_expectedSamples_finite (P : Parameters) (m : ℕ) (x : Bool) :
    P.experiment.expectedSamples (Measure.dirac ()) (P.symmetricHittingTest m) x ≠ ⊤ := by
  apply P.experiment.posteriorSPRT_expectedSamples_finite
  rw [P.endpointThreshold]
  exact mul_nonneg (Nat.cast_nonneg _) P.h_pos.le

theorem symmetricHittingTest_expectedCharge_finite (P : Parameters) (m : ℕ) (x : Bool) :
    P.experiment.expectedObservationCharge (Measure.dirac ()) (P.symmetricHittingTest m) x ≠ ⊤ := by
  apply P.experiment.posteriorSPRT_expectedObservationCharge_finite
  rw [P.endpointThreshold]
  exact mul_nonneg (Nat.cast_nonneg _) P.h_pos.le

/-- Exact D04 performance identities for the real test above. Their proof
is in SymmetricHittingExact, separately from the stopping-boundary encoding. -/
def SymmetricHittingExactLaw (P : Parameters) : Prop :=
  ∀ m : ℕ, 1 ≤ m →
    (∀ x : Bool, P.experiment.conditionalError (Measure.dirac ()) (P.symmetricHittingTest m) x =
      ENNReal.ofReal (P.endpointError m : ℝ)) ∧
    (∀ x : Bool, P.experiment.expectedSamples (Measure.dirac ()) (P.symmetricHittingTest m) x =
      ENNReal.ofReal (P.endpointMeanCount m : ℝ)) ∧
    (∀ x : Bool, P.experiment.expectedObservationCharge (Measure.dirac ()) (P.symmetricHittingTest m) x =
      ENNReal.ofReal (P.endpointCharge m : ℝ))

end PaperProofs.Statistics.BinarySymmetric.Parameters
