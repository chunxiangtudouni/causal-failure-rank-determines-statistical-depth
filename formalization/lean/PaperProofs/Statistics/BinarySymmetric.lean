module

public import PaperProofs.Statistics.Experiment
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FinCases

/-! The fair rational BSC of introduction.tex:32--35, independently of Paid. -/

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators

namespace PaperProofs.Statistics.BinarySymmetric

structure Parameters where
  gamma : ℚ
  gamma_pos : 0 < gamma
  gamma_le_quarter : gamma ≤ 1 / 4
  reviewFee : ℚ
  reviewFee_pos : 0 < reviewFee

namespace Parameters

def experiment (P : Parameters) : BinaryExperiment where
  alphabetSize := 2
  priorOne := 1 / 2
  prior_pos := by norm_num
  prior_lt_one := by norm_num
  channel x y :=
    if y.val = (if x then 1 else 0) then 1 / 2 + P.gamma else 1 / 2 - P.gamma
  channel_pos := by
    intro x y
    split_ifs <;> linarith [P.gamma_pos, P.gamma_le_quarter]
  channel_sum := by
    intro x
    cases x <;> norm_num [Fin.sum_univ_two]
  channel_distinct := by
    intro heq
    have h := congrFun heq (0 : Fin 2)
    norm_num at h
    linarith [P.gamma_pos]
  observationFee := P.reviewFee
  observationFee_pos := P.reviewFee_pos

theorem prior_eq_half (P : Parameters) (x : Bool) : P.experiment.prior x = 1 / 2 := by
  cases x <;> norm_num [experiment, BinaryExperiment.prior]

theorem channel_formula (P : Parameters) (x : Bool) (y : Fin 2) :
    P.experiment.channel x y =
      if y.val = (if x then 1 else 0) then 1 / 2 + P.gamma else 1 / 2 - P.gamma := rfl

theorem channel_correct (P : Parameters) (x : Bool) :
    P.experiment.channel x ⟨if x then 1 else 0, by cases x <;> norm_num [experiment]⟩ = 1 / 2 + P.gamma := by
  cases x <;> rfl

theorem channel_incorrect (P : Parameters) (x : Bool) :
    P.experiment.channel x ⟨if x then 0 else 1, by cases x <;> norm_num [experiment]⟩ = 1 / 2 - P.gamma := by
  cases x <;> rfl

def odds (P : Parameters) : ℚ := (1 + 2 * P.gamma) / (1 - 2 * P.gamma)

theorem odds_gt_one (P : Parameters) : 1 < P.odds := by
  have hd : 0 < 1 - 2 * P.gamma := by linarith [P.gamma_le_quarter]
  apply (lt_div_iff₀ hd).mpr
  linarith [P.gamma_pos]

noncomputable def h (P : Parameters) : ℝ := Real.log (P.odds : ℝ)
noncomputable def kappa (P : Parameters) : ℝ := 2 * (P.gamma : ℝ) * P.h
noncomputable def a (P : Parameters) : ℝ := (P.reviewFee : ℝ) / P.kappa

theorem h_pos (P : Parameters) : 0 < P.h := by
  apply Real.log_pos
  exact_mod_cast P.odds_gt_one

theorem kappa_pos (P : Parameters) : 0 < P.kappa := by
  have hg : 0 < (P.gamma : ℝ) := by exact_mod_cast P.gamma_pos
  exact mul_pos (mul_pos (by norm_num) hg) P.h_pos

theorem a_pos (P : Parameters) : 0 < P.a := by
  have hc : 0 < (P.reviewFee : ℝ) := by exact_mod_cast P.reviewFee_pos
  exact div_pos hc P.kappa_pos

theorem h_formula (P : Parameters) :
    P.h = Real.log ((1 + 2 * (P.gamma : ℝ)) / (1 - 2 * (P.gamma : ℝ))) := by
  simp [h, odds, Rat.cast_div, Rat.cast_sub, Rat.cast_add, Rat.cast_mul]

theorem divergence_eq_kappa (P : Parameters) (x : Bool) : P.experiment.divergence x = P.kappa := by
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
  have hreverse : Real.log (((1 / 2 : ℝ) - (P.gamma : ℝ)) / (1 / 2 + (P.gamma : ℝ))) = -P.h := by
    rw [Real.log_div (ne_of_gt hm) (ne_of_gt hp)]
    rw [h, ← hratio, Real.log_div (ne_of_gt hp) (ne_of_gt hm)]
    ring
  have hforward : Real.log (((1 / 2 : ℝ) + (P.gamma : ℝ)) / (1 / 2 - (P.gamma : ℝ))) = P.h := by
    rw [hratio]; rfl
  change (∑ y : Fin 2, P.experiment.channelReal x y *
    Real.log (P.experiment.channelReal x y / P.experiment.channelReal (!x) y)) = _
  rw [Fin.sum_univ_two]
  have hr (y : Fin 2) (z : Bool) : P.experiment.channelReal z y =
      if y.val = (if z then 1 else 0) then (1 / 2 : ℝ) + (P.gamma : ℝ)
      else (1 / 2 : ℝ) - (P.gamma : ℝ) := by
    unfold BinaryExperiment.channelReal
    rw [P.channel_formula]
    split_ifs <;> push_cast <;> rfl
  simp only [hr]
  cases x <;> norm_num only [Bool.false_eq_true, Bool.not_false, Bool.not_true,
    ↓reduceIte, Fin.val_zero, Fin.val_one, zero_ne_one, one_ne_zero, not_false_eq_true, reduceCtorEq] <;>
    rw [hforward, hreverse] <;> unfold kappa <;> ring

theorem coefficient_eq_a (P : Parameters) : P.experiment.coefficient = P.a := by
  unfold BinaryExperiment.coefficient
  simp only [BinaryExperiment.priorReal, P.prior_eq_half, P.divergence_eq_kappa,
    Rat.cast_div, Rat.cast_one, Rat.cast_ofNat]
  rw [Fintype.sum_bool]
  change (P.reviewFee : ℝ) * _ = _
  unfold a
  ring

end Parameters
end PaperProofs.Statistics.BinarySymmetric
