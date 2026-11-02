module

public import PaperProofs.Paid.PDLower_Majority_001
public import Mathlib.Analysis.Real.Sqrt

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Statistics

namespace PDLower

theorem majority_channel_pair (P : BinarySymmetric.Parameters) (x : Bool) (symbol : Fin 2) :
    P.experiment.channelReal x symbol * P.experiment.channelReal (!x) symbol =
      (1 / 4 : ℝ) - (P.gamma : ℝ) ^ 2 := by
  have hy : symbol.val = 0 ∨ symbol.val = 1 := by omega
  cases x <;> rcases hy with hy | hy <;> simp [P.channelReal_formula, hy] <;> ring

theorem majority_word_pair (P : BinarySymmetric.Parameters) (n : ℕ) (word : Fin n → Fin 2) (x : Bool) :
    P.experiment.wordProbability x ⟨n, word⟩ * P.experiment.wordProbability (!x) ⟨n, word⟩ =
      ((1 / 4 : ℝ) - (P.gamma : ℝ) ^ 2) ^ n := by
  simp only [BinaryExperiment.wordProbability]
  rw [← Finset.prod_mul_distrib]
  simp_rw [majority_channel_pair]
  simp

theorem majority_word_error_bound (P : BinarySymmetric.Parameters) (n : ℕ) (word : Fin n → Fin 2)
    (x : Bool)
    (hwrong : decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore (List.ofFn (fun i => (word i).val))) ≠ x) :
    P.experiment.wordProbability x ⟨n, word⟩ ≤
      Real.sqrt (((1 / 4 : ℝ) - (P.gamma : ℝ) ^ 2) ^ n) := by
  have h := mul_le_mul_of_nonneg_left (majority_wrong_probability_le P n word x hwrong)
    (P.experiment.wordProbability_pos x ⟨n, word⟩).le
  apply Real.le_sqrt_of_sq_le
  rw [← majority_word_pair P n word x]
  simpa only [pow_two] using h

theorem majority_variance_quarter_nonneg (P : BinarySymmetric.Parameters) :
    (0 : ℝ) ≤ 1 / 4 - (P.gamma : ℝ) ^ 2 := by
  rw [← majority_channel_pair P false (0 : Fin 2)]
  exact mul_nonneg (P.experiment.channelReal_pos false _).le
    (P.experiment.channelReal_pos (!false) _).le

end PDLower
