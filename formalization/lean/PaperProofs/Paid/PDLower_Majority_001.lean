module

public import PaperProofs.Paid.MenuCompiler
public import PaperProofs.Statistics.SymmetricHittingExact

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Statistics

namespace PDLower

def majorityScoreStep (symbol : ℕ) : ℤ := if symbol = 1 then 1 else -1

theorem majorityScoreFold_eq (observations : List ℕ) (acc : ℤ) :
    observations.foldl (fun score symbol => if symbol = 1 then score + 1 else score - 1) acc =
      acc + (observations.map majorityScoreStep).sum := by
  induction observations generalizing acc with
  | nil => simp
  | cons symbol rest ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.sum_cons]
    unfold majorityScoreStep
    split_ifs <;> ring

theorem majorityWordScore_eq_sum (observations : List ℕ) :
    PaperProofs.Paid.Parameters.menuWordScore observations = (observations.map majorityScoreStep).sum := by
  rw [PaperProofs.Paid.Parameters.menuWordScore, majorityScoreFold_eq, zero_add]

theorem majorityWordScore_ofFn {n : ℕ} (word : Fin n → Fin 2) :
    PaperProofs.Paid.Parameters.menuWordScore (List.ofFn (fun i => (word i).val)) =
      ∑ i, majorityScoreStep (word i).val := by
  rw [majorityWordScore_eq_sum, List.map_ofFn, List.sum_ofFn]
  simp only [Function.comp_apply]

theorem majorityWordLogLikelihood (P : BinarySymmetric.Parameters) (n : ℕ) (word : Fin n → Fin 2) :
    P.experiment.wordLogLikelihood true ⟨n, word⟩ =
      P.h * (PaperProofs.Paid.Parameters.menuWordScore (List.ofFn (fun i => (word i).val)) : ℝ) := by
  change (∑ i : Fin n, Real.log (P.experiment.channelReal true (word i) / P.experiment.channelReal false (word i))) = _
  calc
    _ = ∑ i : Fin n, P.h * (majorityScoreStep (word i).val : ℝ) := by
      apply Finset.sum_congr rfl
      intro i _
      simpa only [majorityScoreStep] using P.logIncrement_eq_signed (word i)
    _ = P.h * ((∑ i : Fin n, majorityScoreStep (word i).val : ℤ) : ℝ) := by
      rw [Int.cast_sum, Finset.mul_sum]
    _ = _ := by rw [majorityWordScore_ofFn]

theorem majority_wrong_probability_le (P : BinarySymmetric.Parameters) (n : ℕ) (word : Fin n → Fin 2)
    (x : Bool)
    (hwrong : decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore (List.ofFn (fun i => (word i).val))) ≠ x) :
    P.experiment.wordProbability x ⟨n, word⟩ ≤ P.experiment.wordProbability (!x) ⟨n, word⟩ := by
  let score := PaperProofs.Paid.Parameters.menuWordScore (List.ofFn (fun i => (word i).val))
  change decide (0 ≤ score) ≠ x at hwrong
  let w : P.experiment.StoppedWord := ⟨n, word⟩
  have ht := P.experiment.wordProbability_pos true w
  have hf := P.experiment.wordProbability_pos false w
  have hratio := P.experiment.wordLikelihood_eq_div true w
  simp only [Bool.not_true] at hratio
  have hlog : Real.log (P.experiment.wordProbability true w / P.experiment.wordProbability false w) =
      P.h * (score : ℝ) := by
    rw [← hratio, P.experiment.log_wordLikelihood]
    exact majorityWordLogLikelihood P n word
  cases x with
  | false =>
    have hs : 0 ≤ score := by
      by_contra hs
      exact hwrong (by simp [show ¬ 0 ≤ score from hs])
    have hsr : (0 : ℝ) ≤ score := by exact_mod_cast hs
    have hl : 0 ≤ Real.log (P.experiment.wordProbability true w / P.experiment.wordProbability false w) := by
      rw [hlog]
      exact mul_nonneg P.h_pos.le hsr
    have hr := (Real.log_nonneg_iff (div_pos ht hf)).mp hl
    simpa only [Bool.not_false, one_mul] using (le_div_iff₀ hf).mp hr
  | true =>
    have hn : ¬ 0 ≤ score := by
      intro hs
      exact hwrong (by simp [show 0 ≤ score from hs])
    have hs : score ≤ 0 := (lt_of_not_ge hn).le
    have hsr : (score : ℝ) ≤ 0 := by exact_mod_cast hs
    have hl : Real.log (P.experiment.wordProbability true w / P.experiment.wordProbability false w) ≤ 0 := by
      rw [hlog]
      exact mul_nonpos_of_nonneg_of_nonpos P.h_pos.le hsr
    have hr := (Real.log_nonpos_iff (div_nonneg ht.le hf.le)).mp hl
    simpa only [Bool.not_true, one_mul] using (div_le_iff₀ hf).mp hr

end PDLower
