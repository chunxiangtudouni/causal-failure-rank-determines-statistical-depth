module

public import PaperProofs.Paid.PDLower_Majority_002

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped BigOperators ENNReal
open MeasureTheory
open PaperProofs.Statistics

namespace PDLower

theorem majority_finite_word_bound (P : BinarySymmetric.Parameters) (n : ℕ) (x : Bool) :
    P.experiment.tapeLaw x
      {tape | decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore
        (List.ofFn (fun i : Fin n => (tape i.val).val))) ≠ x} ≤
      (2 : ℝ≥0∞) ^ n * ENNReal.ofReal (Real.sqrt (((1 / 4 : ℝ) - (P.gamma : ℝ) ^ 2) ^ n)) := by
  classical
  have hAlphabet : P.experiment.alphabetSize = 2 := rfl
  let words (w : Fin n → Fin P.experiment.alphabetSize) : Set P.experiment.Tape :=
    if decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore (List.ofFn (fun i => (w i).val))) ≠ x
    then P.experiment.prefixEvent ⟨n, w⟩ else ∅
  have hevent :
      {tape : P.experiment.Tape | decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore
        (List.ofFn (fun i : Fin n => (tape i.val).val))) ≠ x} = ⋃ w : Fin n → Fin P.experiment.alphabetSize, words w := by
    ext tape
    simp only [Set.mem_iUnion]
    constructor
    · intro ht
      change decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore
        (List.ofFn (fun i : Fin n => (tape i.val).val))) ≠ x at ht
      refine ⟨fun i => tape i.val, ?_⟩
      dsimp only [words]
      rw [ite_eq_left ht]
      exact fun _ => rfl
    · rintro ⟨w, hw⟩
      by_cases hd : decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore (List.ofFn (fun i => (w i).val))) ≠ x
      · have hpref : tape ∈ P.experiment.prefixEvent ⟨n, w⟩ := by
          dsimp only [words] at hw
          rw [ite_eq_left hd] at hw
          exact hw
        have heq : (fun i : Fin n => (tape i.val).val) = (fun i : Fin n => (w i).val) :=
          funext (fun i => congrArg Fin.val (hpref i))
        change decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore (List.ofFn (fun i : Fin n => (tape i.val).val))) ≠ x
        rw [heq]
        exact hd
      · dsimp only [words] at hw
        rw [ite_eq_right hd] at hw
        change False at hw
        exact hw.elim
  rw [hevent]
  calc
    _ ≤ ∑ w : Fin n → Fin P.experiment.alphabetSize, P.experiment.tapeLaw x (words w) :=
      measure_iUnion_fintype_le (P.experiment.tapeLaw x) words
    _ ≤ ∑ _w : Fin n → Fin P.experiment.alphabetSize,
        ENNReal.ofReal (Real.sqrt (((1 / 4 : ℝ) - (P.gamma : ℝ) ^ 2) ^ n)) := by
      apply Finset.sum_le_sum
      intro w _
      by_cases hw : decide (0 ≤ PaperProofs.Paid.Parameters.menuWordScore (List.ofFn (fun i => (w i).val))) ≠ x
      · dsimp only [words]
        rw [ite_eq_left hw, P.experiment.tapeLaw_prefixEvent]
        exact ENNReal.ofReal_le_ofReal (majority_word_error_bound P n w x hw)
      · have hz : P.experiment.tapeLaw x (words w) = 0 := by
          dsimp only [words]
          rw [ite_eq_right hw, measure_empty]
        rw [hz]
        exact bot_le
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fin,
        hAlphabet, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat]

end PDLower
