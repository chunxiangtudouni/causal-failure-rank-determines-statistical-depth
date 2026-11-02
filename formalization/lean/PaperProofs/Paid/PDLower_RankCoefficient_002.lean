module

public import PaperProofs.Paid.PDLower_RankCoefficient_001

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open scoped ENNReal BigOperators
open PaperProofs.Common PaperProofs.Structure PaperProofs.Statistics

namespace PDLower

variable {Tool : Type*} [Fintype Tool] [DecidableEq Tool]

theorem sharedPool_bad_replicate_short (n : ℕ) (remaining : Finset Tool) :
    badChildRank (Finset.univ : Finset Tool) (List.replicate n Finset.univ) remaining =
      if n < remaining.card then ⊤ else (remaining.card : ℕ∞) := by
  rw [sharedPool_bad_replicate]
  by_cases hk : remaining.card = 0
  · simp [hk]
  · simp only [hk, ↓reduceIte]
    by_cases hn : n < remaining.card
    · have hle : n ≤ remaining.card - 1 := by omega
      simp only [hn, hle, ↓reduceIte]
    · have hle : ¬ n ≤ remaining.card - 1 := by omega
      simp only [hn, hle, ↓reduceIte]

omit [DecidableEq Tool] in
theorem eligibilitySchedule_replicate (n : ℕ) (weight : ℝ) :
    eligibilitySchedule (List.replicate n ((Finset.univ : Finset Tool), weight)) =
      List.replicate n Finset.univ := by
  simp [eligibilitySchedule]

theorem sharedPool_criticalHeadSum_replicate (n : ℕ) (remaining : Finset Tool) (weight : ℝ) :
    criticalHeadSum (List.replicate n ((Finset.univ : Finset Tool), weight)) remaining
      ((remaining.card + 1 : ℕ) : ℕ∞) = weight * (n - remaining.card : ℕ) := by
  induction n with
  | zero => simp [criticalHeadSum]
  | succ n ih =>
    rw [List.replicate_succ, criticalHeadSum, eligibilitySchedule_replicate,
      sharedPool_bad_replicate_short, ih]
    by_cases hn : n < remaining.card
    · rw [ite_eq_left hn]
      have hne : (⊤ : ℕ∞) + 1 ≠ ((remaining.card + 1 : ℕ) : ℕ∞) := by
        rw [top_add]
        exact ENat.top_ne_natCast _
      rw [ite_eq_right hne]
      have hsub : n - remaining.card = 0 := by omega
      have hsub' : n + 1 - remaining.card = 0 := by omega
      simp [hsub, hsub']
    · rw [ite_eq_right hn]
      have heq : (remaining.card : ℕ∞) + 1 = ((remaining.card + 1 : ℕ) : ℕ∞) := by
        rw [ENat.natCast_add, ENat.natCast_one]
      rw [ite_eq_left heq]
      have hsub : n + 1 - remaining.card = (n - remaining.card) + 1 := by omega
      rw [hsub, Nat.cast_add, Nat.cast_one]
      ring

end PDLower
