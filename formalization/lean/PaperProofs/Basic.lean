module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Finset.Card
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-!
Environment smoke checks. These examples test Mathlib and its tactics;
they do not formalize any claim from the paper.
-/

public section

namespace PaperProofs

theorem square_expansion (x y : ℝ) :
    (x + y) ^ 2 = x ^ 2 + 2 * x * y + y ^ 2 := by
  ring

theorem linear_bound (x y : ℝ) (hxy : x ≤ y) :
    2 * x + 1 ≤ 2 * y + 1 := by
  linarith

theorem finite_card_bound {α : Type*} {s t : Finset α} (h : s ⊆ t) :
    s.card ≤ t.card := by
  exact Finset.card_le_card h

end PaperProofs
