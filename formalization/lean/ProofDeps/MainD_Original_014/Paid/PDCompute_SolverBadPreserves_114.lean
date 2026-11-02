module

public import Paid.PDCompute_SolverBadChoice_108

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 650000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation

def BadUntouched (slot : ℕ) : Prop :=
  slot < 13 ∨ slot=19 ∨ slot=20 ∨ slot=21 ∨ (35 ≤ slot ∧ slot < 40) ∨ 43 ≤ slot

theorem badPreparationValues_preserves (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry)
    (slot : ℕ) (outside : BadUntouched slot) : badPreparationValues values fee penalty entry slot=values slot := by
  have h22 : slot ≠ 22 := by unfold BadUntouched at outside; omega
  have h24 : slot ≠ 24 := by unfold BadUntouched at outside; omega
  have h28 : slot ≠ 28 := by unfold BadUntouched at outside; omega
  have h29 : slot ≠ 29 := by unfold BadUntouched at outside; omega
  have h30 : slot ≠ 30 := by unfold BadUntouched at outside; omega
  have h31 : slot ≠ 31 := by unfold BadUntouched at outside; omega
  have h32 : slot ≠ 32 := by unfold BadUntouched at outside; omega
  have h33 : slot ≠ 33 := by unfold BadUntouched at outside; omega
  have h34 : slot ≠ 34 := by unfold BadUntouched at outside; omega
  have h40 : slot ≠ 40 := by unfold BadUntouched at outside; omega
  have h41 : slot ≠ 41 := by unfold BadUntouched at outside; omega
  have h42 : slot ≠ 42 := by unfold BadUntouched at outside; omega
  simp only [badPreparationValues,Function.update_of_ne h22,Function.update_of_ne h24,Function.update_of_ne h28,
    Function.update_of_ne h29,Function.update_of_ne h30,Function.update_of_ne h31,Function.update_of_ne h32,
    Function.update_of_ne h33,Function.update_of_ne h34,Function.update_of_ne h40,Function.update_of_ne h41,
    Function.update_of_ne h42]

theorem acceptRepairValues_preserves (values : ℕ → Cell) (slot : ℕ) (outside : BadUntouched slot) :
    acceptRepairValues values slot=values slot := by
  have h22 : slot ≠ 22 := by unfold BadUntouched at outside; omega
  have h31 : slot ≠ 31 := by unfold BadUntouched at outside; omega
  have h32 : slot ≠ 32 := by unfold BadUntouched at outside; omega
  have h33 : slot ≠ 33 := by unfold BadUntouched at outside; omega
  have h34 : slot ≠ 34 := by unfold BadUntouched at outside; omega
  simp only [acceptRepairValues,Function.update_of_ne h22,Function.update_of_ne h31,Function.update_of_ne h32,
    Function.update_of_ne h33,Function.update_of_ne h34]

theorem loadedBadValues_preserves (values : ℕ → Cell) (fee penalty : ℚ) (entry : MenuEntry)
    (slot : ℕ) (outside : BadUntouched slot) : loadedBadValues values fee penalty entry slot=values slot := by
  have loaded : denseReadHeaderValues (denseEncodeEntry entry) 13 values slot=values slot := by
    apply denseReadHeaderValues_preserves
    simp only [denseEncodeEntry_length,entryWords]
    unfold BadUntouched at outside
    omega
  unfold loadedBadValues positiveBadValues
  split_ifs
  · exact (acceptRepairValues_preserves _ slot outside).trans
      ((badPreparationValues_preserves _ fee penalty entry slot outside).trans loaded)
  · exact (badPreparationValues_preserves _ fee penalty entry slot outside).trans loaded

theorem badChoiceValues_preserves (values : ℕ → Cell) (fee penalty : ℚ) (previous : MenuRow) (tools slot : ℕ)
    (outside : BadUntouched slot) : badChoiceValues values fee penalty previous tools slot=values slot := by
  by_cases zero : tools=0
  · have h22 : slot ≠ 22 := by unfold BadUntouched at outside; omega
    have h31 : slot ≠ 31 := by unfold BadUntouched at outside; omega
    have h32 : slot ≠ 32 := by unfold BadUntouched at outside; omega
    have h33 : slot ≠ 33 := by unfold BadUntouched at outside; omega
    have h34 : slot ≠ 34 := by unfold BadUntouched at outside; omega
    simp only [badChoiceValues,zero,ite_true,zeroBadValues,Function.update_of_ne h22,Function.update_of_ne h31,
      Function.update_of_ne h32,Function.update_of_ne h33,Function.update_of_ne h34]
  · simp only [badChoiceValues,zero,ite_false]
    exact loadedBadValues_preserves values fee penalty _ slot outside

end PDCompute.Solver
