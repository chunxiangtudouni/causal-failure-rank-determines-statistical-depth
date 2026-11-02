module

public import Paid.PDCompute_SolverDenseBlock_071

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 400000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Computation

theorem denseReadHeaderValues_preserves (cells : List Cell) (start slot : ℕ) (values : ℕ → Cell)
    (outside : slot < start ∨ start+cells.length ≤ slot) :
    denseReadHeaderValues cells start values slot=values slot := by
  induction cells generalizing start values with
  | nil => rfl
  | cons cell cells ih =>
    have different : slot ≠ start := by simp only [List.length_cons] at outside; omega
    have tailOutside : slot < start+1 ∨ start+1+cells.length ≤ slot := by
      simp only [List.length_cons] at outside
      omega
    change denseReadHeaderValues cells (start+1) (Function.update values start cell) slot=values slot
    rw [ih (start+1) (Function.update values start cell) tailOutside,Function.update_of_ne different]

/-- These are the ORIGINAL three statistical fields actually loaded
from a six-cell dense entry, independently of its action tag. -/
theorem denseReadHeaderValues_stats (entry : MenuEntry) (start : ℕ) (values : ℕ → Cell) :
    denseReadHeaderValues (denseEncodeEntry entry) start values (start+3)=.rational entry.observation ∧
    denseReadHeaderValues (denseEncodeEntry entry) start values (start+4)=.rational entry.repairs ∧
    denseReadHeaderValues (denseEncodeEntry entry) start values (start+5)=.rational entry.failure := by
  obtain ⟨action,observation,repairs,failure⟩:=entry
  cases action <;> simp [denseEncodeEntry,denseReadHeaderValues,Nat.add_assoc]

theorem denseReadHeaderValues_good_stats (entry : MenuEntry) (values : ℕ → Cell) :
    denseReadHeaderValues (denseEncodeEntry entry) 7 values 10=.rational entry.observation ∧
    denseReadHeaderValues (denseEncodeEntry entry) 7 values 11=.rational entry.repairs ∧
    denseReadHeaderValues (denseEncodeEntry entry) 7 values 12=.rational entry.failure :=
  denseReadHeaderValues_stats entry 7 values

theorem denseReadHeaderValues_repair_stats (entry : MenuEntry) (values : ℕ → Cell) :
    denseReadHeaderValues (denseEncodeEntry entry) 13 values 16=.rational entry.observation ∧
    denseReadHeaderValues (denseEncodeEntry entry) 13 values 17=.rational entry.repairs ∧
    denseReadHeaderValues (denseEncodeEntry entry) 13 values 18=.rational entry.failure :=
  denseReadHeaderValues_stats entry 13 values

end PDCompute.Solver
