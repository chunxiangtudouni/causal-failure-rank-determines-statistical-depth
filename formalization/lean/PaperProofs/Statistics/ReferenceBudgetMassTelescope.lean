module

public import PaperProofs.Statistics.ReferenceBudgetMass
public import Mathlib.Algebra.BigOperators.Intervals

/-!
Finite positive-term telescoping for the actual B17 stage mass flow.
The stage-event construction supplies the displayed local inequalities.
This algebra never subtracts extended values and allows all masses to be
infinite. It contains no policy, cost, success or finiteness restriction.
-/

@[expose] public section

open scoped BigOperators ENNReal

namespace PaperProofs.Statistics

theorem referenceBudgetMass_telescope (failure budget : ℕ → ℝ≥0∞) (N : ℕ)
    (hstep : ∀ i, i < N → failure i + budget (i + 1) ≤ budget i) :
    (∑ i ∈ Finset.range N, failure i) + budget N ≤ budget 0 := by
  revert hstep
  induction N with
  | zero =>
    intro _hstep
    simp
  | succ N ih =>
    intro hstep
    have hprevious := ih (fun i hi => hstep i (by omega))
    calc
      _ = (∑ i ∈ Finset.range N, failure i) + (failure N + budget (N + 1)) := by
        rw [Finset.sum_range_succ]
        ac_rfl
      _ ≤ (∑ i ∈ Finset.range N, failure i) + budget N :=
        add_le_add_right (hstep N (Nat.lt_succ_self N)) _
      _ ≤ _ := hprevious

theorem referenceFailureMass_sum_le (failure budget : ℕ → ℝ≥0∞) (N : ℕ)
    (hstep : ∀ i, i < N → failure i + budget (i + 1) ≤ budget i) :
    (∑ i ∈ Finset.range N, failure i) ≤ budget 0 :=
  (show (∑ i ∈ Finset.range N, failure i) ≤ (∑ i ∈ Finset.range N, failure i) + budget N
    from le_self_add).trans (referenceBudgetMass_telescope failure budget N hstep)

theorem referenceFailureMass_sum_le_initial (failure budget : ℕ → ℝ≥0∞) (N : ℕ)
    (initial : ℝ≥0∞) (hstep : ∀ i, i < N → failure i + budget (i + 1) ≤ budget i)
    (hinitial : budget 0 ≤ initial) : (∑ i ∈ Finset.range N, failure i) ≤ initial :=
  (referenceFailureMass_sum_le failure budget N hstep).trans hinitial

end PaperProofs.Statistics
