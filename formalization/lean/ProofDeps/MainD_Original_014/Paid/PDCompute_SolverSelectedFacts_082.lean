module

public import Paid.PDCompute_SolverCutoffScan_036

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters

theorem cutoffScan_index_le (objective : ℕ → ℚ) (cutoff : ℚ) (last : ℕ) :
    (cutoffScan objective cutoff last).1 ≤ last := by
  induction last with
  | zero => simp only [cutoffScan]; split_ifs <;> exact le_refl _
  | succ last ih =>
    simp only [cutoffScan]
    split_ifs
    · exact le_refl _
    · exact ih.trans (Nat.le_succ last)

theorem cutoffScan_value_le (objective : ℕ → ℚ) (cutoff : ℚ) (last : ℕ) :
    (cutoffScan objective cutoff last).2 ≤ cutoff := by
  induction last with
  | zero => simp only [cutoffScan]; split_ifs with less <;> first | exact less.le | exact le_refl _
  | succ last ih =>
    simp only [cutoffScan]
    split_ifs with improved
    · exact improved.le.trans ih
    · exact ih

/-- This is the strict scalar branch implemented by the caller, with
the original separate outer abandonment comparison and ties intact. -/
theorem cachedNextMenuEntry_cutoff_strict (P : Parameters) (fee penalty : ℚ) (previous : MenuRow)
    (tools : ℕ) (nonzero : penalty ≠ 0) :
    P.cachedNextMenuEntry P.endpointCache fee penalty previous tools=
      let selected:=cutoffScan
        (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
        penalty P.certificate.M
      if selected.2 < penalty then P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools selected.1
      else abandonEntry := by
  rw [cachedNextMenuEntry_cutoff P fee penalty previous tools nonzero]
  dsimp only
  have bound:=cutoffScan_value_le
    (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
    penalty P.certificate.M
  by_cases same : (cutoffScan
      (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
      penalty P.certificate.M).2=penalty
  · simp only [same,ite_true,lt_self_iff_false,ite_false]
  · have less : (cutoffScan
        (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
        penalty P.certificate.M).2 < penalty := by
      exact lt_of_le_of_ne bound same
    simp only [ite_eq_right same,ite_eq_left less]

end PDCompute.Solver
