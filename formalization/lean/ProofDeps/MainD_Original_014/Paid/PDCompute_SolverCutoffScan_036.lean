module

public import Paid.PDCompute_SolverRangeCompare_035
public import Paid.PDCompute_SolverLeastScan_011

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters

/-- Actual scan initialization may use the abandon objective as an upper
cutoff. Endpoints are still visited in increasing order, and only a
strict improvement changes the stored index. -/
def cutoffScan (objective : ℕ → ℚ) (cutoff : ℚ) : ℕ → ℕ × ℚ
  | 0 => if objective 0 < cutoff then (0,objective 0) else (0,cutoff)
  | last+1 =>
    let earlier := cutoffScan objective cutoff last
    if objective (last+1) < earlier.2 then (last+1,objective (last+1)) else earlier

theorem cutoffScan_eq_least (objective : ℕ → ℚ) (cutoff : ℚ) (last : ℕ) :
    cutoffScan objective cutoff last=
      if objective (scanLeast objective last) < cutoff then
        (scanLeast objective last,objective (scanLeast objective last)) else (0,cutoff) := by
  induction last with
  | zero => rfl
  | succ last ih =>
    rw [cutoffScan,ih]
    by_cases old : objective (scanLeast objective last) < cutoff <;>
      by_cases improved : objective (last+1) < objective (scanLeast objective last) <;>
      by_cases below : objective (last+1) < cutoff <;>
      simp only [scanLeast,old,improved,below,ite_true,ite_false] <;>
      exfalso <;> linarith

/-- The cutoff implementation returns EXACTLY the original selected
entry. The λ=0 branch is handled by the genuine caller fast path, not
removed from the original solver's input quantifier. -/
theorem cachedNextMenuEntry_cutoff (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (tools : ℕ)
    (nonzero : penalty ≠ 0) :
    P.cachedNextMenuEntry P.endpointCache fee penalty previous tools=
      let selected := cutoffScan
        (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
        penalty P.certificate.M
      if selected.2=penalty then abandonEntry else
        P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools selected.1 := by
  unfold Parameters.cachedNextMenuEntry
  rw [ite_eq_right nonzero,cachedLeastTestingLevel_scanLeast,cutoffScan_eq_least]
  dsimp only
  by_cases below :
      (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools
        (scanLeast (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
          P.certificate.M)).objective fee penalty < penalty
  · simp only [ite_eq_left below,ite_eq_right (not_le_of_gt below),ite_eq_right (ne_of_lt below)]
  · simp only [ite_eq_right below,ite_eq_left (le_of_not_gt below),ite_true]

end PDCompute.Solver
