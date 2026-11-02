module

public import Paid.PDCompute_SolverDenseLayout_006

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters

/-- Analysis of the literal streaming strict-less comparison. It retains
the earlier index on every tie and needs only one best index/objective. -/
def scanLeast (objective : ℕ → ℚ) : ℕ → ℕ
  | 0 => 0
  | n+1 => if objective (n+1) < objective (scanLeast objective n) then n+1 else scanLeast objective n

theorem argmin_range_scanLeast (objective : ℕ → ℚ) (last : ℕ) :
    (List.range (last+1)).argmin objective=some (scanLeast objective last) := by
  induction last with
  | zero => rfl
  | succ last ih =>
      rw [List.range_succ,List.argmin_concat,ih]
      change (if objective (last+1) < objective (scanLeast objective last) then some (last+1) else some (scanLeast objective last)) =
        some (if objective (last+1) < objective (scanLeast objective last) then last+1 else scanLeast objective last)
      split_ifs <;> rfl

theorem cachedLeastTestingLevel_scanLeast (P : Parameters) (fee penalty : ℚ)
    (previous : MenuRow) (tools : ℕ) :
    P.cachedLeastTestingLevel P.endpointCache fee penalty previous tools =
      scanLeast (fun level => (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty)
        P.certificate.M := by
  unfold Parameters.cachedLeastTestingLevel
  rw [argmin_range_scanLeast]
  rfl

theorem cachedTesting_objective_affine (P : Parameters) (fee penalty : ℚ) (previous : MenuRow)
    (tools level : ℕ) :
    (P.cachedMenuTestingEntry P.endpointCache fee penalty previous tools level).objective fee penalty =
      (P.cachedEndpoint P.endpointCache level).charge +
        (1-(P.cachedEndpoint P.endpointCache level).error)*(previous.getD tools abandonEntry).objective fee penalty +
        (P.cachedEndpoint P.endpointCache level).error*(P.menuBadBranch fee penalty previous tools).2.objective fee penalty := by
  rw [P.cachedMenuTestingEntry_eq]
  simp only [P.cachedEndpoint_eq,Parameters.endpointConstant]
  exact P.menuTestingEntry_objective fee penalty previous tools level

end PDCompute.Solver
