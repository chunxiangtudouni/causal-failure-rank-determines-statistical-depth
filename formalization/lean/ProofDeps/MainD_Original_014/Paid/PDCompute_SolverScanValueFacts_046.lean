module

public import Paid.PDCompute_SolverScanBack_045

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDCompute.Solver

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

theorem scanCandidateValues_preserves (P : Parameters) (values : ℕ → Cell) (index : ℕ) (good bad : ℚ)
    (slot : ℕ) (h26 : slot ≠ 26) (h27 : slot ≠ 27) (h28 : slot ≠ 28)
    (h29 : slot ≠ 29) (h30 : slot ≠ 30) :
    scanCandidateValues P values index good bad slot=values slot := by
  simp only [scanCandidateValues,candidateValues,Function.update_of_ne h26,Function.update_of_ne h27,
    Function.update_of_ne h28,Function.update_of_ne h29,Function.update_of_ne h30]

theorem scanCandidateValues_objective (P : Parameters) (values : ℕ → Cell) (index : ℕ) (good bad : ℚ) :
    scanCandidateValues P values index good bad 28=
      .rational ((P.cachedEndpoint P.endpointCache index).charge+
        (1-(P.cachedEndpoint P.endpointCache index).error)*good+
        (P.cachedEndpoint P.endpointCache index).error*bad) :=
  candidateValues_objective _ _ _ _ _

theorem minimumUpdateValues_preserves (values : ℕ → Cell) (slot : ℕ) (h23 : slot ≠ 23) (h24 : slot ≠ 24) :
    minimumUpdateValues values slot=values slot := by
  simp only [minimumUpdateValues,Function.update_of_ne h23,Function.update_of_ne h24]

def scanIterationValues (P : Parameters) (values : ℕ → Cell) (index source : ℕ) (good bad best : ℚ) : ℕ → Cell :=
  let candidate := scanCandidateValues P values index good bad
  let score := (P.cachedEndpoint P.endpointCache index).charge+
    (1-(P.cachedEndpoint P.endpointCache index).error)*good+(P.cachedEndpoint P.endpointCache index).error*bad
  scanAdvanceValues (if score < best then minimumUpdateValues candidate else candidate) index (source+(1+2*index))

end PDCompute.Solver
