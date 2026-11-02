module

public import PaperProofs.Paid.PDMenu_MenuTableValues_063

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Paid PaperProofs.Paid.Parameters

/-- The compiler's literal first-occurrence finite argmin is the ORIGINAL
least full endpoint minimizer, including the case outer abandonment wins. -/
theorem leastTestingLevel_isLeastPaid (P : Parameters) (fee penalty : ℚ) (hfee : 0 ≤ fee) (hpenalty : 0 ≤ penalty)
    (hLambda : penalty ≤ P.Lambda) (previous : MenuRow) (n K k : ℕ) (hk : k ≤ K)
    (hstats : ∀ j : ℕ, MenuStatsBound (previous.getD j abandonEntry) n j)
    (hvalues : ∀ j : ℕ, j ≤ K → P.freshPaidPenalty fee hfee n j (ENNReal.ofReal (penalty : ℝ)) =
      ENNReal.ofReal ((previous.getD j abandonEntry).objective fee penalty : ℝ)) :
    P.IsLeastPaidEndpointMinimizer fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ))
      (P.leastTestingLevel fee penalty previous k) := by
  let chosen := P.leastTestingLevel fee penalty previous k
  let objective := fun m => P.paidEndpointObjective fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ)) m
  have hs := P.leastTestingLevel_spec fee penalty previous k
  have hmap := menuTestingEntry_value_eq P fee penalty hfee hpenalty previous n K k hk hstats hvalues
  have hchosen : objective chosen = ⨅ m, objective m :=
    (hmap chosen).symm.trans (leastTestingLevel_value_inf P fee penalty hfee hpenalty hLambda previous n K k hk hstats hvalues)
  have hopt : P.IsPaidEndpointMinimizer fee hfee (n + 1) k (ENNReal.ofReal (penalty : ℝ)) chosen := by
    intro m
    exact hchosen.le.trans (iInf_le objective m)
  refine ⟨hopt, ?_⟩
  intro m hm
  by_cases hbound : m ≤ P.certificate.M
  · have hEq : objective chosen = objective m := le_antisymm (hopt m) (hm chosen)
    have hENN : ENNReal.ofReal ((P.menuTestingEntry fee penalty previous k chosen).objective fee penalty : ℝ) =
        ENNReal.ofReal ((P.menuTestingEntry fee penalty previous k m).objective fee penalty : ℝ) :=
      (hmap chosen).trans (hEq.trans (hmap m).symm)
    have hnonneg (m : ℕ) : 0 ≤ ((P.menuTestingEntry fee penalty previous k m).objective fee penalty : ℝ) := by
      exact_mod_cast menuEntry_objective_nonneg (menuTestingEntry_stats P fee penalty previous n k m (hstats k)
        (menuBadBranch_stats P fee penalty previous n k hstats)) fee penalty hfee hpenalty
    have hReal := (ENNReal.ofReal_eq_ofReal_iff (hnonneg chosen) (hnonneg m)).mp hENN
    have hRat : (P.menuTestingEntry fee penalty previous k chosen).objective fee penalty =
        (P.menuTestingEntry fee penalty previous k m).objective fee penalty := by exact_mod_cast hReal
    exact hs.2.2 m hbound hRat
  · exact hs.1.trans (Nat.le_of_lt (lt_of_not_ge hbound))

/-- Actual stored predecessor rows, every original queried cell, original
Lambda/M and all least-tie semantics. No value identity is supplied as input. -/
theorem storedLeastTestingLevel_isLeastPaid (P : Parameters) (fee penalty : ℚ) (hfee : 0 ≤ fee) (hpenalty : 0 ≤ penalty)
    (hLambda : penalty ≤ P.Lambda) (N K n k : ℕ) (hn : 0 < n) (hnN : n ≤ N) (hk : k ≤ K) :
    let table := P.solveMenuTable fee penalty K N
    let previous := table.getD (n - 1) (baseMenuRow K)
    P.IsLeastPaidEndpointMinimizer fee hfee n k (ENNReal.ofReal (penalty : ℝ))
      (P.leastTestingLevel fee penalty previous k) := by
  intro table previous
  have hindex : n - 1 < table.size := by rw [P.solveMenuTable_size]; omega
  have hprev : previous = table.getD (n - 1) #[] :=
    menuArray_getD_fallback table (n - 1) (baseMenuRow K) #[] hindex
  have hstats : ∀ j : ℕ, MenuStatsBound (previous.getD j abandonEntry) (n - 1) j := by
    intro j
    rw [hprev]
    exact solveMenuTable_stats P fee penalty N K (n - 1) (by omega) j
  have hvalues : ∀ j : ℕ, j ≤ K → P.freshPaidPenalty fee hfee (n - 1) j (ENNReal.ofReal (penalty : ℝ)) =
      ENNReal.ofReal ((previous.getD j abandonEntry).objective fee penalty : ℝ) := by
    intro j hj
    rw [hprev]
    exact solveMenuTable_value P fee penalty hfee hpenalty hLambda N K (n - 1) (by omega) j hj
  have he := leastTestingLevel_isLeastPaid P fee penalty hfee hpenalty hLambda previous (n - 1) K k hk hstats hvalues
  have hnEq : n - 1 + 1 = n := by omega
  simpa only [hnEq] using he

end PDMenu
