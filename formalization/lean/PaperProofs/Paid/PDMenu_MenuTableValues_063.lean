module

public import PaperProofs.Paid.PDMenu_MenuStepValues_062

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

open scoped ENNReal

namespace PDMenu

open PaperProofs.Paid PaperProofs.Paid.Parameters

/-- True independently defined full-policy values of every actual stored
cell. The invariant is proved for the complete original computed table. -/
theorem solveMenuTable_value (P : Parameters) (fee penalty : ℚ) (hfee : 0 ≤ fee) (hpenalty : 0 ≤ penalty)
    (hLambda : penalty ≤ P.Lambda) (N K : ℕ) :
    ∀ n : ℕ, n ≤ N → ∀ k : ℕ, k ≤ K →
      P.freshPaidPenalty fee hfee n k (ENNReal.ofReal (penalty : ℝ)) =
        ENNReal.ofReal ((menuEntryAt (P.solveMenuTable fee penalty K N) n k).objective fee penalty : ℝ) := by
  induction N with
  | zero =>
    intro n hn k hk
    have hn0 : n = 0 := by omega
    subst n
    have hsize : k < (baseMenuRow K).size := by rw [baseMenuRow_size]; omega
    have hentry : (baseMenuRow K).getD k abandonEntry = finishEntry :=
      (Array.getElem_eq_getD (h := hsize) abandonEntry).symm.trans (Array.getElem_replicate hsize)
    change P.freshPaidPenalty fee hfee 0 k (ENNReal.ofReal (penalty : ℝ)) =
      ENNReal.ofReal (((baseMenuRow K).getD k abandonEntry).objective fee penalty : ℝ)
    rw [hentry, P.freshPaidPenalty_empty]
    simp only [finishEntry, MenuEntry.objective, mul_zero, add_zero, Rat.cast_zero, ENNReal.ofReal_zero]
  | succ N ih =>
    intro n hn k hk
    let table := P.solveMenuTable fee penalty K N
    let previous := table.getD N (baseMenuRow K)
    let next := P.nextMenuRow fee penalty previous K
    have hsize : table.size = N + 1 := P.solveMenuTable_size fee penalty K N
    by_cases heq : n = N + 1
    · subst n
      have hprevious : previous = table.getD N #[] :=
        menuArray_getD_fallback table N (baseMenuRow K) #[] (by rw [hsize]; omega)
      have hstats : ∀ j : ℕ, MenuStatsBound (previous.getD j abandonEntry) N j := by
        intro j
        rw [hprevious]
        exact solveMenuTable_stats P fee penalty N K N le_rfl j
      have hvalues : ∀ j : ℕ, j ≤ K →
          P.freshPaidPenalty fee hfee N j (ENNReal.ofReal (penalty : ℝ)) =
            ENNReal.ofReal ((previous.getD j abandonEntry).objective fee penalty : ℝ) := by
        intro j hj
        rw [hprevious]
        exact ih N le_rfl j hj
      have hrow : (P.solveMenuTable fee penalty K (N + 1)).getD (N + 1) #[] = next := by
        change (table.push next).getD (N + 1) #[] = next
        rw [menuArray_getD_push, hsize]
        exact ite_eq_left rfl
      have hnextSize : k < next.size := by rw [Parameters.nextMenuRow_size]; omega
      have hentry : next.getD k abandonEntry = P.nextMenuEntry fee penalty previous k :=
        (Array.getElem_eq_getD (h := hnextSize) abandonEntry).symm.trans (Array.getElem_ofFn hnextSize)
      change P.freshPaidPenalty fee hfee (N + 1) k (ENNReal.ofReal (penalty : ℝ)) =
        ENNReal.ofReal ((((P.solveMenuTable fee penalty K (N + 1)).getD (N + 1) #[]).getD k abandonEntry).objective fee penalty : ℝ)
      rw [hrow, hentry]
      exact nextMenuEntry_value_eq P fee penalty hfee hpenalty hLambda previous N K k hk hstats hvalues
    · have hnOld : n ≤ N := by omega
      have hrow : (P.solveMenuTable fee penalty K (N + 1)).getD n #[] = table.getD n #[] := by
        change (table.push next).getD n #[] = table.getD n #[]
        rw [menuArray_getD_push]
        exact ite_eq_right (by rw [hsize]; exact heq)
      change P.freshPaidPenalty fee hfee n k (ENNReal.ofReal (penalty : ℝ)) =
        ENNReal.ofReal ((((P.solveMenuTable fee penalty K (N + 1)).getD n #[]).getD k abandonEntry).objective fee penalty : ℝ)
      rw [hrow]
      exact ih n hnOld k hk

/-- Complete original D18 computed-table/full-history-infimum value field.
Native means and guard behavior remain separate original obligations. -/
theorem menuTableValueCorrect (P : Parameters) : P.MenuTableValueCorrect := by
  intro fee penalty hfee hpenalty hLambda N K n k hn hk
  exact solveMenuTable_value P fee penalty hfee hpenalty hLambda N K n hn k hk

end PDMenu

