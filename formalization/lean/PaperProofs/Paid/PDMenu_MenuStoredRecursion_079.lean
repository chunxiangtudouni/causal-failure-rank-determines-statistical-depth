module

public import PaperProofs.Paid.PDMenu_MenuTableBounds_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu

open PaperProofs.Paid PaperProofs.Paid.Parameters

theorem baseMenuRow_getD (K k : ℕ) (hk : k ≤ K) :
    (baseMenuRow K).getD k abandonEntry = finishEntry := by
  have hsize : k < (baseMenuRow K).size := by rw [baseMenuRow_size]; omega
  exact (Array.getElem_eq_getD (h := hsize) abandonEntry).symm.trans (Array.getElem_replicate hsize)

theorem nextMenuRow_getD (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (K k : ℕ) (hk : k ≤ K) :
    (P.nextMenuRow fee penalty previous K).getD k abandonEntry = P.nextMenuEntry fee penalty previous k := by
  have hsize : k < (P.nextMenuRow fee penalty previous K).size := by rw [P.nextMenuRow_size]; omega
  exact (Array.getElem_eq_getD (h := hsize) abandonEntry).symm.trans (Array.getElem_ofFn hsize)

theorem solveMenuTable_last_row (P : Parameters) (fee penalty : ℚ) (K N : ℕ) :
    (P.solveMenuTable fee penalty K (N + 1)).getD (N + 1) #[] =
      P.nextMenuRow fee penalty ((P.solveMenuTable fee penalty K N).getD N (baseMenuRow K)) K := by
  change ((P.solveMenuTable fee penalty K N).push _).getD (N + 1) #[] = _
  rw [menuArray_getD_push, P.solveMenuTable_size]
  exact ite_eq_left rfl

theorem solveMenuTable_last_entry_succ (P : Parameters) (fee penalty : ℚ) (K N k : ℕ) (hk : k ≤ K) :
    menuEntryAt (P.solveMenuTable fee penalty K (N + 1)) (N + 1) k =
      P.nextMenuEntry fee penalty ((P.solveMenuTable fee penalty K N).getD N #[]) k := by
  unfold menuEntryAt
  rw [solveMenuTable_last_row, nextMenuRow_getD P fee penalty _ K k hk]
  have hvalid : N < (P.solveMenuTable fee penalty K N).size := by rw [P.solveMenuTable_size]; omega
  rw [menuArray_getD_fallback _ N (baseMenuRow K) #[] hvalid]

/-- Growing the complete table preserves every previously stored cell,
including the literal action and each rational statistic. -/
theorem solveMenuTable_cell_prefix (P : Parameters) (fee penalty : ℚ) (K N : ℕ) :
    ∀ n : ℕ, n ≤ N → ∀ k : ℕ,
      menuEntryAt (P.solveMenuTable fee penalty K N) n k = menuEntryAt (P.solveMenuTable fee penalty K n) n k := by
  induction N with
  | zero =>
    intro n hn k
    have hn0 : n = 0 := by omega
    subst n
    rfl
  | succ N ih =>
    intro n hn k
    by_cases heq : n = N + 1
    · subst n
      rfl
    · have hnOld : n ≤ N := by omega
      let table := P.solveMenuTable fee penalty K N
      let next := P.nextMenuRow fee penalty (table.getD N (baseMenuRow K)) K
      have hsize : table.size = N + 1 := P.solveMenuTable_size fee penalty K N
      have hrow : (P.solveMenuTable fee penalty K (N + 1)).getD n #[] = table.getD n #[] := by
        change (table.push next).getD n #[] = table.getD n #[]
        rw [menuArray_getD_push]
        exact ite_eq_right (by rw [hsize]; exact heq)
      change (((P.solveMenuTable fee penalty K (N + 1)).getD n #[]).getD k abandonEntry) = _
      rw [hrow]
      exact ih n hnOld k

end PDMenu
