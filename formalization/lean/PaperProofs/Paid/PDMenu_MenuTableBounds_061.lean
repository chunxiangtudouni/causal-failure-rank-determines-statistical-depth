module

public import PaperProofs.Paid.PDMenu_MenuEntryBounds_060

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu

open PaperProofs.Paid PaperProofs.Paid.Parameters

theorem menuArray_getD_push {α : Type*} (xs : Array α) (x fallback : α) (i : ℕ) :
    (xs.push x).getD i fallback = if i = xs.size then x else xs.getD i fallback := by
  simp only [Array.getD_eq_getD_getElem?, Array.getElem?_push]
  split_ifs <;> rfl

theorem menuArray_getD_outside {α : Type*} (xs : Array α) (i : ℕ) (fallback : α) (h : xs.size ≤ i) :
    xs.getD i fallback = fallback := by
  rw [Array.getD_eq_getD_getElem?, Array.getElem?_eq_none h]
  rfl

theorem menuArray_getD_fallback {α : Type*} (xs : Array α) (i : ℕ) (left right : α) (h : i < xs.size) :
    xs.getD i left = xs.getD i right := by
  exact (Array.getElem_eq_getD (h := h) left).symm.trans (Array.getElem_eq_getD (h := h) right)

theorem baseMenuRow_stats (tools : ℕ) :
    ∀ k : ℕ, MenuStatsBound ((baseMenuRow tools).getD k abandonEntry) 0 k := by
  intro k
  by_cases hk : k < tools + 1
  · have hsize : k < (baseMenuRow tools).size := by simpa only [baseMenuRow_size] using hk
    have hget : (baseMenuRow tools).getD k abandonEntry = finishEntry := by
      exact (Array.getElem_eq_getD (h := hsize) abandonEntry).symm.trans (Array.getElem_replicate hsize)
    rw [hget]
    exact finishEntry_stats 0 k
  · rw [menuArray_getD_outside _ _ _ (by simpa only [baseMenuRow_size] using Nat.le_of_not_gt hk)]
    exact abandonEntry_stats 0 k

theorem nextMenuRow_stats (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (n tools : ℕ)
    (hprevious : ∀ k : ℕ, MenuStatsBound (previous.getD k abandonEntry) n k) :
    ∀ k : ℕ, MenuStatsBound ((P.nextMenuRow fee penalty previous tools).getD k abandonEntry) (n + 1) k := by
  intro k
  by_cases hk : k < tools + 1
  · have hsize : k < (P.nextMenuRow fee penalty previous tools).size := by
      simpa only [Parameters.nextMenuRow_size] using hk
    have hget : (P.nextMenuRow fee penalty previous tools).getD k abandonEntry =
        P.nextMenuEntry fee penalty previous k := by
      exact (Array.getElem_eq_getD (h := hsize) abandonEntry).symm.trans (Array.getElem_ofFn hsize)
    rw [hget]
    exact nextMenuEntry_stats P fee penalty previous n k hprevious
  · rw [menuArray_getD_outside _ _ _ (by simpa only [Parameters.nextMenuRow_size] using Nat.le_of_not_gt hk)]
    exact abandonEntry_stats (n + 1) k

/-- Every actually stored row has the correct n,k numerical ranges. The
out-of-width fallback is covered too, so no hidden getter-validity premise
is used to justify a sign or probability. -/
theorem solveMenuTable_stats (P : Parameters) (fee penalty : ℚ) (N K : ℕ) :
    ∀ n : ℕ, n ≤ N → ∀ k : ℕ,
      MenuStatsBound (menuEntryAt (P.solveMenuTable fee penalty K N) n k) n k := by
  induction N with
  | zero =>
    intro n hn k
    have hn0 : n = 0 := by omega
    subst n
    change MenuStatsBound ((baseMenuRow K).getD k abandonEntry) 0 k
    exact baseMenuRow_stats K k
  | succ N ih =>
    intro n hn k
    let table := P.solveMenuTable fee penalty K N
    let previous := table.getD N (baseMenuRow K)
    let next := P.nextMenuRow fee penalty previous K
    have hsize : table.size = N + 1 := P.solveMenuTable_size fee penalty K N
    by_cases heq : n = N + 1
    · subst n
      have hprevious : ∀ k : ℕ, MenuStatsBound (previous.getD k abandonEntry) N k := by
        intro k
        have he : previous = table.getD N #[] :=
          menuArray_getD_fallback table N (baseMenuRow K) #[] (by rw [hsize]; omega)
        rw [he]
        exact ih N le_rfl k
      have hrow : (P.solveMenuTable fee penalty K (N + 1)).getD (N + 1) #[] = next := by
        change (table.push next).getD (N + 1) #[] = next
        rw [menuArray_getD_push, hsize]
        exact ite_eq_left rfl
      change MenuStatsBound (((P.solveMenuTable fee penalty K (N + 1)).getD (N + 1) #[]).getD k abandonEntry) (N + 1) k
      rw [hrow]
      exact nextMenuRow_stats P fee penalty previous N K hprevious k
    · have hnOld : n ≤ N := by omega
      have hrow : (P.solveMenuTable fee penalty K (N + 1)).getD n #[] = table.getD n #[] := by
        change (table.push next).getD n #[] = table.getD n #[]
        rw [menuArray_getD_push]
        exact ite_eq_right (by rw [hsize]; exact heq)
      change MenuStatsBound (((P.solveMenuTable fee penalty K (N + 1)).getD n #[]).getD k abandonEntry) n k
      rw [hrow]
      exact ih n hnOld k

/-- Complete original D18 numeric table-bounds field, without a Bellman,
compiler-performance or data-sign assumption. -/
theorem menuTableStatsBounds (P : Parameters) : P.MenuTableStatsBounds := by
  intro fee penalty _hfee _hpenalty N K n k hn _hk
  exact solveMenuTable_stats P fee penalty N K n hn k

end PDMenu

