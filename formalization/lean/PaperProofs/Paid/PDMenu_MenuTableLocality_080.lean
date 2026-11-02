module

public import PaperProofs.Paid.PDMenu_MenuRowLocality_078
public import PaperProofs.Paid.PDMenu_MenuStoredRecursion_079

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDMenu

open PaperProofs.Paid PaperProofs.Paid.Parameters

/-- Width independence of actual stored MenuEntry records. This preserves
the original least-tie selected action, not merely its optimal objective. -/
theorem solveMenuTable_last_cell_width (P : Parameters) (fee penalty : ℚ) (N : ℕ) :
    ∀ (K L k : ℕ), k ≤ K → k ≤ L →
      menuEntryAt (P.solveMenuTable fee penalty K N) N k = menuEntryAt (P.solveMenuTable fee penalty L N) N k := by
  induction N with
  | zero =>
    intro K L k hk hl
    change (baseMenuRow K).getD k abandonEntry = (baseMenuRow L).getD k abandonEntry
    rw [baseMenuRow_getD K k hk, baseMenuRow_getD L k hl]
  | succ N ih =>
    intro K L k hk hl
    rw [solveMenuTable_last_entry_succ P fee penalty K N k hk,
      solveMenuTable_last_entry_succ P fee penalty L N k hl]
    apply nextMenuEntry_congr_previous
    intro j hj
    exact ih K L j (hj.trans hk) (hj.trans hl)

/-- All genuine queried subproblems of any two sufficiently large complete
tables contain exactly the same original action/observation/repair/failure
record, with no numerical or policy-performance assumptions. -/
theorem solveMenuTable_cell_locality (P : Parameters) (fee penalty : ℚ) (N K M L n k : ℕ)
    (hn : n ≤ N) (hm : n ≤ M) (hk : k ≤ K) (hl : k ≤ L) :
    menuEntryAt (P.solveMenuTable fee penalty K N) n k = menuEntryAt (P.solveMenuTable fee penalty L M) n k := by
  rw [solveMenuTable_cell_prefix P fee penalty K N n hn k,
    solveMenuTable_cell_prefix P fee penalty L M n hm k]
  exact solveMenuTable_last_cell_width P fee penalty n K L k hk hl

end PDMenu
