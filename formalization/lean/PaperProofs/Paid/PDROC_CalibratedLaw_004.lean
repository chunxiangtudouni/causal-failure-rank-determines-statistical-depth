module

public import PaperProofs.Paid.PDROC_CalibratedLaw_001
public import PaperProofs.Paid.PDMenu_MenuTableBounds_061

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters

namespace PDROC.CalibratedLaw

def EntryLevelsValid (P : Parameters) (entry : MenuEntry) : Prop :=
  ∀ level bad, entry.action = .test level bad → level ≤ P.certificate.M

/-- All actual stored and defaulted table cells respect the original
finite calibration range. This is data validity, never a performance field. -/
def TableLevelsValid (P : Parameters) (table : MenuTable) : Prop :=
  ∀ n k, EntryLevelsValid P (menuEntryAt table n k)

theorem finishEntry_levelsValid (P : Parameters) : EntryLevelsValid P finishEntry := by
  intro level bad action
  cases action

theorem abandonEntry_levelsValid (P : Parameters) : EntryLevelsValid P abandonEntry := by
  intro level bad action
  cases action

theorem nextMenuEntry_levelsValid (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (k : ℕ) :
    EntryLevelsValid P (P.nextMenuEntry fee penalty previous k) := by
  intro level bad action
  simp only [nextMenuEntry] at action
  split_ifs at action with zero abandon
  · cases action
  · cases action
  · change MenuAction.test (P.leastTestingLevel fee penalty previous k)
      (P.menuBadBranch fee penalty previous k).1 = .test level bad at action
    injection action with levelEq _badEq
    rw [← levelEq]
    exact (P.leastTestingLevel_spec fee penalty previous k).1

theorem baseMenuRow_levelsValid (P : Parameters) (K k : ℕ) :
    EntryLevelsValid P ((baseMenuRow K).getD k abandonEntry) := by
  by_cases hk : k < K + 1
  · have hs : k < (baseMenuRow K).size := by simpa only [baseMenuRow_size] using hk
    have he : (baseMenuRow K).getD k abandonEntry = finishEntry :=
      (Array.getElem_eq_getD (h := hs) abandonEntry).symm.trans (Array.getElem_replicate hs)
    rw [he]
    exact finishEntry_levelsValid P
  · rw [PDMenu.menuArray_getD_outside _ _ _ (by simpa only [baseMenuRow_size] using Nat.le_of_not_gt hk)]
    exact abandonEntry_levelsValid P

theorem nextMenuRow_levelsValid (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (K k : ℕ) :
    EntryLevelsValid P ((P.nextMenuRow fee penalty previous K).getD k abandonEntry) := by
  by_cases hk : k < K + 1
  · have hs : k < (P.nextMenuRow fee penalty previous K).size := by simpa only [nextMenuRow_size] using hk
    have he : (P.nextMenuRow fee penalty previous K).getD k abandonEntry = P.nextMenuEntry fee penalty previous k :=
      (Array.getElem_eq_getD (h := hs) abandonEntry).symm.trans (Array.getElem_ofFn hs)
    rw [he]
    exact nextMenuEntry_levelsValid P fee penalty previous k
  · rw [PDMenu.menuArray_getD_outside _ _ _ (by simpa only [nextMenuRow_size] using Nat.le_of_not_gt hk)]
    exact abandonEntry_levelsValid P

/-- Unconditional intrinsic validity of the actual generated Array,
including every out-of-range getter and signed fee/penalty input. -/
theorem solveMenuTable_levelsValid (P : Parameters) (fee penalty : ℚ) (N K : ℕ) :
    TableLevelsValid P (P.solveMenuTable fee penalty K N) := by
  induction N with
  | zero =>
    intro n k
    by_cases hn : n = 0
    · subst n
      change EntryLevelsValid P ((baseMenuRow K).getD k abandonEntry)
      exact baseMenuRow_levelsValid P K k
    · change EntryLevelsValid P (((#[baseMenuRow K] : MenuTable).getD n #[]).getD k abandonEntry)
      rw [PDMenu.menuArray_getD_outside (#[baseMenuRow K] : MenuTable) n #[] (by change 1 ≤ n; omega),
        PDMenu.menuArray_getD_outside (#[] : MenuRow) k abandonEntry (by change 0 ≤ k; omega)]
      exact abandonEntry_levelsValid P
  | succ N ih =>
    intro n k
    let table := P.solveMenuTable fee penalty K N
    let next := P.nextMenuRow fee penalty (table.getD N (baseMenuRow K)) K
    change EntryLevelsValid P (((table.push next).getD n #[]).getD k abandonEntry)
    rw [PDMenu.menuArray_getD_push]
    by_cases hn : n = table.size
    · rw [ite_eq_left hn]
      exact nextMenuRow_levelsValid P fee penalty _ K k
    · rw [ite_eq_right hn]
      exact ih n k

end PDROC.CalibratedLaw
