module

public import PaperProofs.Paid.MenuCompiler

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PDMenu

open PaperProofs.Paid

/-- The original next cell reads only columns up to its genuine tool
snapshot. Actions and tie choices, not only objective values, are preserved. -/
theorem menuBadBranch_congr_previous (P : Parameters) (fee penalty : ℚ) (left right : MenuRow) (tools : ℕ)
    (hprevious : ∀ j : ℕ, j ≤ tools → left.getD j abandonEntry = right.getD j abandonEntry) :
    P.menuBadBranch fee penalty left tools = P.menuBadBranch fee penalty right tools := by
  cases tools with
  | zero => rfl
  | succ tools =>
    dsimp only [Parameters.menuBadBranch]
    rw [hprevious tools (Nat.le_succ tools)]

theorem menuTestingEntry_congr_previous (P : Parameters) (fee penalty : ℚ) (left right : MenuRow) (tools level : ℕ)
    (hprevious : ∀ j : ℕ, j ≤ tools → left.getD j abandonEntry = right.getD j abandonEntry) :
    P.menuTestingEntry fee penalty left tools level = P.menuTestingEntry fee penalty right tools level := by
  simp only [Parameters.menuTestingEntry, hprevious tools le_rfl,
    menuBadBranch_congr_previous P fee penalty left right tools hprevious]

theorem leastTestingLevel_congr_previous (P : Parameters) (fee penalty : ℚ) (left right : MenuRow) (tools : ℕ)
    (hprevious : ∀ j : ℕ, j ≤ tools → left.getD j abandonEntry = right.getD j abandonEntry) :
    P.leastTestingLevel fee penalty left tools = P.leastTestingLevel fee penalty right tools := by
  have hobjectives : (fun level => (P.menuTestingEntry fee penalty left tools level).objective fee penalty) =
      (fun level => (P.menuTestingEntry fee penalty right tools level).objective fee penalty) := by
    funext level
    rw [menuTestingEntry_congr_previous P fee penalty left right tools level hprevious]
  unfold Parameters.leastTestingLevel
  rw [hobjectives]

theorem nextMenuEntry_congr_previous (P : Parameters) (fee penalty : ℚ) (left right : MenuRow) (tools : ℕ)
    (hprevious : ∀ j : ℕ, j ≤ tools → left.getD j abandonEntry = right.getD j abandonEntry) :
    P.nextMenuEntry fee penalty left tools = P.nextMenuEntry fee penalty right tools := by
  unfold Parameters.nextMenuEntry
  rw [leastTestingLevel_congr_previous P fee penalty left right tools hprevious,
    menuTestingEntry_congr_previous P fee penalty left right tools (P.leastTestingLevel fee penalty right tools) hprevious]

end PDMenu
