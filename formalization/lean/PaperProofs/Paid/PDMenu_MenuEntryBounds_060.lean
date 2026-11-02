module

public import PaperProofs.Paid.MenuCompiler

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDMenu

open PaperProofs.Paid

/-- Numeric record invariant only; no native legality, performance or
optimality is assumed as part of an entry. -/
def MenuStatsBound (entry : MenuEntry) (stages tools : ℕ) : Prop :=
  0 ≤ entry.observation ∧ 0 ≤ entry.repairs ∧ entry.repairs ≤ (min stages tools : ℕ) ∧
    0 ≤ entry.failure ∧ entry.failure ≤ 1

theorem finishEntry_stats (stages tools : ℕ) : MenuStatsBound finishEntry stages tools :=
  ⟨le_rfl, le_rfl, Nat.cast_nonneg _, le_rfl, zero_le_one⟩

theorem abandonEntry_stats (stages tools : ℕ) : MenuStatsBound abandonEntry stages tools :=
  ⟨le_rfl, le_rfl, Nat.cast_nonneg _, zero_le_one, le_rfl⟩

theorem MenuStatsBound.mono {entry : MenuEntry} {n k n' k' : ℕ}
    (h : MenuStatsBound entry n k) (hn : n ≤ n') (hk : k ≤ k') : MenuStatsBound entry n' k' := by
  refine ⟨h.1, h.2.1, h.2.2.1.trans ?_, h.2.2.2.1, h.2.2.2.2⟩
  exact_mod_cast min_le_min hn hk

theorem repairEntry_stats {entry : MenuEntry} (n k : ℕ) (h : MenuStatsBound entry n k) :
    MenuStatsBound (repairEntry entry) (n + 1) (k + 1) := by
  have hcapNat : 1 + min n k ≤ min (n + 1) (k + 1) := by
    have hn := min_le_left n k
    have hk := min_le_right n k
    exact le_min (by omega) (by omega)
  have hcap : (1 : ℚ) + (min n k : ℕ) ≤ (min (n + 1) (k + 1) : ℕ) := by exact_mod_cast hcapNat
  refine ⟨h.1, add_nonneg zero_le_one h.2.1, ?_, h.2.2.2.1, h.2.2.2.2⟩
  exact (add_le_add le_rfl h.2.2.1).trans hcap

/-- Bounds are preserved by the ACTUAL bad branch, including its original
fee-dependent decision between real repair and abandonment. -/
theorem menuBadBranch_stats (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (n tools : ℕ)
    (hprevious : ∀ k : ℕ, MenuStatsBound (previous.getD k abandonEntry) n k) :
    MenuStatsBound (P.menuBadBranch fee penalty previous tools).2 (n + 1) tools := by
  cases tools with
  | zero => exact abandonEntry_stats (n + 1) 0
  | succ tools =>
    dsimp only [Parameters.menuBadBranch]
    split_ifs
    · exact repairEntry_stats n tools (hprevious tools)
    · exact abandonEntry_stats (n + 1) (tools + 1)

theorem menuTestingEntry_stats (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (n tools level : ℕ)
    (hgood : MenuStatsBound (previous.getD tools abandonEntry) n tools)
    (hbad : MenuStatsBound (P.menuBadBranch fee penalty previous tools).2 (n + 1) tools) :
    MenuStatsBound (P.menuTestingEntry fee penalty previous tools level) (n + 1) tools := by
  let good := previous.getD tools abandonEntry
  let bad := (P.menuBadBranch fee penalty previous tools).2
  let p := P.binarySymmetric.endpointError level
  have hp : 0 ≤ p := (P.binarySymmetric.endpointError_pos level).le
  have hpone : p ≤ 1 := (P.binarySymmetric.endpointError_le_half level).trans (by norm_num)
  have hq : 0 ≤ 1 - p := sub_nonneg.mpr hpone
  have hg : MenuStatsBound good (n + 1) tools := hgood.mono (Nat.le_succ n) le_rfl
  let cap : ℚ := (min (n + 1) tools : ℕ)
  change 0 ≤ P.binarySymmetric.endpointCharge level + (1 - p) * good.observation + p * bad.observation ∧
    0 ≤ (1 - p) * good.repairs + p * bad.repairs ∧
    (1 - p) * good.repairs + p * bad.repairs ≤ cap ∧
    0 ≤ (1 - p) * good.failure + p * bad.failure ∧
    (1 - p) * good.failure + p * bad.failure ≤ 1
  refine ⟨add_nonneg (add_nonneg (P.binarySymmetric.endpointCharge_nonneg level)
      (mul_nonneg hq hg.1)) (mul_nonneg hp hbad.1),
    add_nonneg (mul_nonneg hq hg.2.1) (mul_nonneg hp hbad.2.1), ?_,
    add_nonneg (mul_nonneg hq hg.2.2.2.1) (mul_nonneg hp hbad.2.2.2.1), ?_⟩
  · calc
      _ ≤ (1 - p) * cap + p * cap := add_le_add
        (mul_le_mul_of_nonneg_left hg.2.2.1 hq) (mul_le_mul_of_nonneg_left hbad.2.2.1 hp)
      _ = cap := by ring
  · calc
      _ ≤ (1 - p) * 1 + p * 1 := add_le_add
        (mul_le_mul_of_nonneg_left hg.2.2.2.2 hq) (mul_le_mul_of_nonneg_left hbad.2.2.2.2 hp)
      _ = 1 := by ring

theorem nextMenuEntry_stats (P : Parameters) (fee penalty : ℚ) (previous : MenuRow) (n tools : ℕ)
    (hprevious : ∀ k : ℕ, MenuStatsBound (previous.getD k abandonEntry) n k) :
    MenuStatsBound (P.nextMenuEntry fee penalty previous tools) (n + 1) tools := by
  dsimp only [Parameters.nextMenuEntry]
  split_ifs
  · exact abandonEntry_stats (n + 1) tools
  · exact abandonEntry_stats (n + 1) tools
  · exact menuTestingEntry_stats P fee penalty previous n tools _ (hprevious tools)
      (menuBadBranch_stats P fee penalty previous n tools hprevious)

end PDMenu
