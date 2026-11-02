module

public import PaperProofs.Structure.Game
public import Mathlib.Data.ENat.Monoid
public import Mathlib.Data.Finset.Lattice.Fold

/-!
The structural-to-statistical rank interface in laminar-proofs.tex:188--231.
All ranks still come from the independent plan/play semantics in `Game`.
The finite supremum below is semantic and does not claim a polynomial-time
method for computing ranks or selecting tools; that is the capacity algorithm.
-/

@[expose] public section

namespace PaperProofs.Structure

variable {Tool : Type*} [DecidableEq Tool]

/-- Keeping more unused tools preserves causal safety. -/
theorem safe_tools_mono (stages : List (Finset Tool))
    {smaller larger : Finset Tool} (hsub : smaller ⊆ larger) (budget : Nat)
    (hsafe : Safe stages smaller budget) : Safe stages larger budget := by
  induction stages generalizing smaller larger budget with
  | nil => exact safe_terminal larger budget
  | cons eligible later ih =>
    cases budget with
    | zero => exact safe_zero _ _
    | succ budget =>
      obtain ⟨hgood, tool, htool, hbad⟩ := (safe_cons_succ_iff _ _ _ _).mp hsafe
      apply (safe_cons_succ_iff eligible later larger budget).mpr
      refine ⟨ih hsub (budget + 1) hgood, tool, ?_, ?_⟩
      · exact Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp htool).1,
          hsub (Finset.mem_inter.mp htool).2⟩
      · exact ih (Finset.erase_subset_erase tool hsub) budget hbad

private theorem enat_le_of_nat_lt_imp {left right : ℕ∞}
    (h : ∀ budget : Nat, (budget : ℕ∞) < left → (budget : ℕ∞) < right) :
    left ≤ right := by
  apply le_of_not_gt
  intro hlt
  obtain ⟨budget, hbudget⟩ := ENat.ne_top_iff_exists.mp (ne_top_of_lt hlt)
  have hleft : (budget : ℕ∞) < left := by
    rw [hbudget]
    exact hlt
  have impossible := h budget hleft
  rw [hbudget] at impossible
  exact (lt_irrefl right) impossible

private theorem enat_eq_of_nat_lt_iff {left right : ℕ∞}
    (h : ∀ budget : Nat, (budget : ℕ∞) < left ↔ (budget : ℕ∞) < right) :
    left = right :=
  le_antisymm (enat_le_of_nat_lt_imp (fun budget => (h budget).mp))
    (enat_le_of_nat_lt_imp (fun budget => (h budget).mpr))

/-- More unused tools can only increase the independent game rank. -/
theorem errorRank_tools_mono (stages : List (Finset Tool))
    {smaller larger : Finset Tool} (hsub : smaller ⊆ larger) :
    errorRank stages smaller ≤ errorRank stages larger := by
  apply enat_le_of_nat_lt_imp
  intro budget hlt
  apply (safe_iff_lt_errorRank stages larger budget).mp
  exact safe_tools_mono stages hsub budget
    ((safe_iff_lt_errorRank stages smaller budget).mpr hlt)

/-- Maximal erroneous-child rank, with value zero for an empty eligible set.
This is not a redefinition of `errorRank`. -/
noncomputable def badChildRank (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool) : ℕ∞ :=
  (eligible ∩ remaining).sup (fun tool => errorRank later (remaining.erase tool))

/-- Every eligible erroneous successor is bounded by the returned supremum. -/
theorem childRank_le_badChildRank (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool)
    {tool : Tool} (htool : tool ∈ eligible ∩ remaining) :
    errorRank later (remaining.erase tool) ≤ badChildRank eligible later remaining :=
  Finset.le_sup (f := fun tool => errorRank later (remaining.erase tool)) htool

/-- With at least one eligible unused tool, a tool actually attains the
maximal child rank, including when the maximum is infinite. -/
theorem exists_maximizing_tool (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool)
    (hnonempty : (eligible ∩ remaining).Nonempty) :
    ∃ tool ∈ eligible ∩ remaining,
      errorRank later (remaining.erase tool) = badChildRank eligible later remaining := by
  obtain ⟨tool, htool, hmax⟩ := Finset.exists_mem_eq_sup (eligible ∩ remaining)
    hnonempty (fun tool => errorRank later (remaining.erase tool))
  exact ⟨tool, htool, hmax.symm⟩

/-- eq:laminar-bad-existence, stated directly using semantic safe families. -/
theorem lt_badChildRank_iff (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool) (budget : Nat) :
    (budget : ℕ∞) < badChildRank eligible later remaining ↔
      ∃ tool ∈ eligible ∩ remaining, Safe later (remaining.erase tool) budget := by
  simp only [badChildRank, Finset.lt_sup_iff, safe_iff_lt_errorRank]

/-- Zero is reserved for the absence of eligible tools, never a child rank. -/
theorem badChildRank_eq_zero_iff (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool) :
    badChildRank eligible later remaining = 0 ↔ eligible ∩ remaining = ∅ := by
  constructor
  · intro hzero
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro tool htool
    have hle := childRank_le_badChildRank eligible later remaining htool
    rw [hzero] at hle
    exact (not_le_of_gt (errorRank_pos later (remaining.erase tool))) hle
  · intro hempty
    simp only [badChildRank, hempty, Finset.sup_empty, bot_eq_zero]

/-- Losing a tool cannot improve the successor rank. This is the `d_b ≤ d_g`
interface required by the statistical branch analysis. -/
theorem badChildRank_le_goodRank (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool) :
    badChildRank eligible later remaining ≤ errorRank later remaining := by
  apply Finset.sup_le
  intro tool _
  exact errorRank_tools_mono later (Finset.erase_subset tool remaining)

/-- The rank Bellman identity in laminar-proofs.tex:223--227. It follows from
the independent game semantics and finite maximum, not from a definition of
the game value by this recurrence. -/
theorem errorRank_cons (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool) :
    errorRank (eligible :: later) remaining =
      min (errorRank later remaining) (1 + badChildRank eligible later remaining) := by
  apply enat_eq_of_nat_lt_iff
  intro budget
  cases budget with
  | zero =>
    have hpositive : (0 : ℕ∞) < 1 + badChildRank eligible later remaining :=
      lt_of_lt_of_le zero_lt_one (le_add_of_nonneg_right zero_le)
    simp only [ENat.natCast_zero, lt_min_iff, errorRank_pos, hpositive, and_self]
  | succ budget =>
    have hshift : ((budget + 1 : Nat) : ℕ∞) <
        1 + badChildRank eligible later remaining ↔
        (budget : ℕ∞) < badChildRank eligible later remaining := by
      rw [ENat.natCast_add, ENat.natCast_one, add_comm (budget : ℕ∞) 1]
      exact ENat.add_lt_add_iff_left (by simp)
    rw [← safe_iff_lt_errorRank, safe_cons_succ_iff, lt_min_iff, hshift,
      ← safe_iff_lt_errorRank, lt_badChildRank_iff]

/-- An infinite-rank live state has both an infinite correct successor and
an infinite maximal erroneous successor. -/
theorem errorRank_cons_eq_top_iff (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool) :
    errorRank (eligible :: later) remaining = ⊤ ↔
      errorRank later remaining = ⊤ ∧ badChildRank eligible later remaining = ⊤ := by
  rw [errorRank_cons]
  constructor
  · intro htop
    have hgood : errorRank later remaining = ⊤ := by
      apply top_le_iff.mp
      rw [← htop]
      exact min_le_left _ _
    have hbad : 1 + badChildRank eligible later remaining = ⊤ := by
      apply top_le_iff.mp
      rw [← htop]
      exact min_le_right _ _
    exact ⟨hgood, (ENat.add_eq_top.mp hbad).resolve_left ENat.one_ne_top⟩
  · rintro ⟨hgood, hbad⟩
    simp only [hgood, hbad, add_top, min_self]

/-- The infinite-rank successor boundary in laminar-proofs.tex:272--277.
The witness is an actually eligible unused tool, not only a numerical maximum. -/
theorem exists_infinite_child_of_rank_top (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool)
    (htop : errorRank (eligible :: later) remaining = ⊤) :
    ∃ tool ∈ eligible ∩ remaining, errorRank later (remaining.erase tool) = ⊤ := by
  have hbad := ((errorRank_cons_eq_top_iff eligible later remaining).mp htop).2
  have hnonempty : (eligible ∩ remaining).Nonempty := by
    by_contra hempty
    have hzero := (badChildRank_eq_zero_iff eligible later remaining).mpr
      (Finset.not_nonempty_iff_eq_empty.mp hempty)
    rw [hzero] at hbad
    exact ENat.zero_ne_top hbad
  obtain ⟨tool, htool, hmax⟩ := exists_maximizing_tool eligible later remaining hnonempty
  exact ⟨tool, htool, hmax.trans hbad⟩

end PaperProofs.Structure
