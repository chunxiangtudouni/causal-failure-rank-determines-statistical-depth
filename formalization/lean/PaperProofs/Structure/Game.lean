module

public import Mathlib.Data.Finset.Card
public import Mathlib.Data.ENat.Basic
public import Mathlib.Data.Nat.Find

/-!
An independent semantics for the finite allocation game in model.tex:57--74
and laminar-proofs.tex:114--150. A plan contains separate continuations after
an error declaration and after a correct declaration. A play follows those
continuations and stops at the first failed allocation. The adversary chooses
the next declaration after observing every allocation on the current path.

`Safe` is defined by quantification over these plays, not by the capacity DP.
The budget recurrence below is a theorem about that semantics.
-/

@[expose] public section

namespace PaperProofs.Structure

variable {Tool : Type*} [DecidableEq Tool]

/-- A finite causal allocation plan, indexed only by the known stage sequence.
The chosen error tool can depend on the entire preceding branch of this tree.
`decline` permits a failed allocation even if a compatible tool exists. -/
inductive Plan (Tool : Type*) : List (Finset Tool) → Type _ where
  | done : Plan Tool []
  | decline {eligible : Finset Tool} {later : List (Finset Tool)}
      (correct : Plan Tool later) : Plan Tool (eligible :: later)
  | choose {eligible : Finset Tool} {later : List (Finset Tool)}
      (correct : Plan Tool later) (tool : Tool) (error : Plan Tool later) :
      Plan Tool (eligible :: later)

/-- All adversarial plays of a causal plan. The natural number counts errors
up to termination or the first failed allocation. On a repaired error the
adversary sees the actual selected tool before choosing its continuation. -/
inductive Play : {stages : List (Finset Tool)} → Plan Tool stages →
    Finset Tool → Nat → Bool → Prop where
  | terminal (remaining : Finset Tool) : Play .done remaining 0 true
  | correct_decline {eligible : Finset Tool} {later : List (Finset Tool)}
      {good : Plan Tool later}
      {remaining : Finset Tool} {errors : Nat} {success : Bool}
      (continuation : Play good remaining errors success) :
      Play (.decline (eligible := eligible) good) remaining errors success
  | correct_choose {eligible : Finset Tool} {later : List (Finset Tool)}
      {good bad : Plan Tool later} {tool : Tool}
      {remaining : Finset Tool} {errors : Nat} {success : Bool}
      (continuation : Play good remaining errors success) :
      Play (.choose (eligible := eligible) good tool bad) remaining errors success
  | unassigned {eligible : Finset Tool} {later : List (Finset Tool)}
      (good : Plan Tool later) (remaining : Finset Tool) :
      Play (.decline (eligible := eligible) good) remaining 1 false
  | unavailable {eligible : Finset Tool} {later : List (Finset Tool)}
      (good bad : Plan Tool later) (remaining : Finset Tool) (tool : Tool)
      (illegal : tool ∉ eligible ∩ remaining) :
      Play (.choose (eligible := eligible) good tool bad) remaining 1 false
  | repaired {eligible : Finset Tool} {later : List (Finset Tool)}
      {good bad : Plan Tool later} {remaining : Finset Tool} {tool : Tool}
      {errors : Nat} {success : Bool}
      (legal : tool ∈ eligible ∩ remaining)
      (continuation : Play bad (remaining.erase tool) errors success) :
      Play (.choose (eligible := eligible) good tool bad)
        remaining (errors + 1) success

/-- A particular plan handles all plays with at most the stated error budget. -/
def SafePlan {stages : List (Finset Tool)} (plan : Plan Tool stages)
    (remaining : Finset Tool) (budget : Nat) : Prop :=
  ∀ errors, errors ≤ budget → ¬ Play plan remaining errors false

/-- Existential causal safety, independently of any dynamic program. -/
def Safe (stages : List (Finset Tool)) (remaining : Finset Tool)
    (budget : Nat) : Prop :=
  ∃ plan : Plan Tool stages, SafePlan plan remaining budget

theorem play_zero_errors_success {stages : List (Finset Tool)}
    {plan : Plan Tool stages} {remaining : Finset Tool} {errors : Nat} {success : Bool}
    (play : Play plan remaining errors success) (hzero : errors = 0) : success = true := by
  induction play with
  | terminal => rfl
  | correct_decline _ ih => exact ih hzero
  | correct_choose _ ih => exact ih hzero
  | unassigned => cases hzero
  | unavailable => cases hzero
  | repaired => cases hzero

theorem play_failure_has_error {stages : List (Finset Tool)}
    {plan : Plan Tool stages} {remaining : Finset Tool} {errors : Nat}
    (play : Play plan remaining errors false) : 0 < errors := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have impossible := play_zero_errors_success play hzero
  cases impossible

/-- The all-correct branch of any plan is safe at budget zero. -/
theorem safePlan_zero {stages : List (Finset Tool)} (plan : Plan Tool stages)
    (remaining : Finset Tool) : SafePlan plan remaining 0 := by
  intro errors hbudget play
  exact (Nat.not_lt_of_ge hbudget) (play_failure_has_error play)

def declinePlan : (stages : List (Finset Tool)) → Plan Tool stages
  | [] => .done
  | _ :: later => .decline (declinePlan later)

/-- The zero-budget boundary of eq:laminar-boundary. -/
theorem safe_zero (stages : List (Finset Tool)) (remaining : Finset Tool) :
    Safe stages remaining 0 :=
  ⟨declinePlan stages, safePlan_zero _ _⟩

/-- The healthy-terminal boundary of eq:laminar-boundary. -/
theorem safe_terminal (remaining : Finset Tool) (budget : Nat) :
    Safe [] remaining budget := by
  refine ⟨.done, ?_⟩
  intro errors hbudget play
  cases play

theorem safePlan_mono {stages : List (Finset Tool)} {plan : Plan Tool stages}
    {remaining : Finset Tool} {small large : Nat}
    (h : SafePlan plan remaining large) (hle : small ≤ large) :
    SafePlan plan remaining small := by
  intro errors herr
  exact h errors (Nat.le_trans herr hle)

theorem safe_mono {stages : List (Finset Tool)} {remaining : Finset Tool}
    {small large : Nat} (h : Safe stages remaining large) (hle : small ≤ large) :
    Safe stages remaining small := by
  obtain ⟨plan, hp⟩ := h
  exact ⟨plan, safePlan_mono hp hle⟩

/-- Semantic decomposition of one stage. In the error branch the allocator
chooses one tool first; every later play may depend on that realized choice. -/
theorem safe_cons_succ_iff (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool) (budget : Nat) :
    Safe (eligible :: later) remaining (budget + 1) ↔
      Safe later remaining (budget + 1) ∧
      ∃ tool ∈ eligible ∩ remaining, Safe later (remaining.erase tool) budget := by
  constructor
  · rintro ⟨plan, hp⟩
    cases plan with
    | decline good =>
      exact False.elim (hp 1 (Nat.succ_le_succ (Nat.zero_le budget))
        (.unassigned good remaining))
    | choose good tool next =>
      have hgood : SafePlan good remaining (budget + 1) := by
        intro errors herr hplay
        exact hp errors herr (.correct_choose hplay)
      refine ⟨⟨good, hgood⟩, ?_⟩
      have hlegal : tool ∈ eligible ∩ remaining := by
        by_contra hillegal
        exact hp 1 (Nat.succ_le_succ (Nat.zero_le budget))
          (.unavailable good next remaining tool hillegal)
      refine ⟨tool, hlegal, next, ?_⟩
      intro errors herr hplay
      exact hp (errors + 1) (Nat.succ_le_succ herr) (.repaired hlegal hplay)
  · rintro ⟨⟨good, hgood⟩, tool, hlegal, next, hnext⟩
    refine ⟨.choose good tool next, ?_⟩
    intro errors herr hplay
    cases hplay with
    | correct_choose continuation => exact hgood errors herr continuation
    | unavailable _ _ _ _ hillegal => exact hillegal hlegal
    | repaired _ continuation =>
      exact hnext _ (Nat.le_of_succ_le_succ herr) continuation

/-- The extension family in eq:laminar-extension-family, before any capacity
representation is chosen. This uses remaining rather than used tools. -/
def CanExtend (eligible remaining : Finset Tool) (family : Finset Tool → Prop) : Prop :=
  ∃ tool ∈ eligible ∩ remaining, family (remaining.erase tool)

/-- eq:laminar-budget-dp proved from the independent plan/play semantics. -/
theorem budget_recurrence (eligible : Finset Tool)
    (later : List (Finset Tool)) (remaining : Finset Tool) (budget : Nat) :
    Safe (eligible :: later) remaining (budget + 1) ↔
      Safe later remaining (budget + 1) ∧
      CanExtend eligible remaining (fun available => Safe later available budget) :=
  safe_cons_succ_iff eligible later remaining budget

/-- An empty compatibility set is immediately unsafe at every positive budget. -/
theorem not_safe_empty_eligibility (later : List (Finset Tool))
    (remaining : Finset Tool) (budget : Nat) :
    ¬ Safe (∅ :: later) remaining (budget + 1) := by
  intro h
  obtain ⟨_, tool, htool, _⟩ := (safe_cons_succ_iff _ _ _ _).mp h
  simp at htool

/-- In particular, zero tools give finite failure budget one at any live stage. -/
theorem not_safe_no_tools (eligible : Finset Tool)
    (later : List (Finset Tool)) (budget : Nat) :
    ¬ Safe (eligible :: later) ∅ (budget + 1) := by
  intro h
  obtain ⟨_, tool, htool, _⟩ := (safe_cons_succ_iff _ _ _ _).mp h
  simp at htool

/-- Every first-failure play has at most one more error than available tools.
This statement counts errors on successful plays as well. -/
theorem play_errors_le_card_add_one {stages : List (Finset Tool)}
    {plan : Plan Tool stages} {remaining : Finset Tool} {errors : Nat} {success : Bool}
    (play : Play plan remaining errors success) : errors ≤ remaining.card + 1 := by
  induction play with
  | terminal => exact Nat.zero_le _
  | correct_decline _ ih => exact ih
  | correct_choose _ ih => exact ih
  | unassigned => exact Nat.succ_le_succ (Nat.zero_le _)
  | unavailable => exact Nat.succ_le_succ (Nat.zero_le _)
  | repaired legal _ ih =>
    rw [Finset.card_erase_add_one (Finset.mem_inter.mp legal).2] at ih
    exact Nat.succ_le_succ ih

/-- Checking the available-tool count plus one suffices for every budget.
It follows from the independent play bound, not from a bounded DP table. -/
theorem safe_of_card_add_one {stages : List (Finset Tool)} {remaining : Finset Tool}
    (h : Safe stages remaining (remaining.card + 1)) (budget : Nat) :
    Safe stages remaining budget := by
  obtain ⟨plan, hp⟩ := h
  refine ⟨plan, ?_⟩
  intro errors _ play
  exact hp errors (play_errors_le_card_add_one play) play

/-- The minimum adversarial error budget defeating every causal plan, or
infinity if no budget does so. This definition uses the independent game
semantics. Plans are semantic trees and are not claimed to be compact. -/
noncomputable def errorRank (stages : List (Finset Tool))
    (remaining : Finset Tool) : ℕ∞ := by
  classical
  exact if h : ∃ budget, ¬ Safe stages remaining budget then (Nat.find h : ℕ∞) else ⊤

/-- eq:laminar-rank-membership, expressed with remaining tools. -/
theorem safe_iff_lt_errorRank (stages : List (Finset Tool))
    (remaining : Finset Tool) (budget : Nat) :
    Safe stages remaining budget ↔ (budget : ℕ∞) < errorRank stages remaining := by
  classical
  unfold errorRank
  split_ifs with hfail
  · rw [ENat.natCast_lt_natCast, Nat.lt_find_iff]
    constructor
    · intro hsafe smaller hle hnot
      exact hnot (safe_mono hsafe hle)
    · intro hall
      exact not_not.mp (hall budget (Nat.le_refl _))
  · simp only [ENat.natCast_lt_top, iff_true]
    by_contra hnot
    exact hfail ⟨budget, hnot⟩

theorem errorRank_eq_top_iff (stages : List (Finset Tool)) (remaining : Finset Tool) :
    errorRank stages remaining = ⊤ ↔ ∀ budget, Safe stages remaining budget := by
  classical
  constructor
  · intro htop budget
    apply (safe_iff_lt_errorRank stages remaining budget).mpr
    rw [htop]
    exact ENat.natCast_lt_top budget
  · intro hall
    unfold errorRank
    split_ifs with hfail
    · exact False.elim ((Nat.find_spec hfail) (hall (Nat.find hfail)))
    · rfl

/-- Healthy termination has infinite rank even when no tool remains. -/
theorem errorRank_terminal (remaining : Finset Tool) : errorRank [] remaining = ⊤ :=
  (errorRank_eq_top_iff [] remaining).mpr (safe_terminal remaining)

theorem errorRank_pos (stages : List (Finset Tool)) (remaining : Finset Tool) :
    0 < errorRank stages remaining := by
  exact (safe_iff_lt_errorRank stages remaining 0).mp (safe_zero stages remaining)

theorem errorRank_eq_one_of_not_safe_one (stages : List (Finset Tool))
    (remaining : Finset Tool) (h : ¬ Safe stages remaining 1) :
    errorRank stages remaining = 1 := by
  classical
  have hfail : ∃ budget, ¬ Safe stages remaining budget := ⟨1, h⟩
  unfold errorRank
  rw [dite_eq_left hfail]
  have hfind : Nat.find hfail = 1 := by
    apply (Nat.find_eq_iff hfail).mpr
    refine ⟨h, ?_⟩
    intro budget hlt hnot
    have hzero : budget = 0 := Nat.lt_one_iff.mp hlt
    subst budget
    exact hnot (safe_zero stages remaining)
  rw [hfind]
  rfl

/-- The live zero-tool boundary in thm:laminar, including empty eligibility. -/
theorem errorRank_no_tools (eligible : Finset Tool) (later : List (Finset Tool)) :
    errorRank (eligible :: later) ∅ = 1 :=
  errorRank_eq_one_of_not_safe_one _ _ (not_safe_no_tools eligible later 0)

theorem errorRank_empty_eligibility (later : List (Finset Tool))
    (remaining : Finset Tool) : errorRank (∅ :: later) remaining = 1 :=
  errorRank_eq_one_of_not_safe_one _ _ (not_safe_empty_eligibility later remaining 0)

/-- Any finite rank is at most the currently available-tool count plus one,
as used by eq:laminar-rank-extraction. -/
theorem errorRank_finite_le_card_add_one (stages : List (Finset Tool))
    (remaining : Finset Tool) (hfinite : errorRank stages remaining ≠ ⊤) :
    errorRank stages remaining ≤ ((remaining.card + 1 : Nat) : ℕ∞) := by
  classical
  by_cases hfail : ∃ budget, ¬ Safe stages remaining budget
  · have hcap : ¬ Safe stages remaining (remaining.card + 1) := by
      intro hsafe
      exact (Nat.find_spec hfail) (safe_of_card_add_one hsafe (Nat.find hfail))
    unfold errorRank
    rw [dite_eq_left hfail]
    exact ENat.natCast_le_natCast.mpr (Nat.find_min' hfail hcap)
  · exact False.elim (hfinite (by simp [errorRank, hfail]))

end PaperProofs.Structure
