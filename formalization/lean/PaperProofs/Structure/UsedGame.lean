module

public import PaperProofs.Structure.Game
public import PaperProofs.Structure.Capacity
public import PaperProofs.Common.Model

/-!
The used/remaining bridge, eq:laminar-safe-family--eq:laminar-rank-membership.
This is the same game and the same extension operator, not another DP model.
Stages are zero-indexed in Lean; dropping all stages is the paper's N+1 state.
-/

@[expose] public section

namespace PaperProofs.Structure

variable {Tool : Type*} [Fintype Tool] [DecidableEq Tool]

def safeUsedFamily (stages : List (Finset Tool)) (budget : ℕ) : Set (Finset Tool) :=
  {used | Safe stages (Finset.univ \ used) budget}

theorem remaining_after_used_insert (used : Finset Tool) (tool : Tool) :
    (Finset.univ \ insert tool used) = (Finset.univ \ used).erase tool := by
  ext r
  simp [Finset.mem_sdiff, Finset.mem_erase, not_or]

/-- The paper's set-family recurrence follows from operational causal safety. -/
theorem safeUsed_budget_recurrence (eligible : Finset Tool)
    (later : List (Finset Tool)) (budget : ℕ) :
    safeUsedFamily (eligible :: later) (budget + 1) =
      safeUsedFamily later (budget + 1) ∩ usedExtension eligible (safeUsedFamily later budget) := by
  ext used
  simp only [safeUsedFamily, usedExtension, Set.mem_inter_iff, Set.mem_ofPred_eq]
  rw [safe_cons_succ_iff]
  constructor
  · rintro ⟨hgood, tool, htool, hbad⟩
    refine ⟨hgood, tool, (Finset.mem_inter.mp htool).1, ?_, ?_⟩
    · simpa using (Finset.mem_inter.mp htool).2
    · simpa [remaining_after_used_insert] using hbad
  · rintro ⟨hgood, tool, heligible, hunused, hbad⟩
    refine ⟨hgood, tool, Finset.mem_inter.mpr ⟨heligible, ?_⟩, ?_⟩
    · simpa using hunused
    · simpa [remaining_after_used_insert] using hbad

theorem safeUsed_rank_membership (stages : List (Finset Tool))
    (used : Finset Tool) (budget : ℕ) :
    used ∈ safeUsedFamily stages budget ↔
      (budget : ℕ∞) < errorRank stages (Finset.univ \ used) :=
  safe_iff_lt_errorRank stages (Finset.univ \ used) budget

theorem safeUsed_zero (stages : List (Finset Tool)) :
    safeUsedFamily stages 0 = Set.univ := by
  ext used
  simp [safeUsedFamily, safe_zero]

theorem safeUsed_terminal (budget : ℕ) :
    safeUsedFamily ([] : List (Finset Tool)) budget = Set.univ := by
  ext used
  simp [safeUsedFamily, safe_terminal]

def suffixSafety (I : Common.Instance) (nextStage budget : ℕ) : Set (Finset I.Tool) :=
  safeUsedFamily (I.compatibility.drop nextStage) budget

noncomputable def initialRank (I : Common.Instance) : ℕ∞ :=
  errorRank I.compatibility I.tools

end PaperProofs.Structure
