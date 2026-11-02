module

public import PaperProofs.Structure.Rank
public import Mathlib.Data.List.MinMax
public import Init.Data.List.FinRange

/-!
Executable rank evaluation for an arbitrary finite compatibility schedule.
The independent causal game rank is not redefined: the executable recurrence
is proved equal to it by suffix induction. No laminarity or complexity
assumption is required or asserted. Recursive evaluation may be exponential.
-/

@[expose] public section

namespace PaperProofs.Structure

variable {Tool : Type*} [DecidableEq Tool]

def genericRank : List (Finset Tool) → Finset Tool → ℕ∞
  | [], _ => ⊤
  | eligible :: later, remaining =>
      min (genericRank later remaining)
        (1 + (eligible ∩ remaining).sup (fun tool => genericRank later (remaining.erase tool)))

theorem genericRank_eq_errorRank (stages : List (Finset Tool)) (remaining : Finset Tool) :
    genericRank stages remaining = errorRank stages remaining := by
  induction stages generalizing remaining with
  | nil => exact (errorRank_terminal remaining).symm
  | cons eligible later ih =>
    simpa only [genericRank, ih, badChildRank] using (errorRank_cons eligible later remaining).symm

theorem safe_iff_lt_genericRank (stages : List (Finset Tool)) (remaining : Finset Tool) (budget : Nat) :
    Safe stages remaining budget ↔ (budget : ℕ∞) < genericRank stages remaining := by
  rw [genericRank_eq_errorRank]
  exact safe_iff_lt_errorRank stages remaining budget

theorem genericRank_pos (stages : List (Finset Tool)) (remaining : Finset Tool) :
    0 < genericRank stages remaining := by
  rw [genericRank_eq_errorRank]
  exact errorRank_pos stages remaining

/-- The actual finite candidates; no semantic safety decision is executed. -/
def genericRankCandidates (q : Nat) (eligible remaining : Finset (Fin q)) : List (Fin q) :=
  (List.finRange q).filter (fun tool => decide (tool ∈ eligible ∩ remaining))

theorem mem_genericRankCandidates (q : Nat) (eligible remaining : Finset (Fin q)) (tool : Fin q) :
    tool ∈ genericRankCandidates q eligible remaining ↔ tool ∈ eligible ∩ remaining := by
  simp only [genericRankCandidates, List.mem_filter, List.mem_finRange, decide_eq_true_eq, true_and]

theorem genericRankCandidates_eq_nil (q : Nat) (eligible remaining : Finset (Fin q)) :
    genericRankCandidates q eligible remaining = [] ↔ eligible ∩ remaining = ∅ := by
  constructor
  · intro hnil
    apply Finset.eq_empty_of_forall_notMem
    intro tool htool
    have hmem := (mem_genericRankCandidates q eligible remaining tool).mpr htool
    rw [hnil] at hmem
    exact List.not_mem_nil hmem
  · intro hempty
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro tool htool
    have hmem := (mem_genericRankCandidates q eligible remaining tool).mp htool
    rw [hempty] at hmem
    exact Finset.notMem_empty _ hmem

/-- Max-rank selection compares the computed recursive child values only. -/
def pickGenericMaxRankTool (q : Nat) (eligible : Finset (Fin q))
    (later : List (Finset (Fin q))) (remaining : Finset (Fin q)) : Option (Fin q) :=
  List.argmax (fun tool => genericRank later (remaining.erase tool))
    (genericRankCandidates q eligible remaining)

theorem pickGenericMaxRankTool_eq_none (q : Nat) (eligible : Finset (Fin q))
    (later : List (Finset (Fin q))) (remaining : Finset (Fin q)) :
    pickGenericMaxRankTool q eligible later remaining = none ↔ eligible ∩ remaining = ∅ := by
  rw [pickGenericMaxRankTool, List.argmax_eq_none, genericRankCandidates_eq_nil]

theorem pickGenericMaxRankTool_spec (q : Nat) (eligible : Finset (Fin q))
    (later : List (Finset (Fin q))) (remaining : Finset (Fin q)) (tool : Fin q)
    (hpick : pickGenericMaxRankTool q eligible later remaining = some tool) :
    tool ∈ eligible ∩ remaining ∧
      errorRank later (remaining.erase tool) = badChildRank eligible later remaining := by
  change List.argmax (fun candidate => genericRank later (remaining.erase candidate))
    (genericRankCandidates q eligible remaining) = some tool at hpick
  have htool := (mem_genericRankCandidates q eligible remaining tool).mp (List.argmax_mem hpick)
  refine ⟨htool, le_antisymm (childRank_le_badChildRank eligible later remaining htool) ?_⟩
  apply Finset.sup_le
  intro candidate hcandidate
  have hle := List.le_of_mem_argmax ((mem_genericRankCandidates q eligible remaining candidate).mpr hcandidate) hpick
  simpa only [genericRank_eq_errorRank] using hle

theorem pickGenericMaxRankTool_exists (q : Nat) (eligible : Finset (Fin q))
    (later : List (Finset (Fin q))) (remaining : Finset (Fin q))
    (hnonempty : (eligible ∩ remaining).Nonempty) :
    ∃ tool, pickGenericMaxRankTool q eligible later remaining = some tool ∧
      tool ∈ eligible ∩ remaining ∧
        errorRank later (remaining.erase tool) = badChildRank eligible later remaining := by
  cases hpick : pickGenericMaxRankTool q eligible later remaining with
  | none => exact False.elim (hnonempty.ne_empty ((pickGenericMaxRankTool_eq_none q eligible later remaining).mp hpick))
  | some tool => exact ⟨tool, rfl, pickGenericMaxRankTool_spec q eligible later remaining tool hpick⟩

theorem pickGenericMaxRankTool_safe (q : Nat) (eligible : Finset (Fin q))
    (later : List (Finset (Fin q))) (remaining : Finset (Fin q)) (budget : Nat) (tool : Fin q)
    (hpick : pickGenericMaxRankTool q eligible later remaining = some tool)
    (hsafe : Safe (eligible :: later) remaining (budget + 1)) :
    Safe later (remaining.erase tool) budget := by
  obtain ⟨_, witness, hwitness, hchild⟩ := (safe_cons_succ_iff _ _ _ _).mp hsafe
  have hbad := (lt_badChildRank_iff eligible later remaining budget).mpr ⟨witness, hwitness, hchild⟩
  apply (safe_iff_lt_errorRank _ _ _).mpr
  rw [(pickGenericMaxRankTool_spec q eligible later remaining tool hpick).2]
  exact hbad

theorem pickGenericMaxRankTool_zero_tools (eligible : Finset (Fin 0))
    (later : List (Finset (Fin 0))) (remaining : Finset (Fin 0)) :
    pickGenericMaxRankTool 0 eligible later remaining = none := rfl

end PaperProofs.Structure
