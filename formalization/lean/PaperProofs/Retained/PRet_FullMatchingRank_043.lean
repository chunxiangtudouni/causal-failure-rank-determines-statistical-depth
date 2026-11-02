module

public import PaperProofs.Retained.Controller
public import PaperProofs.Structure.Rank

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

namespace PaperProofs.Retained.PRetFullMatchingRank043

open Common

variable {I : Instance}

/-- One full distinct assignment supplies an actual causal safety plan.
This is ONLY an infinite-rank witness, never an identification of retained
finite rank or the retained full-policy penalty with available-tool G. -/
theorem ordered_rank_top_of_assignment {Tool : Type*} [DecidableEq Tool]
    (stages : List (Finset Tool)) (remaining : Finset Tool)
    (assignment : Fin stages.length → Tool) (hinj : Function.Injective assignment)
    (hlegal : ∀ stage, assignment stage ∈ stages.get stage ∩ remaining) :
    PaperProofs.Structure.errorRank stages remaining = ⊤ := by
  induction stages generalizing remaining with
  | nil => exact PaperProofs.Structure.errorRank_terminal remaining
  | cons eligible later ih =>
    let tail : Fin later.length → Tool := fun i => assignment i.succ
    have htailInj : Function.Injective tail := by
      intro i j hij
      apply Fin.ext
      have he := congrArg Fin.val (hinj hij)
      change i.val + 1 = j.val + 1 at he
      omega
    have htailLegal : ∀ i, tail i ∈ later.get i ∩ remaining := by
      intro i
      exact hlegal i.succ
    have hgood := ih remaining tail htailInj htailLegal
    have htailErase : ∀ i, tail i ∈ later.get i ∩ remaining.erase (assignment 0) := by
      intro i
      refine Finset.mem_inter.mpr ⟨(Finset.mem_inter.mp (htailLegal i)).1, Finset.mem_erase.mpr ⟨?_, ?_⟩⟩
      · intro heq
        exact (Fin.succ_ne_zero i) (hinj heq)
      · exact (Finset.mem_inter.mp (htailLegal i)).2
    have hbad := ih (remaining.erase (assignment 0)) tail htailInj htailErase
    have hhead : assignment 0 ∈ eligible ∩ remaining := hlegal 0
    have hbadTop : PaperProofs.Structure.badChildRank eligible later remaining = ⊤ := by
      apply top_le_iff.mp
      rw [← hbad]
      exact PaperProofs.Structure.childRank_le_badChildRank eligible later remaining hhead
    exact (PaperProofs.Structure.errorRank_cons_eq_top_iff eligible later remaining).mpr ⟨hgood, hbadTop⟩

theorem ordered_rank_top_of_full_matching (J : Instance) (hmatch : Matchable J Finset.univ) :
    PaperProofs.Structure.errorRank J.compatibility J.tools = ⊤ := by
  obtain ⟨assignment, hinj, hcompatible⟩ := hmatch
  let full : J.Stage → J.Tool := fun i => assignment ⟨i, Finset.mem_univ i⟩
  apply ordered_rank_top_of_assignment J.compatibility J.tools full
  · intro i j hij
    exact congrArg Subtype.val (hinj hij)
  · intro i
    exact Finset.mem_inter.mpr ⟨hcompatible ⟨i, Finset.mem_univ i⟩, Finset.mem_univ _⟩

/-- Retained infinity really means JOINT matchability with old H for ALL
future declarations. The finite full-future set is included, not just a
particular observed successful error set. -/
theorem top_joint_future_matchable (I : Instance) (next : ℕ) (old : Finset I.Stage)
    (htop : errorRank I (stagesFrom I next) old = ⊤) :
    Matchable I (old ∪ (stagesFrom I next).toFinset) := by
  have hs := (rank_eq_top_iff I (stagesFrom I next) old).mp htop ((stagesFrom I next).toFinset.card)
  exact (safe_iff_future_sets I (stagesFrom I next) old _).mp hs
    (stagesFrom I next).toFinset (Finset.Subset.refl _) le_rfl

theorem freshStage_in_future (I : Instance) (next : ℕ) (stage : (I.freshSuffix next).Stage) :
    I.freshStageLift next stage ∈ (stagesFrom I next).toFinset := by
  apply List.mem_toFinset.mpr
  apply (mem_stagesFrom I next _).mpr
  change next ≤ next + stage.val
  omega

theorem fresh_full_matching_of_joint (I : Instance) (next : ℕ) (old : Finset I.Stage)
    (hjoint : Matchable I (old ∪ (stagesFrom I next).toFinset)) :
    Matchable (I.freshSuffix next) Finset.univ := by
  obtain ⟨assignment, hinj, hcompatible⟩ := hjoint
  have hlift (stage : (I.freshSuffix next).Stage) :
      I.freshStageLift next stage ∈ old ∪ (stagesFrom I next).toFinset :=
    Finset.mem_union_right old (freshStage_in_future I next stage)
  refine ⟨fun stage => assignment ⟨I.freshStageLift next stage.val, hlift stage.val⟩, ?_, ?_⟩
  · intro first later heq
    apply Subtype.ext
    apply Fin.ext
    have he := congrArg (fun stage => stage.val.val) (hinj heq)
    change next + first.val.val = next + later.val.val at he
    omega
  · intro stage
    rw [I.freshSuffix_eligible]
    exact hcompatible ⟨I.freshStageLift next stage.val, hlift stage.val⟩

theorem fresh_ordered_rank_top_of_retained_top (I : Instance) (next : ℕ) (old : Finset I.Stage)
    (htop : errorRank I (stagesFrom I next) old = ⊤) :
    PaperProofs.Structure.errorRank (I.freshSuffix next).compatibility (I.freshSuffix next).tools = ⊤ :=
  ordered_rank_top_of_full_matching (I.freshSuffix next)
    (fresh_full_matching_of_joint I next old (top_joint_future_matchable I next old htop))

theorem liftedErrors_subset_future (I : Instance) (next : ℕ) (ledger : Ledger (I.freshSuffix next)) :
    liftedErrors I next ledger ⊆ (stagesFrom I next).toFinset := by
  intro stage hstage
  obtain ⟨localStage, _, rfl⟩ := Finset.mem_image.mp hstage
  exact freshStage_in_future I next localStage

end PaperProofs.Retained.PRetFullMatchingRank043
