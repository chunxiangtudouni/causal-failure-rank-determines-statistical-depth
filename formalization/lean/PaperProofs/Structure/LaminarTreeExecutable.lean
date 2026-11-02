module

public import PaperProofs.Structure.LaminarTreePartition
public import Mathlib.Data.List.OfFn
public import Mathlib.Data.List.Dedup

/-!
Executable finite-list realization of the inclusion-tree construction.
`Finset.toList` uses choice, so the earlier family-based `parent?` is only a
mathematical specification. Here an explicit `Fin q` input supplies an actual
node list, and parent search uses computable filtering and Mathlib argmin.
The agreement theorem links it to the same node family and capacity layout.
No runtime bound is asserted by this module.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

/-- The executable parent search scans only the supplied finite node list. -/
def parentFromList (nodes : List (Finset Tool)) (child : Finset Tool) :
    Option (Finset Tool) :=
  List.argmin Finset.card (nodes.filter (fun parent => decide (child ⊂ parent)))

theorem parentFromList_isParent (nodes : List (Finset Tool))
    {family : Finset (Finset Tool)} (hnodes : nodes.toFinset = family)
    (hlaminar : LaminarFamily family) {child parent : Finset Tool}
    (hchild : child.Nonempty) (hpick : parentFromList nodes child = some parent) :
    IsParent family child parent := by
  have hmem (node : Finset Tool) : node ∈ nodes ↔ node ∈ family := by
    rw [← hnodes]
    exact List.mem_toFinset.symm
  change List.argmin Finset.card (nodes.filter (fun candidate => decide (child ⊂ candidate))) =
    some parent at hpick
  have hparentList := List.argmin_mem hpick
  have hparentFields := List.mem_filter.mp hparentList
  have hparentStrict : child ⊂ parent := by simpa using hparentFields.2
  apply isParent_of_card_min hlaminar hchild
  · exact Finset.mem_filter.mpr ⟨(hmem parent).mp hparentFields.1, hparentStrict⟩
  · intro other hother
    obtain ⟨hotherMem, hotherStrict⟩ := Finset.mem_filter.mp hother
    apply List.le_of_mem_argmin (m := parent) (f := Finset.card) _ hpick
    exact List.mem_filter.mpr ⟨(hmem other).mpr hotherMem, by simp [hotherStrict]⟩

theorem parentFromList_exists (nodes : List (Finset Tool))
    {family : Finset (Finset Tool)} (hnodes : nodes.toFinset = family)
    (hlaminar : LaminarFamily family) {child : Finset Tool} (hchild : child.Nonempty)
    (hcandidate : ∃ other ∈ nodes, child ⊂ other) :
    ∃ parent, parentFromList nodes child = some parent ∧ IsParent family child parent := by
  cases hpick : parentFromList nodes child with
  | none =>
    have hempty : nodes.filter (fun candidate => decide (child ⊂ candidate)) = [] :=
      List.argmin_eq_none.mp hpick
    obtain ⟨other, hother, hstrict⟩ := hcandidate
    have hin : other ∈ nodes.filter (fun candidate => decide (child ⊂ candidate)) :=
      List.mem_filter.mpr ⟨hother, by simp [hstrict]⟩
    rw [hempty] at hin
    exact False.elim (List.not_mem_nil hin)
  | some parent =>
    exact ⟨parent, rfl, parentFromList_isParent nodes hnodes hlaminar hchild hpick⟩

/-- Construct the actual finite node table for the manuscript's `q` tools. -/
def explicitNodeList (q : Nat) (stages : List (Finset (Fin q))) : List (Finset (Fin q)) :=
  ((Finset.univ : Finset (Fin q)) ::
    (stages.filter (fun stage => decide stage.Nonempty) ++
      List.ofFn (fun tool : Fin q => ({tool} : Finset (Fin q))))).dedup

theorem explicitNodeList_nodup (q : Nat) (stages : List (Finset (Fin q))) :
    (explicitNodeList q stages).Nodup := List.nodup_dedup _

theorem explicitNodeList_toFinset (q : Nat) (stages : List (Finset (Fin q))) :
    (explicitNodeList q stages).toFinset = nodeFamily stages := by
  ext node
  simp [explicitNodeList, mem_nodeFamily, eq_comm]

/-- The concrete duplicate-free node list has the same `N+q+1` bound. -/
theorem explicitNodeList_length_le (q : Nat) (stages : List (Finset (Fin q))) :
    (explicitNodeList q stages).length ≤ stages.length + q + 1 := by
  have hcard := List.toFinset_card_of_nodup (explicitNodeList_nodup q stages)
  rw [explicitNodeList_toFinset] at hcard
  rw [← hcard]
  simpa only [Fintype.card_fin] using nodeFamily_card_le stages

def explicitParent (q : Nat) (stages : List (Finset (Fin q))) (child : Finset (Fin q)) :
    Option (Finset (Fin q)) := parentFromList (explicitNodeList q stages) child

theorem explicitParent_spec (q : Nat) (stages : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule stages) {child : Finset (Fin q)}
    (hchild : child ∈ nodeFamily stages) (hroot : child ≠ Finset.univ) :
    ∃ parent, explicitParent q stages child = some parent ∧
      IsParent (nodeFamily stages) child parent := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hnonempty := nodeFamily_nonempty_nodes stages child hchild
  have hrootList : (Finset.univ : Finset (Fin q)) ∈ explicitNodeList q stages := by
    apply List.mem_toFinset.mp
    rw [explicitNodeList_toFinset]
    exact root_mem stages
  have hstrict : child ⊂ Finset.univ :=
    Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ child, hroot⟩
  exact parentFromList_exists (explicitNodeList q stages) (explicitNodeList_toFinset q stages)
    (nodeFamily_laminar stages hlaminar) hnonempty ⟨Finset.univ, hrootList, hstrict⟩

section Root

variable [Fintype Tool]

theorem parentFromList_root_none (nodes : List (Finset Tool)) :
    parentFromList nodes (Finset.univ : Finset Tool) = none := by
  cases hpick : parentFromList nodes (Finset.univ : Finset Tool) with
  | none => rfl
  | some candidate =>
    have hmem := List.argmin_mem hpick
    have hfields := List.mem_filter.mp hmem
    have hstrict : (Finset.univ : Finset Tool) ⊂ candidate := by simpa using hfields.2
    have heq : (Finset.univ : Finset Tool) = candidate :=
      Finset.Subset.antisymm hstrict.subset (Finset.subset_univ candidate)
    exact False.elim ((Finset.ssubset_iff_subset_ne.mp hstrict).2 heq)

end Root

/-- On every actual node the executable search agrees with the same parent
used by the proven child partition and the shared capacity layout. -/
theorem explicitParent_agrees (q : Nat) (stages : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule stages) {child : Finset (Fin q)}
    (hchild : child ∈ nodeFamily stages) :
    explicitParent q stages child = parent? (nodeFamily stages) child := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  by_cases hroot : child = Finset.univ
  · subst child
    exact (parentFromList_root_none (explicitNodeList q stages)).trans
      (root_parent_none stages).symm
  · obtain ⟨parent, hpick, hparent⟩ := explicitParent_spec q stages hq hlaminar hchild hroot
    have hcanonical := (parent?_eq_some_iff (nodeFamily_laminar stages hlaminar)
      (nodeFamily_nonempty_nodes stages child hchild)).mpr hparent
    exact hpick.trans hcanonical.symm

end PaperProofs.Structure.LaminarTree
