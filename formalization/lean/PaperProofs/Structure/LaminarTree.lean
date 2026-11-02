module

public import PaperProofs.Structure.Capacity
public import Mathlib.Data.Fintype.Card
public import Mathlib.Data.List.MinMax
public import Mathlib.Data.Finset.Max

/-!
The finite inclusion tree constructed from the explicit compatibility input,
laminar.tex:12--20 and laminar-proofs.tex:235--243. Nodes are actual distinct
finite supports, not an assumed tree carrying its own correctness fields.
The parent search scans the finite proper-superset candidates with Mathlib's
cardinality argmin. Runtime and bit-complexity certification is separate.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*}

/-- Equal or empty sets cause no extra assumption: they satisfy this formula
automatically. Thus it states precisely the paper's laminar compatibility. -/
def LaminarSchedule (stages : List (Finset Tool)) : Prop :=
  ∀ left ∈ stages, ∀ right ∈ stages,
    Disjoint left right ∨ left ⊆ right ∨ right ⊆ left

def LaminarFamily (family : Finset (Finset Tool)) : Prop :=
  ∀ left ∈ family, ∀ right ∈ family,
    Disjoint left right ∨ left ⊆ right ∨ right ⊆ left

/-- A parent is the least proper superset among the actual finite nodes.
Existence and uniqueness are proved below, not fields of the input. -/
def IsParent (family : Finset (Finset Tool)) (child parent : Finset Tool) : Prop :=
  parent ∈ family ∧ child ⊂ parent ∧
    ∀ other ∈ family, child ⊂ other → parent ⊆ other

theorem isParent_unique {family : Finset (Finset Tool)} {child left right : Finset Tool}
    (hleft : IsParent family child left) (hright : IsParent family child right) : left = right :=
  Finset.Subset.antisymm (hleft.2.2 right hright.1 hright.2.1)
    (hright.2.2 left hleft.1 hleft.2.1)

variable [DecidableEq Tool]

def properSupersets (family : Finset (Finset Tool)) (child : Finset Tool) :
    Finset (Finset Tool) := family.filter (fun parent => child ⊂ parent)

/-- Search only the explicitly supplied nodes, never all tool subsets. -/
noncomputable def parent? (family : Finset (Finset Tool)) (child : Finset Tool) :
    Option (Finset Tool) := List.argmin Finset.card (properSupersets family child).toList

theorem isParent_of_card_min {family : Finset (Finset Tool)}
    (hlaminar : LaminarFamily family) {child parent : Finset Tool}
    (hchild : child.Nonempty) (hparent : parent ∈ properSupersets family child)
    (hmin : ∀ other ∈ properSupersets family child, parent.card ≤ other.card) :
    IsParent family child parent := by
  obtain ⟨hparentMem, hchildSub⟩ := Finset.mem_filter.mp hparent
  refine ⟨hparentMem, hchildSub, ?_⟩
  intro other hother hchildOther
  rcases hlaminar parent hparentMem other hother with hdisjoint | hsub | hsub
  · obtain ⟨tool, htool⟩ := hchild
    exact False.elim ((Finset.disjoint_left.mp hdisjoint)
      (hchildSub.subset htool) (hchildOther.subset htool))
  · exact hsub
  · have hcard : parent.card ≤ other.card := hmin other
      (Finset.mem_filter.mpr ⟨hother, hchildOther⟩)
    have heq : other = parent := Finset.eq_of_subset_of_card_le hsub hcard
    exact heq.symm.subset

theorem parent?_isParent {family : Finset (Finset Tool)}
    (hlaminar : LaminarFamily family) {child parent : Finset Tool}
    (hchild : child.Nonempty) (hpick : parent? family child = some parent) :
    IsParent family child parent := by
  apply isParent_of_card_min hlaminar hchild
  · exact Finset.mem_toList.mp (List.argmin_mem hpick)
  · intro other hother
    exact List.le_of_mem_argmin (Finset.mem_toList.mpr hother) hpick

theorem parent?_exists_of_candidate {family : Finset (Finset Tool)}
    (hlaminar : LaminarFamily family) {child : Finset Tool} (hchild : child.Nonempty)
    (hcandidate : (properSupersets family child).Nonempty) :
    ∃ parent, parent? family child = some parent ∧ IsParent family child parent := by
  cases hpick : parent? family child with
  | none =>
    have hempty : (properSupersets family child).toList = [] :=
      List.argmin_eq_none.mp hpick
    have hemptyFin : properSupersets family child = ∅ :=
      Finset.toList_eq_nil.mp hempty
    exact False.elim (hcandidate.ne_empty hemptyFin)
  | some parent => exact ⟨parent, rfl, parent?_isParent hlaminar hchild hpick⟩

theorem parent?_eq_some_iff {family : Finset (Finset Tool)}
    (hlaminar : LaminarFamily family) {child parent : Finset Tool}
    (hchild : child.Nonempty) : parent? family child = some parent ↔ IsParent family child parent := by
  constructor
  · exact parent?_isParent hlaminar hchild
  · intro hparent
    have hnonempty : (properSupersets family child).Nonempty :=
      ⟨parent, Finset.mem_filter.mpr ⟨hparent.1, hparent.2.1⟩⟩
    obtain ⟨selected, hpick, hselected⟩ := parent?_exists_of_candidate hlaminar hchild hnonempty
    rw [isParent_unique hselected hparent] at hpick
    exact hpick

/-- Derived children of the actual parent search, rather than asserted tree data. -/
noncomputable def children (family : Finset (Finset Tool)) (parent : Finset Tool) :
    Finset (Finset Tool) := family.filter (fun child => parent? family child = some parent)

theorem children_subset (family : Finset (Finset Tool)) (parent : Finset Tool) :
    children family parent ⊆ family := Finset.filter_subset _ _

theorem mem_children_iff {family : Finset (Finset Tool)}
    (hlaminar : LaminarFamily family) (hnonempty : ∀ node ∈ family, node.Nonempty)
    (child parent : Finset Tool) :
    child ∈ children family parent ↔ child ∈ family ∧ IsParent family child parent := by
  constructor
  · intro h
    obtain ⟨hchild, hpick⟩ := Finset.mem_filter.mp h
    exact ⟨hchild, parent?_isParent hlaminar (hnonempty child hchild) hpick⟩
  · rintro ⟨hchild, hparent⟩
    exact Finset.mem_filter.mpr ⟨hchild,
      (parent?_eq_some_iff hlaminar (hnonempty child hchild)).mpr hparent⟩

section ExplicitFamily

variable [Fintype Tool]

/-- Remove duplicate and empty stage supports, then adjoin root and leaves. -/
def nodeFamily (stages : List (Finset Tool)) : Finset (Finset Tool) :=
  insert Finset.univ
    ((stages.toFinset.filter Finset.Nonempty) ∪
      (Finset.univ.image (fun tool : Tool => ({tool} : Finset Tool))))

theorem mem_nodeFamily (stages : List (Finset Tool)) (node : Finset Tool) :
    node ∈ nodeFamily stages ↔ node = Finset.univ ∨
      (node ∈ stages ∧ node.Nonempty) ∨ ∃ tool : Tool, node = {tool} := by
  simp [nodeFamily, eq_comm]

theorem root_mem (stages : List (Finset Tool)) :
    (Finset.univ : Finset Tool) ∈ nodeFamily stages :=
  (mem_nodeFamily stages _).mpr (Or.inl rfl)

theorem singleton_mem (stages : List (Finset Tool)) (tool : Tool) :
    ({tool} : Finset Tool) ∈ nodeFamily stages :=
  (mem_nodeFamily stages _).mpr (Or.inr (Or.inr ⟨tool, rfl⟩))

theorem nonempty_stage_mem (stages : List (Finset Tool)) {node : Finset Tool}
    (hstage : node ∈ stages) (hnonempty : node.Nonempty) : node ∈ nodeFamily stages :=
  (mem_nodeFamily stages _).mpr (Or.inr (Or.inl ⟨hstage, hnonempty⟩))

omit [Fintype Tool] in
private theorem compatible_singleton_left (tool : Tool) (node : Finset Tool) :
    Disjoint ({tool} : Finset Tool) node ∨ {tool} ⊆ node ∨ node ⊆ {tool} := by
  by_cases h : tool ∈ node
  · exact Or.inr (Or.inl (Finset.singleton_subset_iff.mpr h))
  · exact Or.inl (Finset.disjoint_singleton_left.mpr h)

omit [Fintype Tool] in
private theorem compatible_singleton_right (node : Finset Tool) (tool : Tool) :
    Disjoint node ({tool} : Finset Tool) ∨ node ⊆ {tool} ∨ {tool} ⊆ node := by
  by_cases h : tool ∈ node
  · exact Or.inr (Or.inr (Finset.singleton_subset_iff.mpr h))
  · exact Or.inl (Finset.disjoint_singleton_right.mpr h)

/-- Adjoining root and singleton leaves preserves the original laminarity. -/
theorem nodeFamily_laminar (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) : LaminarFamily (nodeFamily stages) := by
  intro left hleft right hright
  rcases (mem_nodeFamily stages left).mp hleft with hroot | hstage | ⟨tool, rfl⟩
  · subst left
    exact Or.inr (Or.inr (Finset.subset_univ right))
  · rcases (mem_nodeFamily stages right).mp hright with hroot | hrightStage | ⟨tool, rfl⟩
    · subst right
      exact Or.inr (Or.inl (Finset.subset_univ left))
    · exact hlaminar left hstage.1 right hrightStage.1
    · exact compatible_singleton_right left tool
  · exact compatible_singleton_left tool right

theorem nodeFamily_nonempty_nodes [Nonempty Tool] (stages : List (Finset Tool)) :
    ∀ node ∈ nodeFamily stages, node.Nonempty := by
  intro node hnode
  rcases (mem_nodeFamily stages node).mp hnode with hroot | hstage | ⟨tool, rfl⟩
  · subst node
    obtain ⟨tool⟩ := ‹Nonempty Tool›
    exact ⟨tool, Finset.mem_univ tool⟩
  · exact hstage.2
  · exact Finset.singleton_nonempty tool

/-- The distinct-node bound, including root and singleton additions. -/
theorem nodeFamily_card_le (stages : List (Finset Tool)) :
    (nodeFamily stages).card ≤ stages.length + Fintype.card Tool + 1 := by
  have hstage : (stages.toFinset.filter Finset.Nonempty).card ≤ stages.length :=
    (Finset.card_filter_le _ _).trans stages.toFinset_card_le
  have hsingle : (Finset.univ.image (fun tool : Tool => ({tool} : Finset Tool))).card ≤
      Fintype.card Tool := by
    simpa only [Finset.card_univ] using
      (Finset.card_image_le (s := (Finset.univ : Finset Tool))
        (f := fun tool : Tool => ({tool} : Finset Tool)))
  exact (Finset.card_insert_le _ _).trans
    ((Nat.add_le_add_right (Finset.card_union_le _ _) 1).trans
      (Nat.add_le_add_right (Nat.add_le_add hstage hsingle) 1))

/-- Every non-root actual node has a uniquely determined parent returned by
the finite candidate search. -/
theorem node_parent_exists_unique [Nonempty Tool] (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) {child : Finset Tool}
    (hchild : child ∈ nodeFamily stages) (hroot : child ≠ Finset.univ) :
    ∃! parent, IsParent (nodeFamily stages) child parent := by
  have hnonempty := nodeFamily_nonempty_nodes stages child hchild
  have hcandidate : (properSupersets (nodeFamily stages) child).Nonempty := by
    refine ⟨Finset.univ, Finset.mem_filter.mpr ⟨root_mem stages, ?_⟩⟩
    exact Finset.ssubset_iff_subset_ne.mpr ⟨Finset.subset_univ child, hroot⟩
  obtain ⟨parent, _, hparent⟩ :=
    parent?_exists_of_candidate (nodeFamily_laminar stages hlaminar) hnonempty hcandidate
  exact ⟨parent, hparent, fun other hother => isParent_unique hother hparent⟩

/-- Reuse the existing active-node capacity layout with each actual support
as its own node. Values outside the finite active family remain irrelevant. -/
def layout (stages : List (Finset Tool)) : CapacityLayout Tool (Finset Tool) where
  nodes := nodeFamily stages
  support := id

theorem layout_hasSingletonNodes (stages : List (Finset Tool)) :
    (layout stages).HasSingletonNodes := by
  intro tool
  exact ⟨{tool}, singleton_mem stages tool, rfl⟩

end ExplicitFamily

end PaperProofs.Structure.LaminarTree
