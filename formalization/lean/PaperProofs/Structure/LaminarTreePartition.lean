module

public import PaperProofs.Structure.LaminarTree

/-!
Children of the inclusion tree are derived from the finite parent search.
Their partition properties are proved from the original laminar input, not
assumed as tree fields. The final lemmas connect these properties directly to
the existing capacity count and single-node normalization proofs.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

private theorem children_eq_of_subset {family : Finset (Finset Tool)}
    {parent left right : Finset Tool} (hrightMem : right ∈ family)
    (hleft : IsParent family left parent) (hright : IsParent family right parent)
    (hsub : left ⊆ right) : left = right := by
  by_contra hne
  have hstrict : left ⊂ right := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, hne⟩
  have hparentSub : parent ⊆ right := hleft.2.2 right hrightMem hstrict
  have heq : right = parent := Finset.Subset.antisymm hright.2.1.subset hparentSub
  exact (Finset.ssubset_iff_subset_ne.mp hright.2.1).2 heq

/-- Distinct children cannot overlap: laminar comparability would otherwise
place one strictly between the other and their common parent. -/
theorem children_pairwise_disjoint (family : Finset (Finset Tool))
    (hlaminar : LaminarFamily family) (hnonempty : ∀ node ∈ family, node.Nonempty)
    (parent : Finset Tool) :
    (children family parent : Set (Finset Tool)).PairwiseDisjoint id := by
  intro left hleft right hright hne
  have hl := (mem_children_iff hlaminar hnonempty left parent).mp hleft
  have hr := (mem_children_iff hlaminar hnonempty right parent).mp hright
  rcases hlaminar left hl.1 right hr.1 with hdisjoint | hsub | hsub
  · exact hdisjoint
  · exact False.elim (hne (children_eq_of_subset hr.1 hl.2 hr.2 hsub))
  · exact False.elim (hne (children_eq_of_subset hl.1 hr.2 hl.2 hsub).symm)

/-- For each tool in an internal support, maximize the cardinality of a
proper node containing that tool. The resulting node has the requested
support as its actual parent. This proves coverage without assuming it. -/
theorem exists_child_containing (family : Finset (Finset Tool))
    (hlaminar : LaminarFamily family) (hsingletons : ∀ tool : Tool, {tool} ∈ family)
    {parent : Finset Tool} (hparent : parent ∈ family) (hinternal : 1 < parent.card)
    {tool : Tool} (htool : tool ∈ parent) :
    ∃ child ∈ children family parent, tool ∈ child := by
  let candidates := family.filter (fun child => tool ∈ child ∧ child ⊂ parent)
  have hsingleton : ({tool} : Finset Tool) ⊂ parent := by
    refine Finset.ssubset_iff_subset_ne.mpr ⟨Finset.singleton_subset_iff.mpr htool, ?_⟩
    intro heq
    rw [← heq, Finset.card_singleton] at hinternal
    exact (Nat.lt_irrefl 1) hinternal
  have hcandidates : candidates.Nonempty :=
    ⟨{tool}, Finset.mem_filter.mpr ⟨hsingletons tool,
      Finset.mem_singleton_self tool, hsingleton⟩⟩
  obtain ⟨child, hchild, hmax⟩ := Finset.exists_max_image candidates Finset.card hcandidates
  obtain ⟨hchildMem, htoolChild, hchildSub⟩ := Finset.mem_filter.mp hchild
  have hparentOfChild : IsParent family child parent := by
    refine ⟨hparent, hchildSub, ?_⟩
    intro other hother hchildOther
    rcases hlaminar other hother parent hparent with hdisjoint | hotherSub | hparentSub
    · exact False.elim ((Finset.disjoint_left.mp hdisjoint)
        (hchildOther.subset htoolChild) htool)
    · by_cases heq : other = parent
      · exact heq.symm.subset
      · have hotherStrict : other ⊂ parent :=
          Finset.ssubset_iff_subset_ne.mpr ⟨hotherSub, heq⟩
        have hotherCandidate : other ∈ candidates :=
          Finset.mem_filter.mpr ⟨hother, hchildOther.subset htoolChild, hotherStrict⟩
        exact False.elim ((Nat.not_lt_of_ge (hmax other hotherCandidate))
          (Finset.card_lt_card hchildOther))
    · exact hparentSub
  refine ⟨child, Finset.mem_filter.mpr ⟨hchildMem, ?_⟩, htoolChild⟩
  exact (parent?_eq_some_iff hlaminar ⟨tool, htoolChild⟩).mpr hparentOfChild

/-- Every internal node is exactly the finite union of its actual children. -/
theorem children_cover (family : Finset (Finset Tool))
    (hlaminar : LaminarFamily family) (hnonempty : ∀ node ∈ family, node.Nonempty)
    (hsingletons : ∀ tool : Tool, {tool} ∈ family)
    {parent : Finset Tool} (hparent : parent ∈ family) (hinternal : 1 < parent.card) :
    (children family parent).biUnion id = parent := by
  ext tool
  constructor
  · intro h
    obtain ⟨child, hchild, htool⟩ := Finset.mem_biUnion.mp h
    have hp := (mem_children_iff hlaminar hnonempty child parent).mp hchild
    exact hp.2.2.1.subset htool
  · intro htool
    obtain ⟨child, hchild, htoolChild⟩ :=
      exists_child_containing family hlaminar hsingletons hparent hinternal htool
    exact Finset.mem_biUnion.mpr ⟨child, hchild, htoolChild⟩

/-- Added singleton nodes really are leaves of the derived parent relation. -/
theorem singleton_children_empty (family : Finset (Finset Tool))
    (hlaminar : LaminarFamily family) (hnonempty : ∀ node ∈ family, node.Nonempty)
    (tool : Tool) : children family {tool} = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro child hchild
  have hp := (mem_children_iff hlaminar hnonempty child {tool}).mp hchild
  have hempty : child = ∅ := Finset.ssubset_singleton_iff.mp hp.2.2.1
  exact (hnonempty child hp.1).ne_empty hempty

/-- Strict support growth on parent edges supplies the finite acyclicity
measure; a node cannot be its own ancestor along a nonempty edge cycle. -/
theorem child_card_lt_parent (family : Finset (Finset Tool))
    (hlaminar : LaminarFamily family) (hnonempty : ∀ node ∈ family, node.Nonempty)
    {child parent : Finset Tool} (hchild : child ∈ children family parent) :
    child.card < parent.card :=
  Finset.card_lt_card ((mem_children_iff hlaminar hnonempty child parent).mp hchild).2.2.1

section InputTree

variable [Fintype Tool] [Nonempty Tool]

omit [Nonempty Tool] in
theorem root_parent_none (stages : List (Finset Tool)) :
    parent? (nodeFamily stages) (Finset.univ : Finset Tool) = none := by
  unfold parent?
  apply List.argmin_eq_none.mpr
  apply Finset.toList_eq_nil.mpr
  apply Finset.eq_empty_of_forall_notMem
  intro candidate hcandidate
  have hstrict := (Finset.mem_filter.mp hcandidate).2
  have heq : (Finset.univ : Finset Tool) = candidate :=
    Finset.Subset.antisymm hstrict.subset (Finset.subset_univ candidate)
  exact (Finset.ssubset_iff_subset_ne.mp hstrict).2 heq

theorem node_children_disjoint (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (parent : Finset Tool) :
    (children (nodeFamily stages) parent : Set (Finset Tool)).PairwiseDisjoint
      (layout stages).support :=
  children_pairwise_disjoint (nodeFamily stages) (nodeFamily_laminar stages hlaminar)
    (nodeFamily_nonempty_nodes stages) parent

theorem node_children_cover (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) {parent : Finset Tool}
    (hparent : parent ∈ nodeFamily stages) (hinternal : 1 < parent.card) :
    (children (nodeFamily stages) parent).biUnion (layout stages).support =
      (layout stages).support parent :=
  children_cover (nodeFamily stages) (nodeFamily_laminar stages hlaminar)
    (nodeFamily_nonempty_nodes stages) (singleton_mem stages) hparent hinternal

/-- The partition count identity now applies to the tree constructed from
the actual input, with all partition premises discharged. -/
theorem layout_used_count_eq_sum_children (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) {parent : Finset Tool}
    (hparent : parent ∈ nodeFamily stages) (hinternal : 1 < parent.card)
    (used : Finset Tool) :
    (used ∩ (layout stages).support parent).card =
      ∑ child ∈ children (nodeFamily stages) parent,
        (used ∩ (layout stages).support child).card :=
  used_count_eq_sum_children (layout stages) parent (children (nodeFamily stages) parent)
    (node_children_disjoint stages hlaminar parent)
    (node_children_cover stages hlaminar hparent hinternal) used

/-- The elementary normalization theorem is connected to real input-tree
children, rather than assuming a cover in an external layout. -/
theorem layout_normalizeAt_preserves (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) {parent : Finset Tool}
    (hparent : parent ∈ nodeFamily stages) (hinternal : 1 < parent.card)
    (capacity : Finset Tool → ℕ) :
    capacityFamily (layout stages)
        (normalizeAt parent (children (nodeFamily stages) parent) capacity) =
      capacityFamily (layout stages) capacity :=
  capacityFamily_normalizeAt (layout stages) parent (children (nodeFamily stages) parent)
    capacity (children_subset _ _) (node_children_cover stages hlaminar hparent hinternal)

end InputTree

end PaperProofs.Structure.LaminarTree
