module

public import Mathlib.Data.Finset.Card
public import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
Used-tool capacity families for eq:laminar-capacity-family in the frozen
manuscript, laminar-proofs.tex:8--18 and 71--111.

The active nodes and all supports are explicitly finite. The elementary
results here need no laminarity assumption. In the paper `Tool` is the finite
type of the input's tools, and `support node` is that tree node's leaf set.
Single-node normalization preserves the family by the finite-cover argument
proved below. Whole-tree normalized output and the nonempty-support
path-decrement theorem are not assumed or asserted by this module.
-/

@[expose] public section

namespace PaperProofs.Structure

variable {Tool Node : Type*} [DecidableEq Tool]

/-- Explicit finite node data; capacities outside `nodes` impose no constraint. -/
structure CapacityLayout (Tool Node : Type*) where
  nodes : Finset Node
  support : Node → Finset Tool

/-- Every tool is represented by an active singleton node in the paper's tree. -/
def CapacityLayout.HasSingletonNodes (layout : CapacityLayout Tool Node) : Prop :=
  ∀ tool : Tool, ∃ node ∈ layout.nodes, layout.support node = {tool}

/-- The family of used-tool sets satisfying all active capacity constraints. -/
def capacityFamily (layout : CapacityLayout Tool Node) (capacity : Node → ℕ) :
    Set (Finset Tool) :=
  {used | ∀ node ∈ layout.nodes, (used ∩ layout.support node).card ≤ capacity node}

/-- Every nonnegative capacity vector permits the empty used-tool set. -/
theorem empty_mem_capacityFamily (layout : CapacityLayout Tool Node)
    (capacity : Node → ℕ) : ∅ ∈ capacityFamily layout capacity := by
  intro node _
  simp

/-- The set-family semantics, independently of any tree normalization. -/
theorem capacityFamily_downward_closed (layout : CapacityLayout Tool Node)
    (capacity : Node → ℕ) {small large : Finset Tool} (hsub : small ⊆ large)
    (hlarge : large ∈ capacityFamily layout capacity) :
    small ∈ capacityFamily layout capacity := by
  intro node hnode
  exact (Finset.card_le_card (Finset.inter_subset_inter_right hsub)).trans
    (hlarge node hnode)

/-- The boundary family `2^U` is represented by the supports' cardinalities. -/
theorem capacityFamily_free (layout : CapacityLayout Tool Node) :
    capacityFamily layout (fun node => (layout.support node).card) = Set.univ := by
  apply Set.ext
  intro used
  constructor
  · intro _
    trivial
  · intro _ node _
    exact Finset.card_le_card Finset.inter_subset_right

/-- With singleton leaves, zero capacities describe exactly `{empty}`. -/
theorem capacityFamily_zero (layout : CapacityLayout Tool Node)
    (hsingletons : layout.HasSingletonNodes) :
    capacityFamily layout (fun _ => 0) = {∅} := by
  apply Set.ext
  intro used
  change (∀ node ∈ layout.nodes, (used ∩ layout.support node).card ≤ 0) ↔ used = ∅
  constructor
  · intro hused
    apply Finset.eq_empty_of_forall_notMem
    intro tool htool
    obtain ⟨node, hnode, hsupport⟩ := hsingletons tool
    have hin : tool ∈ used ∩ layout.support node := by
      exact Finset.mem_inter.mpr ⟨htool, by simp [hsupport]⟩
    exact (Nat.not_lt_of_ge (hused node hnode)) (Finset.card_pos.mpr ⟨tool, hin⟩)
  · intro hused
    subst used
    intro node _
    simp

/-- An empty family is a separate constructor, not a special numeric vector. -/
inductive CapacityEntry (Node : Type*) where
  | void
  | vector (capacity : Node → ℕ)

/-- Interpretation of a table entry as a family of used-tool sets. -/
def CapacityEntry.denote (layout : CapacityLayout Tool Node) :
    CapacityEntry Node → Set (Finset Tool)
  | .void => ∅
  | .vector capacity => capacityFamily layout capacity

/-- In fact no nonnegative numeric vector, not just zero, denotes `VOID`. -/
theorem capacityEntry_vector_ne_void (layout : CapacityLayout Tool Node)
    (capacity : Node → ℕ) :
    CapacityEntry.denote layout (.vector capacity) ≠
      CapacityEntry.denote layout .void := by
  intro heq
  have hempty := empty_mem_capacityFamily layout capacity
  change ∅ ∈ CapacityEntry.denote layout (.vector capacity) at hempty
  rw [heq] at hempty
  exact hempty

theorem capacityEntry_zero_ne_void (layout : CapacityLayout Tool Node) :
    CapacityEntry.denote layout (.vector (fun _ => 0)) ≠
      CapacityEntry.denote layout .void :=
  capacityEntry_vector_ne_void layout _

/-- `eq:laminar-extension-family`, with one actual unused compatible tool. -/
def usedExtension (eligible : Finset Tool) (family : Set (Finset Tool)) :
    Set (Finset Tool) :=
  {used | ∃ tool ∈ eligible, tool ∉ used ∧ insert tool used ∈ family}

/-- Empty compatibility makes extension impossible, even for a nonempty family. -/
theorem extension_empty (family : Set (Finset Tool)) :
    usedExtension ∅ family = ∅ := by
  apply Set.ext
  intro used
  simp [usedExtension]

/-- Extension cannot repair an already empty suffix family. -/
theorem extension_void (eligible : Finset Tool) :
    usedExtension eligible ∅ = ∅ := by
  apply Set.ext
  intro used
  simp [usedExtension]

/-- A capacity extension never introduces a used set violating the old vector. -/
theorem extension_capacityFamily_subset (layout : CapacityLayout Tool Node)
    (capacity : Node → ℕ) (eligible : Finset Tool) :
    usedExtension eligible (capacityFamily layout capacity) ⊆
      capacityFamily layout capacity := by
  rintro used ⟨tool, _, _, hinsert⟩
  exact capacityFamily_downward_closed layout capacity (Finset.subset_insert _ _) hinsert

/-- The intersection identity is exact before any subsequent normalization. -/
theorem capacityFamily_coordinate_min (layout : CapacityLayout Tool Node)
    (left right : Node → ℕ) :
    capacityFamily layout (fun node => min (left node) (right node)) =
      capacityFamily layout left ∩ capacityFamily layout right := by
  apply Set.ext
  intro used
  constructor
  · intro hused
    exact ⟨fun node hnode => (le_min_iff.mp (hused node hnode)).1,
      fun node hnode => (le_min_iff.mp (hused node hnode)).2⟩
  · rintro ⟨hleft, hright⟩ node hnode
    exact le_min (hleft node hnode) (hright node hnode)

/-- The table's coordinate-minimum operation, with an absorbing `VOID` flag. -/
def CapacityEntry.intersection : CapacityEntry Node → CapacityEntry Node → CapacityEntry Node
  | .void, _ => .void
  | _, .void => .void
  | .vector left, .vector right => .vector (fun node => min (left node) (right node))

/-- Coordinate minimum and the `VOID` cases implement family intersection. -/
theorem CapacityEntry.denote_intersection (layout : CapacityLayout Tool Node)
    (left right : CapacityEntry Node) :
    (left.intersection right).denote layout =
      left.denote layout ∩ right.denote layout := by
  cases left with
  | void => simp [CapacityEntry.intersection, CapacityEntry.denote]
  | vector left =>
    cases right with
    | void => simp [CapacityEntry.intersection, CapacityEntry.denote]
    | vector right => exact capacityFamily_coordinate_min layout left right

/-! ### The elementary normalization step

These hypotheses are the actual finite partition/cover data, not a field
postulating preservation of a capacity family. They can later be discharged
from the children of the manuscript's tree.
-/

/-- The child-partition count identity used in the normalization and slack
arguments, laminar-proofs.tex:33--34 and 50--59. -/
theorem used_count_eq_sum_children (layout : CapacityLayout Tool Node)
    (parent : Node) (children : Finset Node)
    (hdisjoint : (children : Set Node).PairwiseDisjoint layout.support)
    (hcover : children.biUnion layout.support = layout.support parent)
    (used : Finset Tool) :
    (used ∩ layout.support parent).card =
      ∑ child ∈ children, (used ∩ layout.support child).card := by
  rw [← hcover, Finset.inter_biUnion]
  apply Finset.card_biUnion
  intro left hleft right hright hne
  exact (hdisjoint hleft hright hne).mono
    Finset.inter_subset_right Finset.inter_subset_right

/-- Active child constraints imply the parent's additional sum bound.
The inequality needs only coverage; disjointness is needed for the exact
count identity above but not for this redundant-constraint argument. -/
theorem used_count_le_sum_children_capacity (layout : CapacityLayout Tool Node)
    (parent : Node) (children : Finset Node) (capacity : Node → ℕ)
    (hactive : children ⊆ layout.nodes)
    (hcover : children.biUnion layout.support = layout.support parent)
    {used : Finset Tool} (hused : used ∈ capacityFamily layout capacity) :
    (used ∩ layout.support parent).card ≤ ∑ child ∈ children, capacity child := by
  calc
    (used ∩ layout.support parent).card =
        (children.biUnion (fun child => used ∩ layout.support child)).card := by
      rw [← hcover, Finset.inter_biUnion]
    _ ≤ ∑ child ∈ children, (used ∩ layout.support child).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ child ∈ children, capacity child :=
      Finset.sum_le_sum (fun child hchild => hused child (hactive hchild))

section NormalizeAt

variable [DecidableEq Node]

/-- One bottom-up update from eq:laminar-normalized. Ordering the whole tree
and proving the normalized output are separate subsequent tasks. -/
def normalizeAt (parent : Node) (children : Finset Node) (capacity : Node → ℕ) :
    Node → ℕ :=
  Function.update capacity parent (min (capacity parent) (∑ child ∈ children, capacity child))

theorem normalizeAt_self (parent : Node) (children : Finset Node) (capacity : Node → ℕ) :
    normalizeAt parent children capacity parent =
      min (capacity parent) (∑ child ∈ children, capacity child) := by
  simp [normalizeAt]

theorem normalizeAt_of_ne (parent : Node) (children : Finset Node) (capacity : Node → ℕ)
    {node : Node} (hne : node ≠ parent) :
    normalizeAt parent children capacity node = capacity node :=
  Function.update_of_ne hne _ _

theorem normalizeAt_le (parent : Node) (children : Finset Node) (capacity : Node → ℕ)
    (node : Node) : normalizeAt parent children capacity node ≤ capacity node := by
  by_cases heq : node = parent
  · subst node
    rw [normalizeAt_self]
    exact min_le_left _ _
  · rw [normalizeAt_of_ne parent children capacity heq]

/-- The finite-cover proof that a single normalization update does not change
the represented family. In particular it applies to pairwise-disjoint tree
children partitioning their parent, with no correctness assumption hidden in
the layout data. -/
theorem capacityFamily_normalizeAt (layout : CapacityLayout Tool Node)
    (parent : Node) (children : Finset Node) (capacity : Node → ℕ)
    (hactive : children ⊆ layout.nodes)
    (hcover : children.biUnion layout.support = layout.support parent) :
    capacityFamily layout (normalizeAt parent children capacity) =
      capacityFamily layout capacity := by
  apply Set.ext
  intro used
  constructor
  · intro hused node hnode
    exact (hused node hnode).trans (normalizeAt_le parent children capacity node)
  · intro hused node hnode
    by_cases heq : node = parent
    · subst node
      rw [normalizeAt_self]
      exact le_min (hused parent hnode)
        (used_count_le_sum_children_capacity layout parent children capacity
          hactive hcover hused)
    · rw [normalizeAt_of_ne parent children capacity heq]
      exact hused node hnode

end NormalizeAt

end PaperProofs.Structure
