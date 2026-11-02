module

public import PaperProofs.Structure.LaminarTreePartition
public import Mathlib.Data.Finset.Lattice.Lemmas

/-!
The extension theorem `lem:laminar-extension`, proved on the actual inclusion
tree of the original finite input. Normalization is defined by its numeric
inequalities, not by an extension guarantee. The reverse implication descends
through genuine children by strong induction on the support cardinality.
No running-time or whole-tree normalization-output theorem is asserted here.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

theorem insert_inter_card_of_mem (used node : Finset Tool) {tool : Tool}
    (hin : tool ∈ node) (hunused : tool ∉ used) :
    (insert tool used ∩ node).card = (used ∩ node).card + 1 := by
  rw [Finset.insert_inter_of_mem hin]
  apply Finset.card_insert_of_notMem
  intro h
  exact hunused (Finset.mem_inter.mp h).1

variable [Fintype Tool]

/-- The paper's normalized Nat capacities: singleton values are at most one,
and every internal value is at most the sum of its actual children's values.
Nonnegativity is intrinsic to Nat. -/
def Normalized (stages : List (Finset Tool)) (capacity : Finset Tool → Nat) : Prop :=
  (∀ tool : Tool, capacity {tool} ≤ 1) ∧
    ∀ node ∈ nodeFamily stages, 1 < node.card →
      capacity node ≤ ∑ child ∈ children (nodeFamily stages) node, capacity child

/-- Ancestors are the actual active supports containing the current support. -/
def ancestors (stages : List (Finset Tool)) (node : Finset Tool) : Finset (Finset Tool) :=
  (nodeFamily stages).filter (fun ancestor => node ⊆ ancestor)

theorem mem_ancestors (stages : List (Finset Tool)) (node ancestor : Finset Tool) :
    ancestor ∈ ancestors stages node ↔ ancestor ∈ nodeFamily stages ∧ node ⊆ ancestor := by
  simp only [ancestors, Finset.mem_filter]

def AncestorSlack (stages : List (Finset Tool)) (capacity : Finset Tool → Nat)
    (used node : Finset Tool) : Prop :=
  ∀ ancestor ∈ ancestors stages node, (used ∩ ancestor).card < capacity ancestor

/-- Necessity counts the extra used tool at every ancestor. It needs neither
normalization nor a laminarity assumption. -/
theorem extension_necessity (stages : List (Finset Tool)) (capacity : Finset Tool → Nat)
    (used eligible : Finset Tool)
    (hextension : ∃ tool ∈ eligible, tool ∉ used ∧
      insert tool used ∈ capacityFamily (layout stages) capacity) :
    AncestorSlack stages capacity used eligible := by
  obtain ⟨tool, htool, hunused, hinsert⟩ := hextension
  intro ancestor hancestor
  obtain ⟨hactive, hsub⟩ := (mem_ancestors stages eligible ancestor).mp hancestor
  have hbound := hinsert ancestor hactive
  change (insert tool used ∩ ancestor).card ≤ capacity ancestor at hbound
  rw [insert_inter_card_of_mem used ancestor (hsub htool) hunused] at hbound
  exact Nat.lt_of_succ_le hbound

/-- The global capacity check for an actual newly inserted tool. Supports
not containing the tool are unchanged; every containing support gains one. -/
theorem insert_mem_capacityFamily_of_slack (stages : List (Finset Tool))
    (capacity : Finset Tool → Nat) (used : Finset Tool)
    (hused : used ∈ capacityFamily (layout stages) capacity) {tool : Tool}
    (hunused : tool ∉ used)
    (hslack : ∀ node ∈ nodeFamily stages, tool ∈ node →
      (used ∩ node).card < capacity node) :
    insert tool used ∈ capacityFamily (layout stages) capacity := by
  intro node hnode
  change (insert tool used ∩ node).card ≤ capacity node
  by_cases hin : tool ∈ node
  · rw [insert_inter_card_of_mem used node hin hunused]
    exact Nat.succ_le_of_lt (hslack node hnode hin)
  · rw [Finset.insert_inter_of_notMem hin]
    exact hused node hnode

section NonemptyTree

variable [Nonempty Tool]

/-- A slack internal node has a slack actual child. The exact child-count
identity comes from the already proved input-tree partition. -/
theorem slack_child_exists (stages : List (Finset Tool)) (hlaminar : LaminarSchedule stages)
    (capacity : Finset Tool → Nat) (hnormalized : Normalized stages capacity)
    (used : Finset Tool) {node : Finset Tool} (hnode : node ∈ nodeFamily stages)
    (hinternal : 1 < node.card) (hslack : (used ∩ node).card < capacity node) :
    ∃ child ∈ children (nodeFamily stages) node,
      (used ∩ child).card < capacity child := by
  have hcount := layout_used_count_eq_sum_children stages hlaminar hnode hinternal used
  change (used ∩ node).card =
    ∑ child ∈ children (nodeFamily stages) node, (used ∩ child).card at hcount
  by_contra hnone
  have hchildBound : ∀ child ∈ children (nodeFamily stages) node,
      capacity child ≤ (used ∩ child).card := by
    intro child hchild
    exact Nat.le_of_not_gt (fun h => hnone ⟨child, hchild, h⟩)
  have hsum := Finset.sum_le_sum hchildBound
  have hparentBound : capacity node ≤ (used ∩ node).card :=
    (hnormalized.2 node hnode hinternal).trans (by simpa only [← hcount] using hsum)
  exact (Nat.not_lt_of_ge hparentBound) hslack

/-- A child has no intermediate active support before its least parent.
Therefore slackness at the child plus all old ancestors gives precisely
slackness at every ancestor of the child. -/
theorem ancestorSlack_child (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (capacity : Finset Tool → Nat)
    (used : Finset Tool) {node child : Finset Tool}
    (hancestors : AncestorSlack stages capacity used node)
    (hchild : child ∈ children (nodeFamily stages) node)
    (hchildSlack : (used ∩ child).card < capacity child) :
    AncestorSlack stages capacity used child := by
  have hparent := ((mem_children_iff (nodeFamily_laminar stages hlaminar)
    (nodeFamily_nonempty_nodes stages) child node).mp hchild).2
  intro ancestor hancestor
  obtain ⟨hactive, hsub⟩ := (mem_ancestors stages child ancestor).mp hancestor
  by_cases heq : ancestor = child
  · subst ancestor
    exact hchildSlack
  · have hstrict : child ⊂ ancestor :=
      Finset.ssubset_iff_subset_ne.mpr ⟨hsub, Ne.symm heq⟩
    exact hancestors ancestor ((mem_ancestors stages node ancestor).mpr
      ⟨hactive, hparent.2.2 ancestor hactive hstrict⟩)

/-- Sufficiency is a genuine slack-child descent, using the strictly smaller
child cardinality as the strong-induction measure. Its returned tool satisfies
every active capacity constraint, not just the chosen descent path. -/
theorem extension_of_ancestorSlack (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (capacity : Finset Tool → Nat)
    (hnormalized : Normalized stages capacity) (used : Finset Tool)
    (hused : used ∈ capacityFamily (layout stages) capacity) :
    ∀ eligible ∈ nodeFamily stages, AncestorSlack stages capacity used eligible →
      ∃ tool ∈ eligible, tool ∉ used ∧ insert tool used ∈ capacityFamily (layout stages) capacity := by
  have aux : ∀ size : Nat, ∀ eligible : Finset Tool, eligible.card = size →
      eligible ∈ nodeFamily stages → AncestorSlack stages capacity used eligible →
        ∃ tool ∈ eligible, tool ∉ used ∧
          insert tool used ∈ capacityFamily (layout stages) capacity := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro eligible hsize heligible hancestors
      have hnonempty := nodeFamily_nonempty_nodes stages eligible heligible
      have hslack : (used ∩ eligible).card < capacity eligible :=
        hancestors eligible ((mem_ancestors stages eligible eligible).mpr
          ⟨heligible, fun _ h => h⟩)
      by_cases hsmall : eligible.card ≤ 1
      · have hone : eligible.card = 1 :=
          Nat.le_antisymm hsmall (Nat.succ_le_of_lt (Finset.card_pos.mpr hnonempty))
        obtain ⟨tool, hsingleton⟩ := Finset.card_eq_one.mp hone
        have hunused : tool ∉ used := by
          intro husedTool
          have hcount : (used ∩ eligible).card = 1 := by
            rw [hsingleton]
            simp [husedTool]
          have hcapacity : capacity eligible ≤ 1 := by
            rw [hsingleton]
            exact hnormalized.1 tool
          rw [hcount] at hslack
          exact (Nat.not_lt_of_ge hcapacity) hslack
        refine ⟨tool, by rw [hsingleton]; exact Finset.mem_singleton_self tool, hunused, ?_⟩
        apply insert_mem_capacityFamily_of_slack stages capacity used hused hunused
        intro node hnode htool
        exact hancestors node ((mem_ancestors stages eligible node).mpr
          ⟨hnode, by rw [hsingleton]; exact Finset.singleton_subset_iff.mpr htool⟩)
      · have hinternal : 1 < eligible.card := Nat.lt_of_not_ge hsmall
        obtain ⟨child, hchild, hchildSlack⟩ :=
          slack_child_exists stages hlaminar capacity hnormalized used heligible hinternal hslack
        have hchildActive : child ∈ nodeFamily stages := children_subset _ _ hchild
        have hchildSmaller : child.card < size := by
          rw [← hsize]
          exact child_card_lt_parent (nodeFamily stages) (nodeFamily_laminar stages hlaminar)
            (nodeFamily_nonempty_nodes stages) hchild
        have hchildAncestors :=
          ancestorSlack_child stages hlaminar capacity used hancestors hchild hchildSlack
        obtain ⟨tool, htool, hunused, hinsert⟩ :=
          ih child.card hchildSmaller child rfl hchildActive hchildAncestors
        have hchildSub : child ⊆ eligible :=
          ((mem_children_iff (nodeFamily_laminar stages hlaminar)
            (nodeFamily_nonempty_nodes stages) child eligible).mp hchild).2.2.1.subset
        exact ⟨tool, hchildSub htool, hunused, hinsert⟩
  intro eligible heligible hancestors
  exact aux eligible.card eligible rfl heligible hancestors

end NonemptyTree

/-- `lem:laminar-extension` with exactly the normalized-capacity, feasible-used
set and nonempty-active-eligibility hypotheses from the manuscript. -/
theorem extension_iff_ancestorSlack (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (capacity : Finset Tool → Nat)
    (hnormalized : Normalized stages capacity) (used eligible : Finset Tool)
    (hused : used ∈ capacityFamily (layout stages) capacity)
    (heligible : eligible ∈ nodeFamily stages) (hnonempty : eligible.Nonempty) :
    (∃ tool ∈ eligible, tool ∉ used ∧
      insert tool used ∈ capacityFamily (layout stages) capacity) ↔
      AncestorSlack stages capacity used eligible := by
  obtain ⟨tool, _⟩ := hnonempty
  let : Nonempty Tool := ⟨tool⟩
  exact ⟨extension_necessity stages capacity used eligible,
    extension_of_ancestorSlack stages hlaminar capacity hnormalized used hused eligible heligible⟩

end PaperProofs.Structure.LaminarTree
