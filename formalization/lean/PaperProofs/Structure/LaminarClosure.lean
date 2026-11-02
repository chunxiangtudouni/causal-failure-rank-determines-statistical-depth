module

public import PaperProofs.Structure.LaminarExtension
import Lean.Elab.Tactic.Omega

/-!
The one-tree extension closure from `lem:laminar-closure`. The capacity
decrement is justified by the already proved extension semantics; its
normalization is proved from the actual child partition and the unique child
below a strict ancestor. Empty eligibility and zero path capacities produce
VOID, not a zero vector. Full intersection normalization is not claimed here.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

/-- Decrement exactly the ancestor supports; inactive coordinates are harmless. -/
def decrementAlong (eligible : Finset Tool) (capacity : Finset Tool → Nat)
    (node : Finset Tool) : Nat := if eligible ⊆ node then capacity node - 1 else capacity node

theorem decrementAlong_le (eligible : Finset Tool) (capacity : Finset Tool → Nat)
    (node : Finset Tool) : decrementAlong eligible capacity node ≤ capacity node := by
  unfold decrementAlong
  split_ifs
  · exact Nat.sub_le _ _
  · exact Nat.le_refl _

theorem decrementAlong_of_subset (eligible : Finset Tool) (capacity : Finset Tool → Nat)
    (node : Finset Tool) (hsub : eligible ⊆ node) :
    decrementAlong eligible capacity node = capacity node - 1 := by
  simp [decrementAlong, hsub]

variable [Fintype Tool]

def HasZeroAncestor (stages : List (Finset Tool)) (capacity : Finset Tool → Nat)
    (eligible : Finset Tool) : Prop :=
  ∃ node ∈ ancestors stages eligible, capacity node = 0

instance decidableHasZeroAncestor (stages : List (Finset Tool))
    (capacity : Finset Tool → Nat) (eligible : Finset Tool) :
    Decidable (HasZeroAncestor stages capacity eligible) :=
  inferInstanceAs (Decidable (∃ node ∈ ancestors stages eligible, capacity node = 0))

theorem ancestor_capacity_pos (stages : List (Finset Tool))
    (capacity : Finset Tool → Nat) (eligible : Finset Tool)
    (hzero : ¬ HasZeroAncestor stages capacity eligible) {node : Finset Tool}
    (hnode : node ∈ ancestors stages eligible) : 0 < capacity node := by
  apply Nat.pos_of_ne_zero
  intro h
  exact hzero ⟨node, hnode, h⟩

/-- The zero-budget free-family vector is genuinely normalized on the
constructed tree; even this base entry needs no assumed tree invariant. -/
theorem free_normalized (stages : List (Finset Tool)) (hlaminar : LaminarSchedule stages) :
    Normalized stages (fun node : Finset Tool => node.card) := by
  refine ⟨fun tool => by simp, ?_⟩
  intro node hnode hinternal
  obtain ⟨tool, _⟩ := Finset.card_pos.mp (Nat.lt_trans Nat.zero_lt_one hinternal)
  let : Nonempty Tool := ⟨tool⟩
  have hcount := layout_used_count_eq_sum_children stages hlaminar hnode hinternal
    (Finset.univ : Finset Tool)
  change (Finset.univ ∩ node).card =
    ∑ child ∈ children (nodeFamily stages) node, (Finset.univ ∩ child).card at hcount
  simp only [Finset.univ_inter] at hcount
  exact Nat.le_of_eq hcount

section NonemptyTree

variable [Nonempty Tool]

/-- The normalized-capacity bound follows from singleton bounds and the
actual child partition, by support-cardinality strong induction. -/
theorem normalized_capacity_le_card (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (capacity : Finset Tool → Nat)
    (hnormalized : Normalized stages capacity) :
    ∀ node ∈ nodeFamily stages, capacity node ≤ node.card := by
  have aux : ∀ size : Nat, ∀ node : Finset Tool, node.card = size →
      node ∈ nodeFamily stages → capacity node ≤ node.card := by
    intro size
    induction size using Nat.strong_induction_on with
    | h size ih =>
      intro node hsize hnode
      by_cases hsmall : node.card ≤ 1
      · have hone : node.card = 1 := Nat.le_antisymm hsmall
          (Nat.succ_le_of_lt (Finset.card_pos.mpr (nodeFamily_nonempty_nodes stages node hnode)))
        obtain ⟨tool, hsingleton⟩ := Finset.card_eq_one.mp hone
        rw [hsingleton, Finset.card_singleton]
        exact hnormalized.1 tool
      · have hinternal : 1 < node.card := Nat.lt_of_not_ge hsmall
        have hchildren : ∀ child ∈ children (nodeFamily stages) node,
            capacity child ≤ child.card := by
          intro child hchild
          have hless : child.card < size := by
            rw [← hsize]
            exact child_card_lt_parent (nodeFamily stages) (nodeFamily_laminar stages hlaminar)
              (nodeFamily_nonempty_nodes stages) hchild
          exact ih child.card hless child rfl (children_subset _ _ hchild)
        have hcount := layout_used_count_eq_sum_children stages hlaminar hnode hinternal
          (Finset.univ : Finset Tool)
        change (Finset.univ ∩ node).card =
          ∑ child ∈ children (nodeFamily stages) node, (Finset.univ ∩ child).card at hcount
        simp only [Finset.univ_inter] at hcount
        exact (hnormalized.2 node hnode hinternal).trans
          ((Finset.sum_le_sum hchildren).trans (Nat.le_of_eq hcount.symm))
  intro node hnode
  exact aux node.card node rfl hnode

theorem normalized_capacity_le_toolCount (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (capacity : Finset Tool → Nat)
    (hnormalized : Normalized stages capacity) {node : Finset Tool}
    (hnode : node ∈ nodeFamily stages) : capacity node ≤ Fintype.card Tool := by
  apply (normalized_capacity_le_card stages hlaminar capacity hnormalized node hnode).trans
  simpa only [Finset.card_univ] using Finset.card_le_card (Finset.subset_univ node)

/-- A strict ancestor has exactly one actual child containing the entire
eligible support. This is derived from laminarity and least-parent minimality. -/
theorem unique_child_containing (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) {eligible parent : Finset Tool}
    (heligible : eligible ∈ nodeFamily stages) (hparent : parent ∈ nodeFamily stages)
    (hstrict : eligible ⊂ parent) :
    ∃! child, child ∈ children (nodeFamily stages) parent ∧ eligible ⊆ child := by
  obtain ⟨tool, htool⟩ := nodeFamily_nonempty_nodes stages eligible heligible
  have hinternal : 1 < parent.card := Nat.lt_of_le_of_lt
    (Nat.succ_le_of_lt (Finset.card_pos.mpr ⟨tool, htool⟩)) (Finset.card_lt_card hstrict)
  obtain ⟨child, hchild, htoolChild⟩ := exists_child_containing (nodeFamily stages)
    (nodeFamily_laminar stages hlaminar) (singleton_mem stages) hparent hinternal
    (hstrict.subset htool)
  have hchildMem := children_subset _ _ hchild
  have hchildParent := ((mem_children_iff (nodeFamily_laminar stages hlaminar)
    (nodeFamily_nonempty_nodes stages) child parent).mp hchild).2
  have hcontains : eligible ⊆ child := by
    rcases nodeFamily_laminar stages hlaminar eligible heligible child hchildMem
      with hdisjoint | hsub | hsub
    · exact False.elim ((Finset.disjoint_left.mp hdisjoint) htool htoolChild)
    · exact hsub
    · by_cases heq : child = eligible
      · exact heq.symm.subset
      · have hbetween : child ⊂ eligible := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, heq⟩
        have hreverse := hchildParent.2.2 eligible heligible hbetween
        have hequal : eligible = parent := Finset.Subset.antisymm hstrict.subset hreverse
        exact False.elim ((Finset.ssubset_iff_subset_ne.mp hstrict).2 hequal)
  refine ⟨child, ⟨hchild, hcontains⟩, ?_⟩
  rintro other ⟨hother, hcontainsOther⟩
  by_contra hne
  have hdisjoint : Disjoint other child :=
    node_children_disjoint stages hlaminar parent hother hchild hne
  exact (Finset.disjoint_left.mp hdisjoint) (hcontainsOther htool) (hcontains htool)

/-- Below a strict ancestor exactly one positive child loses one unit, so
the sum of decremented child capacities also loses precisely one unit. -/
theorem decremented_children_sum_add_one (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (capacity : Finset Tool → Nat)
    {eligible parent : Finset Tool} (heligible : eligible ∈ nodeFamily stages)
    (hparent : parent ∈ nodeFamily stages) (hstrict : eligible ⊂ parent)
    (hzero : ¬ HasZeroAncestor stages capacity eligible) :
    (∑ child ∈ children (nodeFamily stages) parent, decrementAlong eligible capacity child) + 1 =
      ∑ child ∈ children (nodeFamily stages) parent, capacity child := by
  obtain ⟨chosen, ⟨hchosen, hcontains⟩, hunique⟩ :=
    unique_child_containing stages hlaminar heligible hparent hstrict
  have hpositive : 0 < capacity chosen := ancestor_capacity_pos stages capacity eligible hzero
    ((mem_ancestors stages eligible chosen).mpr ⟨children_subset _ _ hchosen, hcontains⟩)
  have hother : ∀ child ∈ (children (nodeFamily stages) parent).erase chosen,
      decrementAlong eligible capacity child = capacity child := by
    intro child hchild
    obtain ⟨hne, hmember⟩ := Finset.mem_erase.mp hchild
    have hnot : ¬ eligible ⊆ child := fun h => hne (hunique child ⟨hmember, h⟩)
    simp [decrementAlong, hnot]
  have hsum := Finset.sum_congr rfl hother
  have hold := Finset.sum_erase_add (children (nodeFamily stages) parent) capacity hchosen
  have hnew := Finset.sum_erase_add (children (nodeFamily stages) parent)
    (decrementAlong eligible capacity) hchosen
  rw [hsum] at hnew
  rw [decrementAlong_of_subset eligible capacity chosen hcontains] at hnew
  calc
    _ = ((children (nodeFamily stages) parent).erase chosen).sum capacity + capacity chosen := by
      rw [← hnew, Nat.add_assoc, Nat.sub_add_cancel (Nat.succ_le_of_lt hpositive)]
    _ = _ := hold

/-- Ancestor decrement preserves normalization without a normalization oracle:
at S only the left side decreases, and at a strict ancestor exactly one child
decreases with its parent. Other nodes and their children remain unchanged. -/
theorem decrementAlong_normalized (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (capacity : Finset Tool → Nat)
    (hnormalized : Normalized stages capacity) {eligible : Finset Tool}
    (heligible : eligible ∈ nodeFamily stages)
    (hzero : ¬ HasZeroAncestor stages capacity eligible) :
    Normalized stages (decrementAlong eligible capacity) := by
  refine ⟨fun tool => (decrementAlong_le eligible capacity {tool}).trans (hnormalized.1 tool), ?_⟩
  intro node hnode hinternal
  have hold := hnormalized.2 node hnode hinternal
  by_cases hancestor : eligible ⊆ node
  · by_cases heq : node = eligible
    · subst node
      have hchildren : ∀ child ∈ children (nodeFamily stages) eligible,
          decrementAlong eligible capacity child = capacity child := by
        intro child hchild
        have hstrict := ((mem_children_iff (nodeFamily_laminar stages hlaminar)
          (nodeFamily_nonempty_nodes stages) child eligible).mp hchild).2.2.1
        have hnot : ¬ eligible ⊆ child := by
          intro hsub
          exact (Finset.ssubset_iff_subset_ne.mp hstrict).2
            (Finset.Subset.antisymm hstrict.subset hsub)
        simp [decrementAlong, hnot]
      rw [Finset.sum_congr rfl hchildren]
      exact (decrementAlong_le eligible capacity eligible).trans hold
    · have hstrict : eligible ⊂ node :=
        Finset.ssubset_iff_subset_ne.mpr ⟨hancestor, Ne.symm heq⟩
      have hsum := decremented_children_sum_add_one stages hlaminar capacity
        heligible hnode hstrict hzero
      rw [decrementAlong_of_subset eligible capacity node hancestor]
      omega
  · have hchildren : ∀ child ∈ children (nodeFamily stages) node,
        decrementAlong eligible capacity child = capacity child := by
      intro child hchild
      have hstrict := ((mem_children_iff (nodeFamily_laminar stages hlaminar)
        (nodeFamily_nonempty_nodes stages) child node).mp hchild).2.2.1
      have hnot : ¬ eligible ⊆ child := fun h => hancestor (h.trans hstrict.subset)
      simp [decrementAlong, hnot]
    rw [Finset.sum_congr rfl hchildren]
    simp only [decrementAlong, hancestor, ↓reduceIte]
    exact hold

end NonemptyTree

/-- With no zero ancestor, the decremented family is precisely the old family
plus the required strict slack inequalities. Nat subtraction does not hide a
zero-capacity case because the latter has been excluded explicitly. -/
theorem mem_decremented_family_iff (stages : List (Finset Tool))
    (capacity : Finset Tool → Nat) (eligible used : Finset Tool)
    (hzero : ¬ HasZeroAncestor stages capacity eligible) :
    used ∈ capacityFamily (layout stages) (decrementAlong eligible capacity) ↔
      used ∈ capacityFamily (layout stages) capacity ∧ AncestorSlack stages capacity used eligible := by
  constructor
  · intro hused
    refine ⟨fun node hnode => (hused node hnode).trans (decrementAlong_le eligible capacity node), ?_⟩
    intro node hnode
    obtain ⟨hactive, hsub⟩ := (mem_ancestors stages eligible node).mp hnode
    have hbound := hused node hactive
    change (used ∩ node).card ≤ decrementAlong eligible capacity node at hbound
    simp only [decrementAlong, hsub, ↓reduceIte] at hbound
    have hpositive := ancestor_capacity_pos stages capacity eligible hzero hnode
    omega
  · rintro ⟨hused, hslack⟩ node hnode
    change (used ∩ node).card ≤ decrementAlong eligible capacity node
    by_cases hsub : eligible ⊆ node
    · have hstrict := hslack node ((mem_ancestors stages eligible node).mpr ⟨hnode, hsub⟩)
      simp only [decrementAlong, hsub, ↓reduceIte]
      omega
    · simp only [decrementAlong, hsub, ↓reduceIte]
      exact hused node hnode

theorem usedExtension_eq_empty_of_zeroAncestor (stages : List (Finset Tool))
    (capacity : Finset Tool → Nat) (eligible : Finset Tool)
    (hzero : HasZeroAncestor stages capacity eligible) :
    usedExtension eligible (capacityFamily (layout stages) capacity) = ∅ := by
  ext used
  constructor
  · intro hextension
    have hslack := extension_necessity stages capacity used eligible hextension
    obtain ⟨node, hnode, hcapacity⟩ := hzero
    have himpossible := hslack node hnode
    rw [hcapacity] at himpossible
    exact (Nat.not_lt_zero _) himpossible
  · intro h
    exact False.elim h

/-- The actual capacity-family extension equality, with zero paths excluded. -/
theorem decremented_family_eq_extension (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (capacity : Finset Tool → Nat)
    (hnormalized : Normalized stages capacity) (eligible : Finset Tool)
    (heligible : eligible ∈ nodeFamily stages) (hnonempty : eligible.Nonempty)
    (hzero : ¬ HasZeroAncestor stages capacity eligible) :
    capacityFamily (layout stages) (decrementAlong eligible capacity) =
      usedExtension eligible (capacityFamily (layout stages) capacity) := by
  ext used
  rw [mem_decremented_family_iff stages capacity eligible used hzero]
  constructor
  · rintro ⟨hused, hslack⟩
    exact (extension_iff_ancestorSlack stages hlaminar capacity hnormalized used eligible
      hused heligible hnonempty).mpr hslack
  · intro hextension
    exact ⟨extension_capacityFamily_subset (layout stages) capacity eligible hextension,
      extension_necessity stages capacity used eligible hextension⟩

/-- Empty eligibility and zero ancestors have their own VOID branch. -/
def extensionEntry (stages : List (Finset Tool)) (capacity : Finset Tool → Nat)
    (eligible : Finset Tool) : CapacityEntry (Finset Tool) :=
  if eligible = ∅ then .void else
    if HasZeroAncestor stages capacity eligible then .void else .vector (decrementAlong eligible capacity)

@[simp] theorem extensionEntry_empty (stages : List (Finset Tool))
    (capacity : Finset Tool → Nat) : extensionEntry stages capacity ∅ = .void := by
  simp [extensionEntry]

theorem extensionEntry_of_zeroAncestor (stages : List (Finset Tool))
    (capacity : Finset Tool → Nat) (eligible : Finset Tool)
    (hzero : HasZeroAncestor stages capacity eligible) :
    extensionEntry stages capacity eligible = .void := by
  by_cases hempty : eligible = ∅ <;> simp [extensionEntry, hempty, hzero]

/-- Includes all stage cases: empty sets, live tree nodes and zero capacities. -/
theorem extensionEntry_sound (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (capacity : Finset Tool → Nat)
    (hnormalized : Normalized stages capacity) (eligible : Finset Tool)
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily stages) :
    (extensionEntry stages capacity eligible).denote (layout stages) =
      usedExtension eligible (capacityFamily (layout stages) capacity) := by
  by_cases hempty : eligible = ∅
  · subst eligible
    simp [CapacityEntry.denote, extension_empty]
  · have hactive : eligible ∈ nodeFamily stages := heligible.resolve_left hempty
    have hnonempty : eligible.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
    by_cases hzero : HasZeroAncestor stages capacity eligible
    · rw [extensionEntry_of_zeroAncestor stages capacity eligible hzero]
      exact (usedExtension_eq_empty_of_zeroAncestor stages capacity eligible hzero).symm
    · simp only [extensionEntry, hempty, hzero, ↓reduceIte, CapacityEntry.denote]
      exact decremented_family_eq_extension stages hlaminar capacity hnormalized eligible
        hactive hnonempty hzero

def EntryNormalized (stages : List (Finset Tool)) : CapacityEntry (Finset Tool) → Prop
  | .void => True
  | .vector capacity => Normalized stages capacity

def extendEntry (stages : List (Finset Tool)) (eligible : Finset Tool) :
    CapacityEntry (Finset Tool) → CapacityEntry (Finset Tool)
  | .void => .void
  | .vector capacity => extensionEntry stages capacity eligible

@[simp] theorem extendEntry_void (stages : List (Finset Tool)) (eligible : Finset Tool) :
    extendEntry stages eligible .void = .void := rfl

theorem extendEntry_sound (stages : List (Finset Tool)) (hlaminar : LaminarSchedule stages)
    (eligible : Finset Tool) (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily stages)
    (entry : CapacityEntry (Finset Tool)) (hnormalized : EntryNormalized stages entry) :
    (extendEntry stages eligible entry).denote (layout stages) =
      usedExtension eligible (entry.denote (layout stages)) := by
  cases entry with
  | void => simp [CapacityEntry.denote, extension_void]
  | vector capacity => exact extensionEntry_sound stages hlaminar capacity hnormalized eligible heligible

/-- The extension operation really preserves normalized-or-VOID output.
Intersection still needs the separately outstanding whole-tree normalization. -/
theorem extendEntry_normalized (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (eligible : Finset Tool)
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily stages)
    (entry : CapacityEntry (Finset Tool)) (hnormalized : EntryNormalized stages entry) :
    EntryNormalized stages (extendEntry stages eligible entry) := by
  cases entry with
  | void => trivial
  | vector capacity =>
    by_cases hempty : eligible = ∅
    · subst eligible
      simp [extendEntry, EntryNormalized]
    · by_cases hzero : HasZeroAncestor stages capacity eligible
      · rw [extendEntry, extensionEntry_of_zeroAncestor stages capacity eligible hzero]
        trivial
      · have hnonempty : eligible.Nonempty := Finset.nonempty_iff_ne_empty.mpr hempty
        obtain ⟨tool, _⟩ := hnonempty
        let : Nonempty Tool := ⟨tool⟩
        simp only [extendEntry, extensionEntry, hempty, hzero, ↓reduceIte, EntryNormalized]
        exact decrementAlong_normalized stages hlaminar capacity hnormalized
          (heligible.resolve_left hempty) hzero

end PaperProofs.Structure.LaminarTree
