module

public import PaperProofs.Structure.LaminarClosure
public import PaperProofs.Structure.LaminarTreeExecutable
public import Mathlib.Data.List.Sort

/-!
Whole-tree bottom-up normalization on the actual finite input tree.
The node order and parent table are preprocessing data. A normalization call
does not sort the tree or discover parents again. Children are currently
obtained by filtering the parent table; constant-time adjacency and capacity
access, and the paper's O(t) normalization bound, are not asserted here.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*} [DecidableEq Tool]

/-- One numeric update. Singleton leaves must not be normalized against an
empty child sum: their original zero/one capacity is retained. -/
def normalizeStep (childMap : Finset Tool → Finset (Finset Tool))
    (capacity : Finset Tool → Nat) (node : Finset Tool) : Finset Tool → Nat :=
  if 1 < node.card then normalizeAt node (childMap node) capacity else capacity

/-- A normalization pass through a previously prepared order. -/
def normalizeAlong (childMap : Finset Tool → Finset (Finset Tool)) :
    List (Finset Tool) → (Finset Tool → Nat) → Finset Tool → Nat
  | [], capacity => capacity
  | node :: later, capacity =>
      normalizeAlong childMap later (normalizeStep childMap capacity node)

theorem normalizeStep_le (childMap : Finset Tool → Finset (Finset Tool))
    (capacity : Finset Tool → Nat) (node target : Finset Tool) :
    normalizeStep childMap capacity node target ≤ capacity target := by
  unfold normalizeStep
  split_ifs
  · exact normalizeAt_le _ _ _ _
  · exact Nat.le_refl _

theorem normalizeStep_eq_of_ne (childMap : Finset Tool → Finset (Finset Tool))
    (capacity : Finset Tool → Nat) (node target : Finset Tool) (hne : target ≠ node) :
    normalizeStep childMap capacity node target = capacity target := by
  unfold normalizeStep
  split_ifs
  · exact normalizeAt_of_ne _ _ _ hne
  · rfl

theorem normalizeAlong_le (childMap : Finset Tool → Finset (Finset Tool))
    (order : List (Finset Tool)) (capacity : Finset Tool → Nat) (target : Finset Tool) :
    normalizeAlong childMap order capacity target ≤ capacity target := by
  induction order generalizing capacity with
  | nil => exact Nat.le_refl _
  | cons node later ih =>
    exact (ih (normalizeStep childMap capacity node)).trans
      (normalizeStep_le childMap capacity node target)

/-- A coordinate absent from the remaining pass can never change. -/
theorem normalizeAlong_eq_of_not_mem (childMap : Finset Tool → Finset (Finset Tool))
    (order : List (Finset Tool)) (capacity : Finset Tool → Nat) (target : Finset Tool)
    (hnot : target ∉ order) : normalizeAlong childMap order capacity target = capacity target := by
  revert hnot
  induction order generalizing capacity with
  | nil => intro _; rfl
  | cons node later ih =>
    intro hnot
    have hne : target ≠ node := fun h => hnot (List.mem_cons.mpr (Or.inl h))
    have htail : target ∉ later := fun h => hnot (List.mem_cons_of_mem _ h)
    rw [normalizeAlong, ih (normalizeStep childMap capacity node) htail]
    exact normalizeStep_eq_of_ne childMap capacity node target hne

section TreeCorrectness

variable [Fintype Tool] [Nonempty Tool]

theorem normalizeStep_preserves (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (childMap : Finset Tool → Finset (Finset Tool))
    (capacity : Finset Tool → Nat) (node : Finset Tool) (hnode : node ∈ nodeFamily stages)
    (hchildren : childMap node = children (nodeFamily stages) node) :
    capacityFamily (layout stages) (normalizeStep childMap capacity node) =
      capacityFamily (layout stages) capacity := by
  unfold normalizeStep
  split_ifs with hinternal
  · rw [hchildren]
    exact layout_normalizeAt_preserves stages hlaminar hnode hinternal capacity
  · rfl

/-- The update makes its own internal constraint true. Actual children are
proper supports, so updating the parent leaves their values unchanged. -/
theorem normalizeStep_internal_bound (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (childMap : Finset Tool → Finset (Finset Tool))
    (capacity : Finset Tool → Nat) (node : Finset Tool)
    (hchildren : childMap node = children (nodeFamily stages) node) (hinternal : 1 < node.card) :
    normalizeStep childMap capacity node node ≤
      ∑ child ∈ children (nodeFamily stages) node, normalizeStep childMap capacity node child := by
  have hsum :
      (∑ child ∈ children (nodeFamily stages) node,
        normalizeAt node (children (nodeFamily stages) node) capacity child) =
      ∑ child ∈ children (nodeFamily stages) node, capacity child := by
    apply Finset.sum_congr rfl
    intro child hchild
    have hstrict := ((mem_children_iff (nodeFamily_laminar stages hlaminar)
      (nodeFamily_nonempty_nodes stages) child node).mp hchild).2.2.1
    exact normalizeAt_of_ne _ _ _ (Finset.ssubset_iff_subset_ne.mp hstrict).2
  simp only [normalizeStep, hinternal, ↓reduceIte, hchildren]
  rw [normalizeAt_self, hsum]
  exact min_le_right _ _

/-- Any order of valid internal updates preserves the represented family. -/
theorem normalizeAlong_preserves (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (childMap : Finset Tool → Finset (Finset Tool))
    (order : List (Finset Tool)) (hactive : ∀ node ∈ order, node ∈ nodeFamily stages)
    (hchildren : ∀ node ∈ order, childMap node = children (nodeFamily stages) node)
    (capacity : Finset Tool → Nat) :
    capacityFamily (layout stages) (normalizeAlong childMap order capacity) =
      capacityFamily (layout stages) capacity := by
  revert hactive hchildren
  induction order generalizing capacity with
  | nil => intro _ _; rfl
  | cons node later ih =>
    intro hactive hchildren
    have hactiveTail : ∀ next ∈ later, next ∈ nodeFamily stages :=
      fun next h => hactive next (List.mem_cons_of_mem _ h)
    have hchildrenTail : ∀ next ∈ later, childMap next = children (nodeFamily stages) next :=
      fun next h => hchildren next (List.mem_cons_of_mem _ h)
    exact (ih (normalizeStep childMap capacity node) hactiveTail hchildrenTail).trans
      (normalizeStep_preserves stages hlaminar childMap capacity node
        (hactive node List.mem_cons_self) (hchildren node List.mem_cons_self))

/-- Ascending cardinalities ensure that after normalizing a node none of its
strictly smaller children can be updated later. This proves every processed
internal constraint, without assuming normalization as a loop invariant. -/
theorem normalizeAlong_internal_nodes (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (childMap : Finset Tool → Finset (Finset Tool))
    (order : List (Finset Tool)) (hactive : ∀ node ∈ order, node ∈ nodeFamily stages)
    (hchildren : ∀ node ∈ order, childMap node = children (nodeFamily stages) node)
    (hsorted : order.Pairwise (fun left right => left.card ≤ right.card))
    (capacity : Finset Tool → Nat) :
    ∀ node ∈ order, 1 < node.card →
      normalizeAlong childMap order capacity node ≤
        ∑ child ∈ children (nodeFamily stages) node, normalizeAlong childMap order capacity child := by
  revert hactive hchildren hsorted
  induction order generalizing capacity with
  | nil =>
    intro _ _ _ node hnode
    exact False.elim (List.not_mem_nil hnode)
  | cons head later ih =>
    intro hactive hchildren hsorted node hnode hinternal
    have hactiveTail : ∀ next ∈ later, next ∈ nodeFamily stages :=
      fun next h => hactive next (List.mem_cons_of_mem _ h)
    have hchildrenTail : ∀ next ∈ later, childMap next = children (nodeFamily stages) next :=
      fun next h => hchildren next (List.mem_cons_of_mem _ h)
    have hsortedTail := (List.pairwise_cons.mp hsorted).2
    rcases List.mem_cons.mp hnode with heq | htail
    · subst node
      have hstep := normalizeStep_internal_bound stages hlaminar childMap capacity head
        (hchildren head List.mem_cons_self) hinternal
      have hfixed : ∀ child ∈ children (nodeFamily stages) head,
          normalizeAlong childMap later (normalizeStep childMap capacity head) child =
            normalizeStep childMap capacity head child := by
        intro child hchild
        apply normalizeAlong_eq_of_not_mem
        intro hchildLater
        have hle := (List.pairwise_cons.mp hsorted).1 child hchildLater
        have hlt := child_card_lt_parent (nodeFamily stages) (nodeFamily_laminar stages hlaminar)
          (nodeFamily_nonempty_nodes stages) hchild
        exact (Nat.not_le_of_gt hlt) hle
      change normalizeAlong childMap later (normalizeStep childMap capacity head) head ≤
        ∑ child ∈ children (nodeFamily stages) head,
          normalizeAlong childMap later (normalizeStep childMap capacity head) child
      calc
        _ ≤ normalizeStep childMap capacity head head := normalizeAlong_le childMap later _ head
        _ ≤ ∑ child ∈ children (nodeFamily stages) head,
            normalizeStep childMap capacity head child := hstep
        _ = _ := Finset.sum_congr rfl (fun child hchild => (hfixed child hchild).symm)
    · exact ih (normalizeStep childMap capacity head) hactiveTail hchildrenTail hsortedTail
        node htail hinternal

/-- A full ascending pass produces the actual normalized vector. The only
input numeric assumption is the paper's initial singleton zero/one bound. -/
theorem normalizeAlong_normalized (stages : List (Finset Tool))
    (hlaminar : LaminarSchedule stages) (childMap : Finset Tool → Finset (Finset Tool))
    (order : List (Finset Tool)) (hactive : ∀ node ∈ order, node ∈ nodeFamily stages)
    (hchildren : ∀ node ∈ order, childMap node = children (nodeFamily stages) node)
    (hsorted : order.Pairwise (fun left right => left.card ≤ right.card))
    (hcomplete : ∀ node ∈ nodeFamily stages, node ∈ order)
    (capacity : Finset Tool → Nat) (hsingletons : ∀ tool : Tool, capacity {tool} ≤ 1) :
    Normalized stages (normalizeAlong childMap order capacity) := by
  refine ⟨fun tool => (normalizeAlong_le childMap order capacity {tool}).trans (hsingletons tool), ?_⟩
  intro node hnode hinternal
  exact normalizeAlong_internal_nodes stages hlaminar childMap order hactive hchildren hsorted
    capacity node (hcomplete node hnode) hinternal

end TreeCorrectness

/-- Preprocessing data only. No correctness, normalization or complexity
conclusion is stored as an input field. -/
structure NormalizationData (Tool : Type*) where
  order : List (Finset Tool)
  parentTable : List (Finset Tool × Option (Finset Tool))

/-- Current executable adjacency lookup scans the cached parent table.
An indexed adjacency representation and its cost certificate remain separate. -/
def NormalizationData.childSet (data : NormalizationData Tool) (parent : Finset Tool) :
    Finset (Finset Tool) :=
  ((data.parentTable.filter (fun entry => decide (entry.2 = some parent))).map Prod.fst).toFinset

theorem mem_data_childSet (data : NormalizationData Tool) (child parent : Finset Tool) :
    child ∈ data.childSet parent ↔
      ∃ entry ∈ data.parentTable, entry.1 = child ∧ entry.2 = some parent := by
  unfold NormalizationData.childSet
  constructor
  · intro h
    obtain ⟨entry, hentry, heq⟩ := List.mem_map.mp (List.mem_toFinset.mp h)
    obtain ⟨htable, hparent⟩ := List.mem_filter.mp hentry
    exact ⟨entry, htable, heq, by simpa using hparent⟩
  · rintro ⟨entry, htable, hchild, hparent⟩
    apply List.mem_toFinset.mpr
    exact List.mem_map.mpr ⟨entry, List.mem_filter.mpr ⟨htable, by simp [hparent]⟩, hchild⟩

/-- Prepare the node order and all parent choices once, before normalizing
the many suffix/budget vectors. Original stage order is not modified. -/
def prepareNormalization (q : Nat) (stages : List (Finset (Fin q))) :
    NormalizationData (Fin q) :=
  let nodes := explicitNodeList q stages
  {
    order := nodes.mergeSort (fun left right => decide (left.card ≤ right.card))
    parentTable := nodes.map (fun node => (node, parentFromList nodes node))
  }

/-- This entrypoint only consumes prepared data. It performs no sort or
parent search on a normalization call. -/
def NormalizationData.normalize (data : NormalizationData Tool)
    (capacity : Finset Tool → Nat) : Finset Tool → Nat :=
  normalizeAlong data.childSet data.order capacity

theorem mem_preparedOrder (q : Nat) (stages : List (Finset (Fin q))) (node : Finset (Fin q)) :
    node ∈ (prepareNormalization q stages).order ↔ node ∈ nodeFamily stages := by
  change node ∈ (explicitNodeList q stages).mergeSort
    (fun left right => decide (left.card ≤ right.card)) ↔ node ∈ nodeFamily stages
  rw [List.mem_mergeSort, ← List.mem_toFinset, explicitNodeList_toFinset]

theorem prepared_order_sorted (q : Nat) (stages : List (Finset (Fin q))) :
    (prepareNormalization q stages).order.Pairwise
      (fun left right => left.card ≤ right.card) := by
  change ((explicitNodeList q stages).mergeSort
    (fun left right => decide (left.card ≤ right.card))).Pairwise
      (fun left right => left.card ≤ right.card)
  have hsorted := List.pairwise_mergeSort
    (le := fun left right : Finset (Fin q) => decide (left.card ≤ right.card))
    (by
      intro left middle right hleft hright
      have hleft' : left.card ≤ middle.card := by simpa using hleft
      have hright' : middle.card ≤ right.card := by simpa using hright
      simpa using Nat.le_trans hleft' hright')
    (by intro left right; simpa using Nat.le_total left.card right.card)
    (explicitNodeList q stages)
  simpa using hsorted

theorem prepared_order_length_le (q : Nat) (stages : List (Finset (Fin q))) :
    (prepareNormalization q stages).order.length ≤ stages.length + q + 1 := by
  simpa [prepareNormalization] using explicitNodeList_length_le q stages

/-- The cached executable parent table yields exactly the already proved
canonical children of the same original tree. -/
theorem prepared_childSet_eq (q : Nat) (stages : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule stages) (parent : Finset (Fin q)) :
    (prepareNormalization q stages).childSet parent = children (nodeFamily stages) parent := by
  ext child
  rw [mem_data_childSet]
  constructor
  · rintro ⟨entry, hentry, hchild, hparent⟩
    change entry ∈ (explicitNodeList q stages).map
      (fun node => (node, parentFromList (explicitNodeList q stages) node)) at hentry
    obtain ⟨node, hnode, rfl⟩ := List.mem_map.mp hentry
    dsimp only at hchild hparent
    subst child
    have hactive : node ∈ nodeFamily stages := by
      have hin := List.mem_toFinset.mpr hnode
      rw [explicitNodeList_toFinset] at hin
      exact hin
    have hagree : parentFromList (explicitNodeList q stages) node =
        parent? (nodeFamily stages) node := explicitParent_agrees q stages hq hlaminar hactive
    exact Finset.mem_filter.mpr ⟨hactive, hagree.symm.trans hparent⟩
  · intro hchild
    obtain ⟨hactive, hcanonical⟩ := Finset.mem_filter.mp hchild
    have hlist : child ∈ explicitNodeList q stages := by
      apply List.mem_toFinset.mp
      rw [explicitNodeList_toFinset]
      exact hactive
    refine ⟨(child, parentFromList (explicitNodeList q stages) child), ?_, rfl, ?_⟩
    · change (child, parentFromList (explicitNodeList q stages) child) ∈
        (explicitNodeList q stages).map
          (fun node => (node, parentFromList (explicitNodeList q stages) node))
      exact List.mem_map.mpr ⟨child, hlist, rfl⟩
    · exact (explicitParent_agrees q stages hq hlaminar hactive).trans hcanonical

/-- Full semantic correctness of the executable whole-tree normalization. -/
theorem prepared_normalize_preserves (q : Nat) (stages : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule stages) (capacity : Finset (Fin q) → Nat) :
    capacityFamily (layout stages) ((prepareNormalization q stages).normalize capacity) =
      capacityFamily (layout stages) capacity := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  exact normalizeAlong_preserves stages hlaminar (prepareNormalization q stages).childSet
    (prepareNormalization q stages).order
    (fun node hnode => (mem_preparedOrder q stages node).mp hnode)
    (fun node _ => prepared_childSet_eq q stages hq hlaminar node) capacity

/-- Output normalization follows from the actual sorted order and child map,
not from a specification field or an assumed normalization oracle. -/
theorem prepared_normalize_normalized (q : Nat) (stages : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule stages) (capacity : Finset (Fin q) → Nat)
    (hsingletons : ∀ tool : Fin q, capacity {tool} ≤ 1) :
    Normalized stages ((prepareNormalization q stages).normalize capacity) := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  exact normalizeAlong_normalized stages hlaminar (prepareNormalization q stages).childSet
    (prepareNormalization q stages).order
    (fun node hnode => (mem_preparedOrder q stages node).mp hnode)
    (fun node _ => prepared_childSet_eq q stages hq hlaminar node)
    (prepared_order_sorted q stages)
    (fun node hnode => (mem_preparedOrder q stages node).mpr hnode) capacity hsingletons

/-- The original input bound `0 ≤ c_T ≤ |T|` supplies the singleton premise;
no stronger numeric input hypothesis is needed. -/
theorem prepared_normalize_normalized_of_bounded (q : Nat)
    (stages : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule stages)
    (capacity : Finset (Fin q) → Nat)
    (hbounded : ∀ node ∈ nodeFamily stages, capacity node ≤ node.card) :
    Normalized stages ((prepareNormalization q stages).normalize capacity) := by
  apply prepared_normalize_normalized q stages hq hlaminar capacity
  intro tool
  simpa only [Finset.card_singleton] using hbounded {tool} (singleton_mem stages tool)

theorem prepared_normalize_capacity_le_q (q : Nat) (stages : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule stages) (capacity : Finset (Fin q) → Nat)
    (hsingletons : ∀ tool : Fin q, capacity {tool} ≤ 1) {node : Finset (Fin q)}
    (hnode : node ∈ nodeFamily stages) :
    (prepareNormalization q stages).normalize capacity node ≤ q := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hnormalized := prepared_normalize_normalized q stages hq hlaminar capacity hsingletons
  simpa only [Fintype.card_fin] using normalized_capacity_le_toolCount stages hlaminar
    ((prepareNormalization q stages).normalize capacity) hnormalized hnode

def NormalizationData.normalizeEntry (data : NormalizationData Tool) :
    CapacityEntry (Finset Tool) → CapacityEntry (Finset Tool)
  | .void => .void
  | .vector capacity => .vector (data.normalize capacity)

/-- Reuse the existing exact coordinate-min intersection, then run the actual
whole-tree pass. Coordinate minimum alone is not asserted normalized. -/
def NormalizationData.intersectEntries (data : NormalizationData Tool)
    (left right : CapacityEntry (Finset Tool)) : CapacityEntry (Finset Tool) :=
  data.normalizeEntry (left.intersection right)

theorem prepared_normalizeEntry_sound (q : Nat) (stages : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule stages) (entry : CapacityEntry (Finset (Fin q))) :
    ((prepareNormalization q stages).normalizeEntry entry).denote (layout stages) =
      entry.denote (layout stages) := by
  cases entry with
  | void => rfl
  | vector capacity => exact prepared_normalize_preserves q stages hq hlaminar capacity

/-- The complete semantic intersection closure uses the proved full
normalizer and keeps the original tree and VOID interpretation. -/
theorem prepared_intersectEntries_sound (q : Nat) (stages : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule stages) (left right : CapacityEntry (Finset (Fin q))) :
    ((prepareNormalization q stages).intersectEntries left right).denote (layout stages) =
      left.denote (layout stages) ∩ right.denote (layout stages) := by
  rw [NormalizationData.intersectEntries, prepared_normalizeEntry_sound q stages hq hlaminar]
  exact CapacityEntry.denote_intersection (layout stages) left right

/-- Normalized input entries give normalized-or-VOID output. This proof does
not assume that coordinatewise minimum preserves normalization. -/
theorem prepared_intersectEntries_normalized (q : Nat)
    (stages : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule stages)
    (left right : CapacityEntry (Finset (Fin q)))
    (hleft : EntryNormalized stages left) (hright : EntryNormalized stages right) :
    EntryNormalized stages ((prepareNormalization q stages).intersectEntries left right) := by
  cases left with
  | void => cases right <;> trivial
  | vector leftCapacity =>
    cases right with
    | void => trivial
    | vector rightCapacity =>
      change Normalized stages ((prepareNormalization q stages).normalize
        (fun node => min (leftCapacity node) (rightCapacity node)))
      apply prepared_normalize_normalized q stages hq hlaminar
      intro tool
      simpa only [min_self] using min_le_min (hleft.1 tool) (hright.1 tool)

end PaperProofs.Structure.LaminarTree
