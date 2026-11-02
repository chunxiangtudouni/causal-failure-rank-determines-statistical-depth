module

public import PaperProofs.Structure.IndexedNodeCache
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Data.List.FinRange
public import Mathlib.Data.List.Pairwise
import Lean.Elab.Tactic.Omega

/-!
Workpad: actual indexed capacity vectors and cached-adjacency normalization.
No performance theorem is encoded as a structure field. The runtime pass
reads only vector indices and stored child arrays, and performs no node-set
search, parent reconstruction or sorting.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*}

def IndexedNodeCache.capacityLayout (cache : IndexedNodeCache Tool) : CapacityLayout Tool cache.NodeId :=
  { nodes := Finset.univ, support := cache.decode }

abbrev IndexedCapacity (cache : IndexedNodeCache Tool) := Vector Nat cache.nodes.size

def IndexedNodeCache.capacityFamily [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (capacity : IndexedCapacity cache) :
    Set (Finset Tool) := Structure.capacityFamily cache.capacityLayout capacity.get

def IndexedNodeCache.childIds (cache : IndexedNodeCache Tool) (parent : cache.NodeId) : Finset cache.NodeId :=
  (cache.children.get parent).toList.toFinset

def IndexedNodeCache.childSum (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (parent : cache.NodeId) : Nat := ((cache.children.get parent).toList.map capacity.get).sum

def IndexedNodeCache.normalizeStep (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (parent : cache.NodeId) : IndexedCapacity cache :=
  if 1 < (cache.decode parent).card then
    capacity.set parent.val (min (capacity.get parent) (cache.childSum capacity parent)) parent.isLt
  else capacity

def IndexedNodeCache.normalizeAlong (cache : IndexedNodeCache Tool) :
    List cache.NodeId → IndexedCapacity cache → IndexedCapacity cache
  | [], capacity => capacity
  | parent :: later, capacity => cache.normalizeAlong later (cache.normalizeStep capacity parent)

def IndexedNodeCache.normalize (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache) :
    IndexedCapacity cache := cache.normalizeAlong (List.finRange cache.nodes.size) capacity

theorem vector_set_get {α : Type*} {size : Nat} (values : Vector α size)
    (index target : Fin size) (value : α) :
    (values.set index.val value index.isLt).get target =
      if target = index then value else values.get target := by
  change (values.set index.val value index.isLt)[target.val] = _
  rw [Vector.getElem_set]
  by_cases heq : target = index
  · subst target
    simp
  · have hval : index.val ≠ target.val := fun h => heq (Fin.ext h.symm)
    simp only [hval, heq, ↓reduceIte]
    rfl

theorem indexNodes_children_nodup [DecidableEq Tool] (nodes : Array (Finset Tool))
    (sourceParent : Finset Tool → Option (Finset Tool)) (parent : Fin nodes.size) :
    ((indexNodes nodes sourceParent).children.get parent).toList.Nodup := by
  let parents : Vector (Option (Fin nodes.size)) nodes.size := Vector.ofFn
    (fun child : Fin nodes.size => (sourceParent nodes[child.val]).bind (findNodeId nodes))
  change ((Vector.ofFn (fun parent : Fin nodes.size =>
    ((List.finRange nodes.size).filter (fun child => decide (parents.get child = some parent))).toArray)).get
      parent).toList.Nodup
  rw [cache_get_ofFn, List.toList_toArray]
  exact List.Pairwise.filter _ (List.nodup_finRange nodes.size)

theorem childSum_eq_finset (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (parent : cache.NodeId) (hnodup : (cache.children.get parent).toList.Nodup) :
    cache.childSum capacity parent = ∑ child ∈ cache.childIds parent, capacity.get child :=
  (List.sum_toFinset capacity.get hnodup).symm

theorem indexed_normalizeStep_get (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (parent target : cache.NodeId) :
    (cache.normalizeStep capacity parent).get target =
      if 1 < (cache.decode parent).card ∧ target = parent then
        min (capacity.get parent) (cache.childSum capacity parent) else capacity.get target := by
  unfold IndexedNodeCache.normalizeStep
  by_cases hinternal : 1 < (cache.decode parent).card
  · simp only [hinternal, ↓reduceIte, true_and, vector_set_get]
  · simp only [hinternal, ↓reduceIte, false_and]

theorem indexed_normalizeStep_le (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (parent target : cache.NodeId) :
    (cache.normalizeStep capacity parent).get target ≤ capacity.get target := by
  rw [indexed_normalizeStep_get]
  split_ifs with h
  · rw [h.2]
    exact min_le_left _ _
  · exact Nat.le_refl _

theorem indexed_normalizeAlong_le (cache : IndexedNodeCache Tool) (order : List cache.NodeId)
    (capacity : IndexedCapacity cache) (target : cache.NodeId) :
    (cache.normalizeAlong order capacity).get target ≤ capacity.get target := by
  induction order generalizing capacity with
  | nil => exact Nat.le_refl _
  | cons parent later ih =>
    exact (ih (cache.normalizeStep capacity parent)).trans (indexed_normalizeStep_le cache capacity parent target)

theorem indexed_normalizeStep_fun (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (parent : cache.NodeId) (hinternal : 1 < (cache.decode parent).card)
    (hnodup : (cache.children.get parent).toList.Nodup) :
    (cache.normalizeStep capacity parent).get = normalizeAt parent (cache.childIds parent) capacity.get := by
  funext target
  rw [indexed_normalizeStep_get, childSum_eq_finset cache capacity parent hnodup]
  by_cases heq : target = parent
  · subst target
    simp only [hinternal, and_self, ↓reduceIte, normalizeAt_self]
  · simp only [heq, and_false, ↓reduceIte, normalizeAt_of_ne _ _ _ heq]

theorem prepared_indexed_children_cover (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (parent : (prepareNormalization q full).indexed.NodeId)
    (hinternal : 1 < ((prepareNormalization q full).indexed.decode parent).card) :
    ((prepareNormalization q full).indexed.childIds parent).biUnion
      (prepareNormalization q full).indexed.decode =
        (prepareNormalization q full).indexed.decode parent := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hcover := node_children_cover full hlaminar (prepared_indexed_node_mem q full parent) hinternal
  change (children (nodeFamily full) ((prepareNormalization q full).indexed.decode parent)).biUnion id =
    (prepareNormalization q full).indexed.decode parent at hcover
  rw [← hcover, ← prepared_indexed_children_decode q full hq hlaminar parent, Finset.image_biUnion]
  rfl

theorem prepared_indexed_normalizeStep_preserves (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (parent : (prepareNormalization q full).indexed.NodeId) :
    (prepareNormalization q full).indexed.capacityFamily
      ((prepareNormalization q full).indexed.normalizeStep capacity parent) =
        (prepareNormalization q full).indexed.capacityFamily capacity := by
  by_cases hinternal : 1 < ((prepareNormalization q full).indexed.decode parent).card
  · unfold IndexedNodeCache.capacityFamily
    rw [indexed_normalizeStep_fun _ capacity parent hinternal (indexNodes_children_nodup _ _ parent)]
    exact capacityFamily_normalizeAt _ parent _ _ (Finset.subset_univ _)
      (prepared_indexed_children_cover q full hq hlaminar parent hinternal)
  · simp only [IndexedNodeCache.normalizeStep, hinternal, ↓reduceIte]

theorem prepared_indexed_normalizeAlong_preserves (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (order : List (prepareNormalization q full).indexed.NodeId)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) :
    (prepareNormalization q full).indexed.capacityFamily
      ((prepareNormalization q full).indexed.normalizeAlong order capacity) =
        (prepareNormalization q full).indexed.capacityFamily capacity := by
  induction order generalizing capacity with
  | nil => rfl
  | cons parent later ih =>
    exact (ih ((prepareNormalization q full).indexed.normalizeStep capacity parent)).trans
      (prepared_indexed_normalizeStep_preserves q full hq hlaminar capacity parent)

def IndexedNormalized (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache) : Prop :=
  (∀ node, (cache.decode node).card = 1 → capacity.get node ≤ 1) ∧
    ∀ node, 1 < (cache.decode node).card → capacity.get node ≤ cache.childSum capacity node

theorem indexed_normalizeAlong_eq_of_not_mem (cache : IndexedNodeCache Tool)
    (order : List cache.NodeId) (capacity : IndexedCapacity cache) (target : cache.NodeId)
    (hnot : target ∉ order) : (cache.normalizeAlong order capacity).get target = capacity.get target := by
  induction order generalizing capacity with
  | nil => rfl
  | cons parent later ih =>
    have hne : target ≠ parent := fun heq => hnot (heq ▸ List.mem_cons_self)
    have htail : target ∉ later := fun hmem => hnot (List.mem_cons_of_mem _ hmem)
    rw [IndexedNodeCache.normalizeAlong, ih _ htail, indexed_normalizeStep_get]
    simp only [hne, and_false, ↓reduceIte]

theorem indexed_normalizeStep_internal_bound (cache : IndexedNodeCache Tool)
    (capacity : IndexedCapacity cache) (parent : cache.NodeId)
    (hinternal : 1 < (cache.decode parent).card)
    (hchildNe : ∀ child ∈ (cache.children.get parent).toList, child ≠ parent) :
    (cache.normalizeStep capacity parent).get parent ≤
      cache.childSum (cache.normalizeStep capacity parent) parent := by
  have hfixed (child : cache.NodeId) (hmem : child ∈ (cache.children.get parent).toList) :
      (cache.normalizeStep capacity parent).get child = capacity.get child := by
    rw [indexed_normalizeStep_get]
    simp only [hchildNe child hmem, and_false, ↓reduceIte]
  have hsum : cache.childSum (cache.normalizeStep capacity parent) parent = cache.childSum capacity parent :=
    congrArg List.sum (List.map_congr_left hfixed)
  rw [hsum, indexed_normalizeStep_get]
  simp only [hinternal, and_self, ↓reduceIte]
  exact min_le_right _ _

theorem indexed_normalizeAlong_internal (cache : IndexedNodeCache Tool)
    (order : List cache.NodeId)
    (hchildren : ∀ parent child, child ∈ (cache.children.get parent).toList →
      (cache.decode child).card < (cache.decode parent).card)
    (hsorted : order.Pairwise (fun left right => (cache.decode left).card ≤ (cache.decode right).card))
    (capacity : IndexedCapacity cache) :
    ∀ node ∈ order, 1 < (cache.decode node).card →
      (cache.normalizeAlong order capacity).get node ≤
        cache.childSum (cache.normalizeAlong order capacity) node := by
  induction order generalizing capacity with
  | nil => intro node hmem; exact False.elim (List.not_mem_nil hmem)
  | cons parent later ih =>
    intro node hnode hinternal
    have htail := (List.pairwise_cons.mp hsorted).2
    rcases List.mem_cons.mp hnode with heq | hmem
    · subst node
      have hstep := indexed_normalizeStep_internal_bound cache capacity parent hinternal
        (fun child hchild heq => by
          have hlt := hchildren parent child hchild
          rw [heq] at hlt
          exact Nat.lt_irrefl _ hlt)
      have hfixed (child : cache.NodeId) (hchild : child ∈ (cache.children.get parent).toList) :
          (cache.normalizeAlong later (cache.normalizeStep capacity parent)).get child =
            (cache.normalizeStep capacity parent).get child := by
        apply indexed_normalizeAlong_eq_of_not_mem
        intro hchildLater
        have hle := (List.pairwise_cons.mp hsorted).1 child hchildLater
        exact (Nat.not_le_of_gt (hchildren parent child hchild)) hle
      change (cache.normalizeAlong later (cache.normalizeStep capacity parent)).get parent ≤ _
      calc
        _ ≤ (cache.normalizeStep capacity parent).get parent := indexed_normalizeAlong_le _ _ _ _
        _ ≤ cache.childSum (cache.normalizeStep capacity parent) parent := hstep
        _ = cache.childSum (cache.normalizeAlong later (cache.normalizeStep capacity parent)) parent :=
          congrArg List.sum (List.map_congr_left (fun child hchild => (hfixed child hchild).symm))
    · exact ih htail (cache.normalizeStep capacity parent) node hmem hinternal

theorem prepared_indexed_child_card_lt (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (parent child : (prepareNormalization q full).indexed.NodeId)
    (hchild : child ∈ ((prepareNormalization q full).indexed.children.get parent).toList) :
    ((prepareNormalization q full).indexed.decode child).card <
      ((prepareNormalization q full).indexed.decode parent).card := by
  have hparent := (prepared_indexed_parent_iff q full hq hlaminar child parent).mp
    ((indexNodes_child_mem _ _ child parent).mp (Array.mem_toList_iff.mp hchild))
  exact Finset.card_lt_card hparent.2.1

theorem prepared_indexed_order_sorted (q : Nat) (full : List (Finset (Fin q))) :
    (List.finRange (prepareNormalization q full).indexed.nodes.size).Pairwise
      (fun left right => ((prepareNormalization q full).indexed.decode left).card ≤
        ((prepareNormalization q full).indexed.decode right).card) := by
  apply (List.pairwise_lt_finRange _).imp
  intro left right hlt
  have hsorted := (prepared_order_sorted q full).rel_get_of_lt
    (a := ⟨left.val, left.isLt⟩) (b := ⟨right.val, right.isLt⟩) hlt
  change ((prepareNormalization q full).order.toArray[left.val]).card ≤
    ((prepareNormalization q full).order.toArray[right.val]).card
  simpa only [List.get_eq_getElem, List.getElem_toArray] using hsorted

theorem prepared_indexed_normalize_normalized (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hsingletons : ∀ node, ((prepareNormalization q full).indexed.decode node).card = 1 →
      capacity.get node ≤ 1) :
    IndexedNormalized (prepareNormalization q full).indexed
      ((prepareNormalization q full).indexed.normalize capacity) := by
  refine ⟨fun node hsingle => ?_, ?_⟩
  · exact (indexed_normalizeAlong_le _ _ _ node).trans (hsingletons node hsingle)
  · intro node hinternal
    exact indexed_normalizeAlong_internal _ _ (prepared_indexed_child_card_lt q full hq hlaminar)
      (prepared_indexed_order_sorted q full) capacity node (List.mem_finRange _) hinternal

/-- A specification bridge to the existing support-indexed capacity family.
Runtime normalization does not use this preprocessing support lookup. -/
def IndexedNodeCache.unindexCapacity [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (capacity : IndexedCapacity cache) (support : Finset Tool) : Nat :=
  match findNodeId cache.nodes support with
  | none => 0
  | some index => capacity.get index

theorem unindexCapacity_at [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (hnodup : cache.nodes.toList.Nodup) (capacity : IndexedCapacity cache) (index : cache.NodeId) :
    cache.unindexCapacity capacity (cache.decode index) = capacity.get index := by
  have hfind : findNodeId cache.nodes (cache.decode index) = some index :=
    (findNodeId_eq_some_iff cache.nodes hnodup _ index).mpr rfl
  simp only [IndexedNodeCache.unindexCapacity, hfind]

theorem prepared_indexed_nodes_nodup (q : Nat) (full : List (Finset (Fin q))) :
    (prepareNormalization q full).indexed.nodes.toList.Nodup := by
  change (prepareNormalization q full).order.toArray.toList.Nodup
  simpa only [List.toList_toArray] using prepared_order_nodup q full

theorem prepared_indexed_family_eq (q : Nat) (full : List (Finset (Fin q)))
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) :
    (prepareNormalization q full).indexed.capacityFamily capacity =
      Structure.capacityFamily (layout full) ((prepareNormalization q full).indexed.unindexCapacity capacity) := by
  ext used
  constructor
  · intro hused node hnode
    obtain ⟨index, hdecode⟩ := prepared_indexed_node_exists q full node hnode
    have hbound := hused index (Finset.mem_univ index)
    change (used ∩ (prepareNormalization q full).indexed.decode index).card ≤ capacity.get index at hbound
    rw [← hdecode, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)]
    exact hbound
  · intro hused index _
    have hbound := hused _ (prepared_indexed_node_mem q full index)
    rw [unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)] at hbound
    exact hbound

theorem prepared_indexed_childSum_eq_original (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (parent : (prepareNormalization q full).indexed.NodeId) :
    (prepareNormalization q full).indexed.childSum capacity parent =
      ∑ child ∈ children (nodeFamily full) ((prepareNormalization q full).indexed.decode parent),
        (prepareNormalization q full).indexed.unindexCapacity capacity child := by
  rw [← prepared_indexed_children_decode q full hq hlaminar parent]
  rw [Finset.sum_image (fun left _ right _ heq => prepared_indexed_decode_injective q full heq)]
  simp_rw [unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)]
  exact childSum_eq_finset _ capacity parent (indexNodes_children_nodup _ _ parent)

theorem prepared_indexed_normalized_to_original (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hnormalized : IndexedNormalized (prepareNormalization q full).indexed capacity) :
    Normalized full ((prepareNormalization q full).indexed.unindexCapacity capacity) := by
  refine ⟨fun tool => ?_, ?_⟩
  · obtain ⟨index, hdecode⟩ := prepared_indexed_node_exists q full {tool} (singleton_mem full tool)
    rw [← hdecode, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)]
    apply hnormalized.1
    simp only [hdecode, Finset.card_singleton]
  · intro node hnode hinternal
    obtain ⟨index, hdecode⟩ := prepared_indexed_node_exists q full node hnode
    rw [← hdecode, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full),
      ← prepared_indexed_childSum_eq_original q full hq hlaminar capacity index]
    exact hnormalized.2 index (hdecode.symm ▸ hinternal)

theorem prepared_indexed_normalize_preserves_original (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) :
    Structure.capacityFamily (layout full)
      ((prepareNormalization q full).indexed.unindexCapacity
        ((prepareNormalization q full).indexed.normalize capacity)) =
      Structure.capacityFamily (layout full) ((prepareNormalization q full).indexed.unindexCapacity capacity) := by
  rw [← prepared_indexed_family_eq, ← prepared_indexed_family_eq]
  exact prepared_indexed_normalizeAlong_preserves q full hq hlaminar _ capacity

theorem prepared_indexed_normalize_capacity_le_q (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hsingletons : ∀ node, ((prepareNormalization q full).indexed.decode node).card = 1 →
      capacity.get node ≤ 1) (node : (prepareNormalization q full).indexed.NodeId) :
    ((prepareNormalization q full).indexed.normalize capacity).get node ≤ q := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hnormalized := prepared_indexed_normalized_to_original q full hq hlaminar _
    (prepared_indexed_normalize_normalized q full hq hlaminar capacity hsingletons)
  have hbound := normalized_capacity_le_toolCount full hlaminar _ hnormalized
    (prepared_indexed_node_mem q full node)
  rw [unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)] at hbound
  simpa only [Fintype.card_fin] using hbound

end PaperProofs.Structure.LaminarTree
