module

public import PaperProofs.Structure.IndexedNormalize
public import Mathlib.Data.Fintype.BigOperators
import Lean.Elab.Tactic.Omega

/-!
Workpad: stored cardinality/internal-node metadata and the actual adjacency
edge count of the same full-input tree. All structure fields below are data.
Correctness and the t-1 edge theorem are derived from the existing tree proofs.
RAM access, persistent Array/Vector copy costs and bit storage remain unproved.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree

variable {Tool : Type*}

structure IndexedTreeMetadata (cache : IndexedNodeCache Tool) where
  cardinalities : Vector Nat cache.nodes.size
  isInternal : Vector Bool cache.nodes.size
  root : Option cache.NodeId

def IndexedNodeCache.metadata [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool) :
    IndexedTreeMetadata cache :=
  let cardinalities := Vector.ofFn (fun node => (cache.decode node).card)
  { cardinalities := cardinalities
    isInternal := Vector.ofFn (fun node => decide (1 < cardinalities.get node))
    root := findNodeId cache.nodes Finset.univ }

theorem metadata_cardinality [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : cache.NodeId) : cache.metadata.cardinalities.get node = (cache.decode node).card :=
  cache_get_ofFn _ _

theorem metadata_isInternal [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : cache.NodeId) : cache.metadata.isInternal.get node = true ↔ 1 < (cache.decode node).card := by
  simp only [IndexedNodeCache.metadata, cache_get_ofFn, decide_eq_true_eq]

theorem metadata_cardinality_le_q (q : Nat) (cache : IndexedNodeCache (Fin q)) (node : cache.NodeId) :
    cache.metadata.cardinalities.get node ≤ q := by
  rw [metadata_cardinality]
  simpa only [Fintype.card_fin] using Finset.card_le_univ (cache.decode node)

theorem prepared_metadata_root_spec (q : Nat) (full : List (Finset (Fin q)))
    (root : (prepareNormalization q full).indexed.NodeId) :
    (prepareNormalization q full).indexed.metadata.root = some root ↔
      (prepareNormalization q full).indexed.decode root = Finset.univ :=
  findNodeId_eq_some_iff _ (prepared_indexed_nodes_nodup q full) _ root

theorem prepared_metadata_root_exists_unique (q : Nat) (full : List (Finset (Fin q))) :
    ∃! root : (prepareNormalization q full).indexed.NodeId,
      (prepareNormalization q full).indexed.metadata.root = some root := by
  obtain ⟨root, hdecode⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hpick := (prepared_metadata_root_spec q full root).mpr hdecode
  refine ⟨root, hpick, fun other hother => ?_⟩
  exact Option.some.inj (hother.symm.trans hpick)

theorem prepared_indexed_root_parent_none (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (root : (prepareNormalization q full).indexed.NodeId)
    (hroot : (prepareNormalization q full).indexed.decode root = Finset.univ) :
    (prepareNormalization q full).indexed.parents.get root = none := by
  cases hpick : (prepareNormalization q full).indexed.parents.get root with
  | none => rfl
  | some parent =>
    have hparent := (prepared_indexed_parent_iff q full hq hlaminar root parent).mp hpick
    have hstrict : Finset.univ ⊂ (prepareNormalization q full).indexed.decode parent := hroot ▸ hparent.2.1
    have heq : Finset.univ = (prepareNormalization q full).indexed.decode parent :=
      Finset.Subset.antisymm hstrict.subset (Finset.subset_univ _)
    exact False.elim ((Finset.ssubset_iff_subset_ne.mp hstrict).2 heq)

theorem prepared_indexed_nonroot_parent_exists_unique (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (child : (prepareNormalization q full).indexed.NodeId)
    (hnonroot : (prepareNormalization q full).indexed.decode child ≠ Finset.univ) :
    ∃! parent : (prepareNormalization q full).indexed.NodeId,
      (prepareNormalization q full).indexed.parents.get child = some parent := by
  obtain ⟨parentSupport, _, hparent⟩ := explicitParent_spec q full hq hlaminar
    (prepared_indexed_node_mem q full child) hnonroot
  obtain ⟨parent, hdecode⟩ := prepared_indexed_node_exists q full parentSupport hparent.1
  have hpick : (prepareNormalization q full).indexed.parents.get child = some parent :=
    (prepared_indexed_parent_iff q full hq hlaminar child parent).mpr (hdecode.symm ▸ hparent)
  refine ⟨parent, hpick, fun other hother => ?_⟩
  exact Option.some.inj (hother.symm.trans hpick)

theorem prepared_indexed_parent_none_iff (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (child : (prepareNormalization q full).indexed.NodeId) :
    (prepareNormalization q full).indexed.parents.get child = none ↔
      (prepareNormalization q full).indexed.decode child = Finset.univ := by
  constructor
  · intro hnone
    by_contra hnonroot
    obtain ⟨parent, hpick, _⟩ := prepared_indexed_nonroot_parent_exists_unique q full hq hlaminar child hnonroot
    rw [hnone] at hpick
    cases hpick
  · exact prepared_indexed_root_parent_none q full hq hlaminar child

/-- A generic finite counting identity, with both premises subsequently
discharged by the constructed cache, rather than stored as data fields. -/
theorem indexed_child_size_eq_fiber (cache : IndexedNodeCache Tool)
    (hnodup : ∀ parent, (cache.children.get parent).toList.Nodup)
    (hmem : ∀ child parent, child ∈ cache.children.get parent ↔ cache.parents.get child = some parent)
    (parent : cache.NodeId) :
    (cache.children.get parent).size =
      ((Finset.univ : Finset cache.NodeId).filter (fun child => cache.parents.get child = some parent)).card := by
  have hset : cache.childIds parent =
      (Finset.univ : Finset cache.NodeId).filter (fun child => cache.parents.get child = some parent) := by
    ext child
    simp only [IndexedNodeCache.childIds, List.mem_toFinset, Array.mem_toList_iff,
      hmem child parent, Finset.mem_filter, Finset.mem_univ, true_and]
  rw [← hset]
  simpa only [IndexedNodeCache.childIds, Array.length_toList] using
    (List.toFinset_card_of_nodup (hnodup parent)).symm

theorem indexed_child_size_sum_add_noneCount (cache : IndexedNodeCache Tool)
    (hnodup : ∀ parent, (cache.children.get parent).toList.Nodup)
    (hmem : ∀ child parent, child ∈ cache.children.get parent ↔ cache.parents.get child = some parent) :
    (∑ parent : cache.NodeId, (cache.children.get parent).size) +
      ((Finset.univ : Finset cache.NodeId).filter (fun child => cache.parents.get child = none)).card =
        cache.nodes.size := by
  have htotal := Finset.card_eq_sum_card_fiberwise (f := cache.parents.get)
    (s := (Finset.univ : Finset cache.NodeId)) (t := (Finset.univ : Finset (Option cache.NodeId)))
    (fun _ _ => Finset.mem_univ _)
  simp only [Finset.card_univ, Fintype.card_fin] at htotal
  rw [Fintype.sum_option] at htotal
  have hsum :
      (∑ parent : cache.NodeId,
        ((Finset.univ : Finset cache.NodeId).filter (fun child => cache.parents.get child = some parent)).card) =
        ∑ parent : cache.NodeId, (cache.children.get parent).size :=
    Finset.sum_congr rfl (fun parent _ => (indexed_child_size_eq_fiber cache hnodup hmem parent).symm)
  rw [hsum] at htotal
  omega

theorem prepared_indexed_edge_count (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (∑ parent : (prepareNormalization q full).indexed.NodeId,
      ((prepareNormalization q full).indexed.children.get parent).size) =
        (prepareNormalization q full).indexed.nodes.size - 1 := by
  obtain ⟨root, hroot⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hnone (child : (prepareNormalization q full).indexed.NodeId) :
      (prepareNormalization q full).indexed.parents.get child = none ↔ child = root := by
    rw [prepared_indexed_parent_none_iff q full hq hlaminar child]
    exact ⟨fun heq => prepared_indexed_decode_injective q full (heq.trans hroot.symm),
      fun heq => heq ▸ hroot⟩
  have hnoneSet :
      ((Finset.univ : Finset (prepareNormalization q full).indexed.NodeId).filter
        (fun child => (prepareNormalization q full).indexed.parents.get child = none)) = {root} := by
    ext child
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_singleton, hnone child]
  have hcount := indexed_child_size_sum_add_noneCount (prepareNormalization q full).indexed
    (fun parent => indexNodes_children_nodup _ _ parent)
    (fun child parent => indexNodes_child_mem _ _ child parent)
  rw [hnoneSet, Finset.card_singleton] at hcount
  omega

end PaperProofs.Structure.LaminarTree
