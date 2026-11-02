module

public import PaperProofs.Structure.IndexedEntry
import Lean.Elab.Tactic.Omega

/-!
Actual fuel-bounded traversal of the stored parent pointers. On the positive-q
full-input laminar cache, node indices strictly grow along parent edges. This
proves that fuel t enumerates precisely all support ancestors without repeats.
Length is a combinatorial traversal bound, not a RAM execution-time claim.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedAncestors

variable {Tool : Type*}

def parentChain (cache : IndexedNodeCache Tool) : Nat → cache.NodeId → List cache.NodeId
  | 0, _ => []
  | fuel + 1, node => node :: match cache.parents.get node with
      | none => []
      | some parent => parentChain cache fuel parent

def ancestorChain (cache : IndexedNodeCache Tool) (node : cache.NodeId) : List cache.NodeId :=
  parentChain cache cache.nodes.size node

theorem parentChain_length_le (cache : IndexedNodeCache Tool) (fuel : Nat) (node : cache.NodeId) :
    (parentChain cache fuel node).length ≤ fuel := by
  induction fuel generalizing node with
  | zero => exact Nat.le_refl 0
  | succ fuel ih =>
    cases hparent : cache.parents.get node with
    | none => simp only [parentChain, hparent, List.length_singleton]; omega
    | some parent =>
      simpa only [parentChain, hparent, List.length_cons] using Nat.succ_le_succ (ih parent)

theorem ancestorChain_length_le (cache : IndexedNodeCache Tool) (node : cache.NodeId) :
    (ancestorChain cache node).length ≤ cache.nodes.size := parentChain_length_le cache _ node

theorem parentChain_index_le (cache : IndexedNodeCache Tool)
    (hincreasing : ∀ child parent, cache.parents.get child = some parent → child.val < parent.val)
    (fuel : Nat) (node target : cache.NodeId) (hmem : target ∈ parentChain cache fuel node) :
    node.val ≤ target.val := by
  induction fuel generalizing node with
  | zero => cases hmem
  | succ fuel ih =>
    simp only [parentChain, List.mem_cons] at hmem
    rcases hmem with heq | hmem
    · exact heq.symm.le
    · cases hparent : cache.parents.get node with
      | none => simp only [hparent, List.not_mem_nil] at hmem
      | some parent =>
        have htail : target ∈ parentChain cache fuel parent := by simpa only [hparent] using hmem
        exact (hincreasing node parent hparent).le.trans (ih parent htail)

theorem parentChain_nodup (cache : IndexedNodeCache Tool)
    (hincreasing : ∀ child parent, cache.parents.get child = some parent → child.val < parent.val)
    (fuel : Nat) (node : cache.NodeId) : (parentChain cache fuel node).Nodup := by
  induction fuel generalizing node with
  | zero => exact List.nodup_nil
  | succ fuel ih =>
    cases hparent : cache.parents.get node with
    | none => simp only [parentChain, hparent, List.nodup_singleton]
    | some parent =>
      simp only [parentChain, hparent, List.nodup_cons]
      refine ⟨?_, ih parent⟩
      intro hmem
      have hle := parentChain_index_le cache hincreasing fuel parent node hmem
      exact (not_le_of_gt (hincreasing node parent hparent)) hle

theorem prepared_parent_index_lt (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (child parent : (prepareNormalization q full).indexed.NodeId)
    (hparent : (prepareNormalization q full).indexed.parents.get child = some parent) :
    child.val < parent.val := by
  have hstrict := ((prepared_indexed_parent_iff q full hq hlaminar child parent).mp hparent).2.1
  have hcard := Finset.card_lt_card hstrict
  by_contra hnot
  rcases lt_or_eq_of_le (Nat.le_of_not_gt hnot) with hlt | heq
  · have hsorted := (prepared_order_sorted q full).rel_get_of_lt
      (a := ⟨parent.val, parent.isLt⟩) (b := ⟨child.val, child.isLt⟩) hlt
    have hreverse : ((prepareNormalization q full).indexed.decode parent).card ≤
        ((prepareNormalization q full).indexed.decode child).card := by
      change ((prepareNormalization q full).order.toArray[parent.val]).card ≤
        ((prepareNormalization q full).order.toArray[child.val]).card
      simpa only [List.get_eq_getElem, List.getElem_toArray] using hsorted
    exact (not_le_of_gt hcard) hreverse
  · have heqNode : parent = child := Fin.ext heq
    subst parent
    exact (Nat.lt_irrefl _) hcard

theorem prepared_parentChain_mem_iff (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (fuel : Nat)
    (node target : (prepareNormalization q full).indexed.NodeId)
    (hsufficient : (prepareNormalization q full).indexed.nodes.size ≤ fuel + node.val) :
    target ∈ parentChain (prepareNormalization q full).indexed fuel node ↔
      (prepareNormalization q full).indexed.decode node ⊆ (prepareNormalization q full).indexed.decode target := by
  induction fuel generalizing node with
  | zero => exact False.elim (by have := node.isLt; omega)
  | succ fuel ih =>
    cases hparent : (prepareNormalization q full).indexed.parents.get node with
    | none =>
      simp only [parentChain, hparent, List.mem_cons, List.not_mem_nil, or_false]
      constructor
      · intro heq
        subst target
        exact Finset.Subset.refl _
      · intro hsub
        have hroot := (prepared_indexed_parent_none_iff q full hq hlaminar node).mp hparent
        apply prepared_indexed_decode_injective q full
        have htarget : (prepareNormalization q full).indexed.decode target = Finset.univ :=
          Finset.Subset.antisymm (Finset.subset_univ _) (hroot ▸ hsub)
        exact htarget.trans hroot.symm
    | some parent =>
      have hparentSpec := (prepared_indexed_parent_iff q full hq hlaminar node parent).mp hparent
      have hindex := prepared_parent_index_lt q full hq hlaminar node parent hparent
      have htail : (prepareNormalization q full).indexed.nodes.size ≤ fuel + parent.val := by omega
      simp only [parentChain, hparent, List.mem_cons]
      rw [ih parent htail]
      constructor
      · rintro (heq | hsub)
        · subst target
          exact Finset.Subset.refl _
        · exact hparentSpec.2.1.subset.trans hsub
      · intro hsub
        by_cases heq : target = node
        · exact Or.inl heq
        · apply Or.inr
          apply hparentSpec.2.2 _ (prepared_indexed_node_mem q full target)
          exact Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h =>
            heq (prepared_indexed_decode_injective q full h).symm⟩

theorem prepared_ancestorChain_mem_iff (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (node target : (prepareNormalization q full).indexed.NodeId) :
    target ∈ ancestorChain (prepareNormalization q full).indexed node ↔
      (prepareNormalization q full).indexed.decode node ⊆ (prepareNormalization q full).indexed.decode target :=
  prepared_parentChain_mem_iff q full hq hlaminar _ node target (Nat.le_add_right _ _)

theorem prepared_ancestorChain_nodup (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (node : (prepareNormalization q full).indexed.NodeId) :
    (ancestorChain (prepareNormalization q full).indexed node).Nodup :=
  parentChain_nodup _ (prepared_parent_index_lt q full hq hlaminar) _ node

theorem prepared_ancestorChain_image (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (node : (prepareNormalization q full).indexed.NodeId) :
    ((ancestorChain (prepareNormalization q full).indexed node).toFinset.image
      (prepareNormalization q full).indexed.decode) =
      ancestors full ((prepareNormalization q full).indexed.decode node) := by
  ext support
  rw [Finset.mem_image]
  constructor
  · rintro ⟨target, htarget, rfl⟩
    exact (mem_ancestors full _ _).mpr ⟨prepared_indexed_node_mem q full target,
      (prepared_ancestorChain_mem_iff q full hq hlaminar node target).mp (List.mem_toFinset.mp htarget)⟩
  · intro hsupport
    obtain ⟨hactive, hsub⟩ := (mem_ancestors full _ support).mp hsupport
    obtain ⟨target, hdecode⟩ := prepared_indexed_node_exists q full support hactive
    refine ⟨target, List.mem_toFinset.mpr ?_, hdecode⟩
    exact (prepared_ancestorChain_mem_iff q full hq hlaminar node target).mpr (hdecode.symm ▸ hsub)

def chainZero (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (node : cache.NodeId) : Bool :=
  (ancestorChain cache node).any (fun ancestor => decide (capacity.get ancestor = 0))

/-- Traverse the chain and perform one actual vector update per listed node. -/
def decrementNodes (cache : IndexedNodeCache Tool) :
    List cache.NodeId → IndexedCapacity cache → IndexedCapacity cache
  | [], capacity => capacity
  | node :: later, capacity =>
      decrementNodes cache later (capacity.set node.val (capacity.get node - 1) node.isLt)

def chainDecrement (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (node : cache.NodeId) : IndexedCapacity cache := decrementNodes cache (ancestorChain cache node) capacity

theorem decrementNodes_get (cache : IndexedNodeCache Tool) (nodes : List cache.NodeId)
    (hnodup : nodes.Nodup) (capacity : IndexedCapacity cache) (target : cache.NodeId) :
    (decrementNodes cache nodes capacity).get target =
      if target ∈ nodes then capacity.get target - 1 else capacity.get target := by
  induction nodes generalizing capacity with
  | nil => simp only [decrementNodes, List.not_mem_nil, ↓reduceIte]
  | cons node later ih =>
    rw [decrementNodes, ih (List.nodup_cons.mp hnodup).2]
    by_cases heq : target = node
    · subst target
      have hnot := (List.nodup_cons.mp hnodup).1
      simp only [hnot, ↓reduceIte, vector_set_get, List.mem_cons, true_or]
    · simp only [vector_set_get, heq, ↓reduceIte, List.mem_cons, false_or]

theorem prepared_chainZero_eq (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (node : (prepareNormalization q full).indexed.NodeId) :
    chainZero (prepareNormalization q full).indexed capacity node =
      IndexedEntry.zeroAncestor (prepareNormalization q full).indexed capacity
        ((prepareNormalization q full).indexed.decode node) := by
  rw [Bool.eq_iff_iff]
  simp only [chainZero, IndexedEntry.zeroAncestor, List.any_eq_true,
    decide_eq_true_eq, List.mem_finRange, true_and]
  constructor
  · rintro ⟨target, htarget, hzero⟩
    exact ⟨target, (prepared_ancestorChain_mem_iff q full hq hlaminar node target).mp htarget, hzero⟩
  · rintro ⟨target, hsub, hzero⟩
    exact ⟨target, (prepared_ancestorChain_mem_iff q full hq hlaminar node target).mpr hsub, hzero⟩

theorem prepared_chainDecrement_eq (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (node : (prepareNormalization q full).indexed.NodeId) :
    chainDecrement (prepareNormalization q full).indexed capacity node =
      IndexedEntry.ancestorDecrement (prepareNormalization q full).indexed capacity
        ((prepareNormalization q full).indexed.decode node) := by
  apply Vector.ext
  intro index hindex
  change (chainDecrement (prepareNormalization q full).indexed capacity node).get ⟨index, hindex⟩ =
    (IndexedEntry.ancestorDecrement (prepareNormalization q full).indexed capacity
      ((prepareNormalization q full).indexed.decode node)).get ⟨index, hindex⟩
  rw [chainDecrement, decrementNodes_get _ _ (prepared_ancestorChain_nodup q full hq hlaminar node),
    IndexedEntry.ancestorDecrement_get]
  simp only [prepared_ancestorChain_mem_iff q full hq hlaminar]

/-- The support lookup is done once; empty eligibility bypasses it directly. -/
def chainExtend [DecidableEq Tool] (cache : IndexedNodeCache Tool) (eligible : Finset Tool) :
    IndexedEntry.FixedEntry cache → IndexedEntry.FixedEntry cache
  | .void => .void
  | .vector capacity => if eligible = ∅ then .void else
      match findNodeId cache.nodes eligible with
      | none => .void
      | some node => if chainZero cache capacity node then .void else .vector (chainDecrement cache capacity node)

def chainCell [DecidableEq Tool] (cache : IndexedNodeCache Tool) (eligible : Finset Tool)
    (good bad : IndexedEntry.FixedEntry cache) : IndexedEntry.FixedEntry cache :=
  IndexedEntry.intersect cache good (chainExtend cache eligible bad)

def chainBudgetCell [DecidableEq Tool] (cache : IndexedNodeCache Tool) (eligible : Finset Tool)
    (budget : Nat) (good bad : IndexedEntry.FixedEntry cache) : IndexedEntry.FixedEntry cache :=
  if budget = 0 then IndexedEntry.free cache else chainCell cache eligible good bad

theorem prepared_chainExtend_eq (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) :
    chainExtend (prepareNormalization q full).indexed eligible entry =
      IndexedEntry.extend (prepareNormalization q full).indexed eligible entry := by
  cases entry with
  | void => rfl
  | vector capacity =>
    by_cases hempty : eligible = ∅
    · simp only [chainExtend, IndexedEntry.extend, hempty, ↓reduceIte]
    · obtain ⟨node, hdecode⟩ := prepared_indexed_node_exists q full eligible (heligible.resolve_left hempty)
      have hfind := (findNodeId_eq_some_iff _ (prepared_indexed_nodes_nodup q full) eligible node).mpr hdecode
      simp only [chainExtend, IndexedEntry.extend, hempty, ↓reduceIte, hfind]
      rw [prepared_chainZero_eq q full hq hlaminar, prepared_chainDecrement_eq q full hq hlaminar, hdecode]

theorem prepared_chainCell_eq (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) :
    chainCell (prepareNormalization q full).indexed eligible good bad =
      IndexedEntry.cell (prepareNormalization q full).indexed eligible good bad := by
  rw [chainCell, prepared_chainExtend_eq q full hq hlaminar eligible heligible]
  rfl

theorem prepared_chainBudgetCell_eq (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full) (budget : Nat)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) :
    chainBudgetCell (prepareNormalization q full).indexed eligible budget good bad =
      IndexedEntry.budgetCell (prepareNormalization q full).indexed eligible budget good bad := by
  simp only [chainBudgetCell, IndexedEntry.budgetCell,
    prepared_chainCell_eq q full hq hlaminar eligible heligible]

theorem prepared_chainExtend_denote (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hnormalized : IndexedEntry.IsNormalized (prepareNormalization q full).indexed entry) :
    (chainExtend (prepareNormalization q full).indexed eligible entry).denote (prepareNormalization q full).indexed =
      usedExtension eligible (entry.denote (prepareNormalization q full).indexed) := by
  rw [prepared_chainExtend_eq q full hq hlaminar eligible heligible]
  exact IndexedEntry.prepared_extend_denote q full hq hlaminar eligible heligible entry hnormalized

theorem prepared_chainCell_denote (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hbad : IndexedEntry.IsNormalized (prepareNormalization q full).indexed bad) :
    (chainCell (prepareNormalization q full).indexed eligible good bad).denote (prepareNormalization q full).indexed =
      good.denote (prepareNormalization q full).indexed ∩
        usedExtension eligible (bad.denote (prepareNormalization q full).indexed) := by
  rw [prepared_chainCell_eq q full hq hlaminar eligible heligible]
  exact IndexedEntry.prepared_cell_denote q full hq hlaminar eligible heligible good bad hbad

theorem prepared_chainCell_normalized_bounded (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hgood : IndexedEntry.IsNormalized (prepareNormalization q full).indexed good) :
    IndexedEntry.IsNormalized (prepareNormalization q full).indexed
      (chainCell (prepareNormalization q full).indexed eligible good bad) ∧
        (chainCell (prepareNormalization q full).indexed eligible good bad).Bounded q := by
  rw [prepared_chainCell_eq q full hq hlaminar eligible heligible]
  exact IndexedEntry.prepared_cell_normalized_bounded q full hq hlaminar eligible good bad hgood

theorem chainExtend_empty [DecidableEq Tool] (cache : IndexedNodeCache Tool) (entry : IndexedEntry.FixedEntry cache) :
    chainExtend cache ∅ entry = .void := by
  cases entry <;> simp only [chainExtend, ↓reduceIte]

theorem chainCell_empty [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (good bad : IndexedEntry.FixedEntry cache) : chainCell cache ∅ good bad = .void := by
  rw [chainCell, chainExtend_empty]
  cases good <;> rfl

theorem chainBudgetCell_zero [DecidableEq Tool] (cache : IndexedNodeCache Tool) (eligible : Finset Tool)
    (good bad : IndexedEntry.FixedEntry cache) : chainBudgetCell cache eligible 0 good bad = IndexedEntry.free cache := rfl

theorem chainBudgetCell_zero_tools (cache : IndexedNodeCache (Fin 0)) (eligible : Finset (Fin 0)) (budget : Nat)
    (good bad : IndexedEntry.FixedEntry cache) : chainBudgetCell cache eligible (budget + 1) good bad = .void := by
  have hempty : eligible = ∅ := Finset.eq_empty_of_forall_notMem (fun tool => Fin.elim0 tool)
  rw [chainBudgetCell, ite_eq_right (Nat.succ_ne_zero budget), hempty, chainCell_empty]

end PaperProofs.Structure.LaminarTree.IndexedAncestors
