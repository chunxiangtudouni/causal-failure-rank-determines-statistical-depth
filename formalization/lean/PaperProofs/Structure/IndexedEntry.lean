module

public import PaperProofs.Structure.CapacityBits
public import PaperProofs.Structure.IndexedRAM
import Lean.Elab.Tactic.Omega

/-!
Fixed-coordinate entries for one real full-input tree. Operations
are actual finite vector algorithms: ancestor-coordinate tests/decrements,
an explicit zero-ancestor/empty/VOID branch, coordinate minima and the proved
indexed normalization pass. Set-family refinement is proved separately.
Ancestor tests currently use support containment; no O(t) decrement or packed
random-access cost is asserted. The existing zero-tool table is unchanged.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedEntry

variable {Tool : Type*}

abbrev FixedEntry (cache : IndexedNodeCache Tool) := CapacityBits.Entry cache.nodes.size

def reifyCapacity (cache : IndexedNodeCache Tool) (capacity : Finset Tool → Nat) : IndexedCapacity cache :=
  Vector.ofFn (fun node => capacity (cache.decode node))

theorem reifyCapacity_get (cache : IndexedNodeCache Tool) (capacity : Finset Tool → Nat) (node : cache.NodeId) :
    (reifyCapacity cache capacity).get node = capacity (cache.decode node) := cache_get_ofFn _ _

def reify (cache : IndexedNodeCache Tool) : CapacityEntry (Finset Tool) → FixedEntry cache
  | .void => .void
  | .vector capacity => .vector (reifyCapacity cache capacity)

def toSupportEntry [DecidableEq Tool] (cache : IndexedNodeCache Tool) :
    FixedEntry cache → CapacityEntry (Finset Tool)
  | .void => .void
  | .vector capacity => .vector (cache.unindexCapacity capacity)

def IsNormalized (cache : IndexedNodeCache Tool) : FixedEntry cache → Prop
  | .void => True
  | .vector capacity => IndexedNormalized cache capacity

def free (cache : IndexedNodeCache Tool) : FixedEntry cache := .vector (reifyCapacity cache Finset.card)

def ancestorDecrement [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (capacity : IndexedCapacity cache) (eligible : Finset Tool) : IndexedCapacity cache :=
  Vector.ofFn (fun node => if eligible ⊆ cache.decode node then capacity.get node - 1 else capacity.get node)

def zeroAncestor [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (capacity : IndexedCapacity cache) (eligible : Finset Tool) : Bool :=
  (List.finRange cache.nodes.size).any (fun node => decide (eligible ⊆ cache.decode node ∧ capacity.get node = 0))

def extend [DecidableEq Tool] (cache : IndexedNodeCache Tool) (eligible : Finset Tool) : FixedEntry cache → FixedEntry cache
  | .void => .void
  | .vector capacity => if eligible = ∅ then .void else
      if zeroAncestor cache capacity eligible then .void else .vector (ancestorDecrement cache capacity eligible)

def coordinateMin (cache : IndexedNodeCache Tool) : FixedEntry cache → FixedEntry cache → FixedEntry cache
  | .void, _ => .void
  | _, .void => .void
  | .vector left, .vector right => .vector (Vector.ofFn (fun node => min (left.get node) (right.get node)))

def normalize (cache : IndexedNodeCache Tool) : FixedEntry cache → FixedEntry cache
  | .void => .void
  | .vector capacity => .vector (cache.normalize capacity)

def intersect (cache : IndexedNodeCache Tool) (left right : FixedEntry cache) : FixedEntry cache :=
  normalize cache (coordinateMin cache left right)

def cell [DecidableEq Tool] (cache : IndexedNodeCache Tool) (eligible : Finset Tool)
    (good bad : FixedEntry cache) : FixedEntry cache := intersect cache good (extend cache eligible bad)

def budgetCell [DecidableEq Tool] (cache : IndexedNodeCache Tool) (eligible : Finset Tool) (budget : Nat)
    (good bad : FixedEntry cache) : FixedEntry cache := if budget = 0 then free cache else cell cache eligible good bad

theorem family_of_active_eq [DecidableEq Tool] [Fintype Tool] (full : List (Finset Tool))
    (left right : Finset Tool → Nat) (heq : ∀ node ∈ nodeFamily full, left node = right node) :
    Structure.capacityFamily (layout full) left = Structure.capacityFamily (layout full) right := by
  ext used
  constructor
  · intro hused node hnode
    rw [← heq node hnode]
    exact hused node hnode
  · intro hused node hnode
    rw [heq node hnode]
    exact hused node hnode

theorem normalized_of_active_eq [DecidableEq Tool] [Fintype Tool] (full : List (Finset Tool))
    (left right : Finset Tool → Nat) (heq : ∀ node ∈ nodeFamily full, left node = right node)
    (hnormalized : Normalized full left) : Normalized full right := by
  refine ⟨fun tool => ?_, ?_⟩
  · rw [← heq {tool} (singleton_mem full tool)]
    exact hnormalized.1 tool
  · intro node hnode hinternal
    rw [← heq node hnode]
    have hsum : (∑ child ∈ children (nodeFamily full) node, right child) =
        ∑ child ∈ children (nodeFamily full) node, left child :=
      Finset.sum_congr rfl (fun child hchild => (heq child (children_subset _ _ hchild)).symm)
    rw [hsum]
    exact hnormalized.2 node hnode hinternal

theorem prepared_reify_active (q : Nat) (full : List (Finset (Fin q))) (capacity : Finset (Fin q) → Nat)
    (node : Finset (Fin q)) (hnode : node ∈ nodeFamily full) :
    (prepareNormalization q full).indexed.unindexCapacity
      (reifyCapacity (prepareNormalization q full).indexed capacity) node = capacity node := by
  obtain ⟨index, hdecode⟩ := prepared_indexed_node_exists q full node hnode
  rw [← hdecode, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full), reifyCapacity_get]

theorem prepared_toSupport_denote (q : Nat) (full : List (Finset (Fin q)))
    (entry : FixedEntry (prepareNormalization q full).indexed) :
    entry.denote (prepareNormalization q full).indexed =
      (toSupportEntry (prepareNormalization q full).indexed entry).denote (layout full) := by
  cases entry with
  | void => rfl
  | vector capacity => exact prepared_indexed_family_eq q full capacity

theorem prepared_reify_denote (q : Nat) (full : List (Finset (Fin q)))
    (entry : CapacityEntry (Finset (Fin q))) :
    (reify (prepareNormalization q full).indexed entry).denote (prepareNormalization q full).indexed =
      entry.denote (layout full) := by
  cases entry with
  | void => rfl
  | vector capacity =>
    exact (prepared_indexed_family_eq q full _).trans
      (family_of_active_eq full _ _ (prepared_reify_active q full capacity))

theorem prepared_normalized_from_original (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hnormalized : Normalized full ((prepareNormalization q full).indexed.unindexCapacity capacity)) :
    IndexedNormalized (prepareNormalization q full).indexed capacity := by
  refine ⟨fun node hsingle => ?_, ?_⟩
  · obtain ⟨tool, hsingleton⟩ := Finset.card_eq_one.mp hsingle
    have hbound := hnormalized.1 tool
    rw [← hsingleton, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)] at hbound
    exact hbound
  · intro node hinternal
    have hbound := hnormalized.2 _ (prepared_indexed_node_mem q full node) hinternal
    rw [unindexCapacity_at _ (prepared_indexed_nodes_nodup q full),
      ← prepared_indexed_childSum_eq_original q full hq hlaminar capacity node] at hbound
    exact hbound

theorem prepared_reify_normalized (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (entry : CapacityEntry (Finset (Fin q)))
    (hnormalized : EntryNormalized full entry) : IsNormalized (prepareNormalization q full).indexed
      (reify (prepareNormalization q full).indexed entry) := by
  cases entry with
  | void => trivial
  | vector capacity =>
    apply prepared_normalized_from_original q full hq hlaminar
    exact normalized_of_active_eq full capacity _
      (fun node hnode => (prepared_reify_active q full capacity node hnode).symm) hnormalized

theorem prepared_normalized_bounded (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (entry : FixedEntry (prepareNormalization q full).indexed)
    (hnormalized : IsNormalized (prepareNormalization q full).indexed entry) : entry.Bounded q := by
  cases entry with
  | void => trivial
  | vector capacity =>
    intro node
    let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
    have hnormOld := prepared_indexed_normalized_to_original q full hq hlaminar capacity hnormalized
    have hbound := normalized_capacity_le_toolCount full hlaminar _ hnormOld (prepared_indexed_node_mem q full node)
    rw [unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)] at hbound
    simpa only [Fintype.card_fin] using hbound

theorem ancestorDecrement_get [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (capacity : IndexedCapacity cache) (eligible : Finset Tool) (node : cache.NodeId) :
    (ancestorDecrement cache capacity eligible).get node =
      if eligible ⊆ cache.decode node then capacity.get node - 1 else capacity.get node := cache_get_ofFn _ _

theorem prepared_zeroAncestor_iff (q : Nat) (full : List (Finset (Fin q)))
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) (eligible : Finset (Fin q)) :
    zeroAncestor (prepareNormalization q full).indexed capacity eligible = true ↔
      HasZeroAncestor full ((prepareNormalization q full).indexed.unindexCapacity capacity) eligible := by
  rw [zeroAncestor, List.any_eq_true]
  constructor
  · rintro ⟨node, _, hfields⟩
    have hfields : eligible ⊆ (prepareNormalization q full).indexed.decode node ∧ capacity.get node = 0 := by
      simpa only [decide_eq_true_eq] using hfields
    refine ⟨_, (mem_ancestors full eligible _).mpr ⟨prepared_indexed_node_mem q full node, hfields.1⟩, ?_⟩
    rw [unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)]
    exact hfields.2
  · rintro ⟨support, hancestor, hzero⟩
    obtain ⟨hactive, hcontains⟩ := (mem_ancestors full eligible support).mp hancestor
    obtain ⟨node, hdecode⟩ := prepared_indexed_node_exists q full support hactive
    refine ⟨node, List.mem_finRange _, ?_⟩
    apply decide_eq_true_eq.mpr
    refine ⟨hdecode.symm ▸ hcontains, ?_⟩
    rw [← hdecode, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)] at hzero
    exact hzero

theorem prepared_noZeroAncestor_iff (q : Nat) (full : List (Finset (Fin q)))
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) (eligible : Finset (Fin q)) :
    zeroAncestor (prepareNormalization q full).indexed capacity eligible = false ↔
      ¬ HasZeroAncestor full ((prepareNormalization q full).indexed.unindexCapacity capacity) eligible := by
  rw [Bool.eq_false_iff]
  exact not_congr (prepared_zeroAncestor_iff q full capacity eligible)

theorem prepared_ancestorDecrement_active (q : Nat) (full : List (Finset (Fin q)))
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) (eligible node : Finset (Fin q))
    (hnode : node ∈ nodeFamily full) :
    (prepareNormalization q full).indexed.unindexCapacity
      (ancestorDecrement (prepareNormalization q full).indexed capacity eligible) node =
        decrementAlong eligible ((prepareNormalization q full).indexed.unindexCapacity capacity) node := by
  obtain ⟨index, hdecode⟩ := prepared_indexed_node_exists q full node hnode
  rw [← hdecode, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full), ancestorDecrement_get]
  simp only [decrementAlong, unindexCapacity_at _ (prepared_indexed_nodes_nodup q full)]

theorem prepared_ancestorDecrement_normalized (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hnormalized : IndexedNormalized (prepareNormalization q full).indexed capacity)
    (eligible : Finset (Fin q)) (heligible : eligible ∈ nodeFamily full)
    (hzero : zeroAncestor (prepareNormalization q full).indexed capacity eligible = false) :
    IndexedNormalized (prepareNormalization q full).indexed
      (ancestorDecrement (prepareNormalization q full).indexed capacity eligible) := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hnoOld := (prepared_noZeroAncestor_iff q full capacity eligible).mp hzero
  have hnormOld := prepared_indexed_normalized_to_original q full hq hlaminar capacity hnormalized
  have hdecrement := decrementAlong_normalized full hlaminar _ hnormOld heligible hnoOld
  apply prepared_normalized_from_original q full hq hlaminar
  exact normalized_of_active_eq full _ _
    (fun node hnode => (prepared_ancestorDecrement_active q full capacity eligible node hnode).symm) hdecrement

theorem coordinateMin_toCapacityEntry (cache : IndexedNodeCache Tool) (left right : FixedEntry cache) :
    (coordinateMin cache left right).toCapacityEntry = left.toCapacityEntry.intersection right.toCapacityEntry := by
  cases left with
  | void => rfl
  | vector left =>
    cases right with
    | void => rfl
    | vector right =>
      apply congrArg CapacityEntry.vector
      funext node
      exact cache_get_ofFn _ _

theorem coordinateMin_denote [DecidableEq Tool] (cache : IndexedNodeCache Tool) (left right : FixedEntry cache) :
    (coordinateMin cache left right).denote cache = left.denote cache ∩ right.denote cache := by
  rw [CapacityBits.Entry.denote, coordinateMin_toCapacityEntry, CapacityEntry.denote_intersection]
  rfl

theorem prepared_normalize_denote (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (entry : FixedEntry (prepareNormalization q full).indexed) :
    (normalize (prepareNormalization q full).indexed entry).denote (prepareNormalization q full).indexed =
      entry.denote (prepareNormalization q full).indexed := by
  cases entry with
  | void => rfl
  | vector capacity => exact prepared_indexed_normalizeAlong_preserves q full hq hlaminar _ capacity

theorem prepared_intersect_denote (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (left right : FixedEntry (prepareNormalization q full).indexed) :
    (intersect (prepareNormalization q full).indexed left right).denote (prepareNormalization q full).indexed =
      left.denote (prepareNormalization q full).indexed ∩ right.denote (prepareNormalization q full).indexed := by
  rw [intersect, prepared_normalize_denote q full hq hlaminar, coordinateMin_denote]

theorem prepared_intersect_normalized (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (left right : FixedEntry (prepareNormalization q full).indexed)
    (hleft : IsNormalized (prepareNormalization q full).indexed left) :
    IsNormalized (prepareNormalization q full).indexed (intersect (prepareNormalization q full).indexed left right) := by
  cases left with
  | void => trivial
  | vector left =>
    cases right with
    | void => trivial
    | vector right =>
      apply prepared_indexed_normalize_normalized q full hq hlaminar
      intro node hsingle
      have hget : (Vector.ofFn (fun node => min (left.get node) (right.get node))).get node =
          min (left.get node) (right.get node) := cache_get_ofFn _ _
      rw [hget]
      exact (min_le_left _ _).trans (hleft.1 node hsingle)

theorem prepared_extend_denote (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (entry : FixedEntry (prepareNormalization q full).indexed)
    (hnormalized : IsNormalized (prepareNormalization q full).indexed entry) :
    (extend (prepareNormalization q full).indexed eligible entry).denote (prepareNormalization q full).indexed =
      usedExtension eligible (entry.denote (prepareNormalization q full).indexed) := by
  cases entry with
  | void => simp [extend, CapacityBits.Entry.denote, CapacityBits.Entry.toCapacityEntry, CapacityEntry.denote, extension_void]
  | vector capacity =>
    have hnormOld := prepared_indexed_normalized_to_original q full hq hlaminar capacity hnormalized
    by_cases hempty : eligible = ∅
    · subst eligible
      simp [extend, CapacityBits.Entry.denote, CapacityBits.Entry.toCapacityEntry, CapacityEntry.denote, extension_empty]
    · by_cases hzero : zeroAncestor (prepareNormalization q full).indexed capacity eligible = true
      · have hzeroOld := (prepared_zeroAncestor_iff q full capacity eligible).mp hzero
        simp only [extend, hempty, hzero, ↓reduceIte, CapacityBits.Entry.denote,
          CapacityBits.Entry.toCapacityEntry, CapacityEntry.denote]
        change ∅ = usedExtension eligible ((prepareNormalization q full).indexed.capacityFamily capacity)
        rw [prepared_indexed_family_eq]
        exact (usedExtension_eq_empty_of_zeroAncestor full _ eligible hzeroOld).symm
      · have hnoOld : ¬ HasZeroAncestor full ((prepareNormalization q full).indexed.unindexCapacity capacity) eligible :=
          fun h => hzero ((prepared_zeroAncestor_iff q full capacity eligible).mpr h)
        simp only [extend, hempty, hzero, ↓reduceIte]
        change (prepareNormalization q full).indexed.capacityFamily
          (ancestorDecrement (prepareNormalization q full).indexed capacity eligible) =
          usedExtension eligible ((prepareNormalization q full).indexed.capacityFamily capacity)
        rw [prepared_indexed_family_eq, prepared_indexed_family_eq]
        exact (family_of_active_eq full _ _ (prepared_ancestorDecrement_active q full capacity eligible)).trans
          (decremented_family_eq_extension full hlaminar _ hnormOld eligible (heligible.resolve_left hempty)
            (Finset.nonempty_iff_ne_empty.mpr hempty) hnoOld)

theorem prepared_extend_normalized (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (entry : FixedEntry (prepareNormalization q full).indexed)
    (hnormalized : IsNormalized (prepareNormalization q full).indexed entry) :
    IsNormalized (prepareNormalization q full).indexed (extend (prepareNormalization q full).indexed eligible entry) := by
  cases entry with
  | void => trivial
  | vector capacity =>
    by_cases hempty : eligible = ∅
    · simp only [extend, hempty, ↓reduceIte, IsNormalized]
    · by_cases hzero : zeroAncestor (prepareNormalization q full).indexed capacity eligible = true
      · simp only [extend, hempty, hzero, ↓reduceIte, IsNormalized]
      · simp only [extend, hempty, hzero, ↓reduceIte, IsNormalized]
        exact prepared_ancestorDecrement_normalized q full hq hlaminar capacity hnormalized eligible
          (heligible.resolve_left hempty) (Bool.eq_false_iff.mpr hzero)

theorem prepared_cell_denote (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (good bad : FixedEntry (prepareNormalization q full).indexed)
    (hbad : IsNormalized (prepareNormalization q full).indexed bad) :
    (cell (prepareNormalization q full).indexed eligible good bad).denote (prepareNormalization q full).indexed =
      good.denote (prepareNormalization q full).indexed ∩
        usedExtension eligible (bad.denote (prepareNormalization q full).indexed) := by
  rw [cell, prepared_intersect_denote q full hq hlaminar,
    prepared_extend_denote q full hq hlaminar eligible heligible bad hbad]

theorem prepared_cell_normalized_bounded (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (good bad : FixedEntry (prepareNormalization q full).indexed)
    (hgood : IsNormalized (prepareNormalization q full).indexed good) :
    IsNormalized (prepareNormalization q full).indexed (cell (prepareNormalization q full).indexed eligible good bad) ∧
      (cell (prepareNormalization q full).indexed eligible good bad).Bounded q := by
  have hnormalized := prepared_intersect_normalized q full hq hlaminar good
    (extend (prepareNormalization q full).indexed eligible bad) hgood
  exact ⟨hnormalized, prepared_normalized_bounded q full hq hlaminar _ hnormalized⟩

theorem prepared_reify_cell_refines (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (good bad : CapacityEntry (Finset (Fin q)))
    (hgood : EntryNormalized full good) (hbad : EntryNormalized full bad) :
    let cache := (prepareNormalization q full).indexed
    let result := cell cache eligible (reify cache good) (reify cache bad)
    result.denote cache = ((prepareNormalization q full).intersectEntries good (extendEntry full eligible bad)).denote (layout full) ∧
      IsNormalized cache result ∧ result.Bounded q := by
  have hgoodIndexed := prepared_reify_normalized q full hq hlaminar good hgood
  have hbadIndexed := prepared_reify_normalized q full hq hlaminar bad hbad
  refine ⟨?_, prepared_cell_normalized_bounded q full hq hlaminar eligible _ _ hgoodIndexed⟩
  rw [prepared_cell_denote q full hq hlaminar eligible heligible _ _ hbadIndexed,
    prepared_reify_denote, prepared_reify_denote, prepared_intersectEntries_sound q full hq hlaminar,
    extendEntry_sound full hlaminar eligible heligible bad hbad]

theorem extend_empty [DecidableEq Tool] (cache : IndexedNodeCache Tool) (entry : FixedEntry cache) :
    extend cache ∅ entry = .void := by
  cases entry <;> simp only [extend, ↓reduceIte]

theorem cell_empty [DecidableEq Tool] (cache : IndexedNodeCache Tool) (good bad : FixedEntry cache) :
    cell cache ∅ good bad = .void := by
  rw [cell, extend_empty]
  cases good <;> rfl

theorem cell_zero_tools (cache : IndexedNodeCache (Fin 0)) (eligible : Finset (Fin 0))
    (good bad : FixedEntry cache) : cell cache eligible good bad = .void := by
  have hempty : eligible = ∅ := Finset.eq_empty_of_forall_notMem (fun tool => Fin.elim0 tool)
  rw [hempty]
  exact cell_empty cache good bad

theorem budgetCell_zero [DecidableEq Tool] (cache : IndexedNodeCache Tool) (eligible : Finset Tool)
    (good bad : FixedEntry cache) : budgetCell cache eligible 0 good bad = free cache := rfl

theorem budgetCell_zero_tools (cache : IndexedNodeCache (Fin 0)) (eligible : Finset (Fin 0)) (budget : Nat)
    (good bad : FixedEntry cache) : budgetCell cache eligible (budget + 1) good bad = .void := by
  rw [budgetCell, ite_eq_right (Nat.succ_ne_zero budget), cell_zero_tools]

theorem free_denote [DecidableEq Tool] (cache : IndexedNodeCache Tool) :
    (free cache).denote cache = Set.univ := by
  change Structure.capacityFamily cache.capacityLayout (reifyCapacity cache Finset.card).get = Set.univ
  have heq : (reifyCapacity cache Finset.card).get = fun node => (cache.capacityLayout.support node).card := by
    funext node
    exact reifyCapacity_get cache Finset.card node
  rw [heq]
  exact capacityFamily_free cache.capacityLayout

theorem free_bounded (q : Nat) (cache : IndexedNodeCache (Fin q)) : (free cache).Bounded q := by
  intro node
  rw [reifyCapacity_get]
  exact (Finset.card_le_univ _).trans (Fintype.card_fin q).le

/-!
The following implementation runs only the normalization phase on the existing
RAM machine. The raw entry is computed by the explicit finite ancestor and
coordinate operations above. Their RAM costs are not included in the pass
trace. ROM/program compilation can be shared: the compiled object is a
parameter of the executable cell operation, not reconstructed by it.
-/

def heapCapacity (cache : IndexedNodeCache Tool) (heap : Nat → Nat) : IndexedCapacity cache :=
  Vector.ofFn (fun node => heap node.val)

theorem heapCapacity_eq (cache : IndexedNodeCache Tool) (heap : Nat → Nat)
    (capacity : IndexedCapacity cache) (hagrees : IndexedRAM.HeapAgrees heap capacity) :
    heapCapacity cache heap = capacity := by
  apply Vector.ext
  intro index hindex
  change (heapCapacity cache heap).get ⟨index, hindex⟩ = capacity.get ⟨index, hindex⟩
  rw [heapCapacity, cache_get_ofFn]
  exact hagrees ⟨index, hindex⟩

def ramNormalize (cache : IndexedNodeCache Tool) (compiled : IndexedRAM.CompiledNormalizer cache)
    (entry : FixedEntry cache) (initial : IndexedRAM.State) : FixedEntry cache :=
  match entry with
  | .void => .void
  | .vector capacity => .vector (heapCapacity cache (compiled.run capacity initial).heap)

def ramCell [DecidableEq Tool] (cache : IndexedNodeCache Tool) (compiled : IndexedRAM.CompiledNormalizer cache)
    (eligible : Finset Tool) (good bad : FixedEntry cache) (initial : IndexedRAM.State) : FixedEntry cache :=
  ramNormalize cache compiled (coordinateMin cache good (extend cache eligible bad)) initial

theorem ramNormalize_refines [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (entry : FixedEntry cache) (initial : IndexedRAM.State) :
    ramNormalize cache (IndexedRAM.compileNormalizer cache) entry initial = normalize cache entry := by
  cases entry with
  | void => rfl
  | vector capacity =>
    exact congrArg CapacityBits.Entry.vector
      (heapCapacity_eq cache _ _ (IndexedRAM.compiledNormalizer_run_refines cache capacity initial))

theorem ramCell_refines [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (eligible : Finset Tool) (good bad : FixedEntry cache) (initial : IndexedRAM.State) :
    ramCell cache (IndexedRAM.compileNormalizer cache) eligible good bad initial = cell cache eligible good bad :=
  ramNormalize_refines cache _ initial

theorem prepared_ramCell_refines (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (good bad : CapacityEntry (Finset (Fin q)))
    (hgood : EntryNormalized full good) (hbad : EntryNormalized full bad) (initial : IndexedRAM.State) :
    let cache := (prepareNormalization q full).indexed
    let result := ramCell cache (IndexedRAM.compileNormalizer cache) eligible (reify cache good) (reify cache bad) initial
    result.denote cache = ((prepareNormalization q full).intersectEntries good (extendEntry full eligible bad)).denote (layout full) ∧
      IsNormalized cache result ∧ result.Bounded q := by
  dsimp only
  rw [ramCell_refines]
  exact prepared_reify_cell_refines q full hq hlaminar eligible heligible good bad hgood hbad

theorem prepared_cell_normalization_phase_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (good bad : FixedEntry (prepareNormalization q full).indexed)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hraw : coordinateMin (prepareNormalization q full).indexed good
      (extend (prepareNormalization q full).indexed eligible bad) = .vector capacity)
    (initial : IndexedRAM.State) (hpc : initial.pc = 0) :
    ∃ final trace,
      IndexedRAM.HaltingRuns
        ((IndexedRAM.treeROM (prepareNormalization q full).indexed).withInput capacity)
        (IndexedRAM.normalizationProgram (prepareNormalization q full).indexed) initial final trace ∧
      CapacityBits.Entry.vector (heapCapacity (prepareNormalization q full).indexed final.heap) =
        cell (prepareNormalization q full).indexed eligible good bad ∧
      trace.length ≤ 176 * (prepareNormalization q full).indexed.nodes.size := by
  obtain ⟨final, trace, hrun, hagrees, hlength⟩ :=
    IndexedRAM.prepared_haltingNormalization_run q full hq hlaminar capacity initial hpc
  refine ⟨final, trace, hrun, ?_, hlength⟩
  rw [heapCapacity_eq _ _ _ hagrees]
  change CapacityBits.Entry.vector ((prepareNormalization q full).indexed.normalize capacity) =
    normalize (prepareNormalization q full).indexed
      (coordinateMin (prepareNormalization q full).indexed good
        (extend (prepareNormalization q full).indexed eligible bad))
  rw [hraw]
  rfl

theorem ramCell_zero_tools (cache : IndexedNodeCache (Fin 0))
    (compiled : IndexedRAM.CompiledNormalizer cache) (eligible : Finset (Fin 0))
    (good bad : FixedEntry cache) (initial : IndexedRAM.State) :
    ramCell cache compiled eligible good bad initial = .void := by
  have hempty : eligible = ∅ := Finset.eq_empty_of_forall_notMem (fun tool => Fin.elim0 tool)
  rw [ramCell, hempty, extend_empty]
  cases good <;> rfl

end PaperProofs.Structure.LaminarTree.IndexedEntry
