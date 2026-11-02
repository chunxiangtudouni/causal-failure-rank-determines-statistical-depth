module

public import PaperProofs.Structure.UniformNormalizationRAM
public import PaperProofs.Structure.UniformFreeTableSafety
import Mathlib.Tactic.IntervalCases

/-! Every actual instruction prefix of the runtime parent-push normalizer.
The accumulator sentinel is controlled by the unique root of the prepared
tree. Initial accumulator contents may be arbitrary for the post-clear node
loop. Full CapacityThroughout includes clock zero and therefore consumes the
caller's original leading-word bound, including initial accumulator words. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17NormalizationSafety004

open IndexedRAM IndexedClosureRAM AlgorithmClaims UniformNormalizationRAM

variable {Tool : Type*}

theorem bounded_update (q words : Nat) (heap : Nat → Nat)
    (hbound : CapacityPrefixBounded q words heap) (address value : Nat) (hv : value ≤ q) :
    CapacityPrefixBounded q words (Function.update heap address value) := by
  intro target ht
  by_cases he : target = address
  · rw [he, Function.update_self]
    exact hv
  · rw [Function.update_of_ne he]
    exact hbound target ht

theorem clearBlock_capacityThroughout (q words address : Nat) (rom : PhysicalROM)
    (state : State) (hbound : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (clearBlock address) state := by
  intro count hc
  change count ≤ 3 at hc
  interval_cases count <;> first
    | exact hbound
    | exact bounded_update q words state.heap hbound address 0 (Nat.zero_le q)

theorem clearIndices_capacityThroughout (q words base : Nat) (rom : PhysicalROM)
    (indices : List Nat) (state : State) (hbound : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (indices.flatMap (fun index => clearBlock (base + index))) state := by
  induction indices generalizing state with
  | nil => intro count hc; simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hbound
  | cons head later ih =>
    rw [List.flatMap_cons]
    have hh := clearBlock_capacityThroughout q words (base + head) rom state hbound
    apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hh
    apply ih
    simpa only [List.take_length] using hh _ le_rfl

theorem clearWords_bounded (q words base size : Nat) (rom : ROM) (state : State)
    (hbound : ∀ address < words, (∀ index ≤ size, address ≠ base + index) → state.heap address ≤ q) :
    CapacityPrefixBounded q words (execute rom (clearWords base (size + 1)) state).heap := by
  intro address ha
  by_cases hin : ∃ index ≤ size, address = base + index
  · obtain ⟨index, hi, rfl⟩ := hin
    rw [clearWords, clearIndices_value rom base (List.range (size + 1)) state index
      (List.mem_range.mpr (by omega))]
    exact Nat.zero_le q
  · rw [clearWords, clearIndices_frame rom base (List.range (size + 1)) state address (by
      intro index hi he
      exact hin ⟨index, by have := List.mem_range.mp hi; omega, he⟩)]
    apply hbound address ha
    intro index hi he
    exact hin ⟨index, hi, he⟩

theorem updateNode_capacityThroughout (q words size cap acc node : Nat) (rom : PhysicalROM)
    (state : State) (hbound : CapacityPrefixBounded q words state.heap)
    (hv : updatedValue rom.semantic size cap acc node state ≤ q) :
    CapacityThroughout q words rom (updateNode size cap acc node) state := by
  intro count hc
  change count ≤ 9 at hc
  have hh := bounded_update q words state.heap hbound (cap + node)
    (updatedValue rom.semantic size cap acc node state) hv
  interval_cases count <;> first | exact hbound | exact hh

theorem pushParent_capacityThroughout (q words acc node : Nat) (rom : PhysicalROM)
    (state : State) (hbound : CapacityPrefixBounded q words state.heap)
    (hv : state.heap (acc + rom.semantic.read .internal node) + state.register .fresh ≤ q) :
    CapacityThroughout q words rom (pushParent acc node) state := by
  intro count hc
  change count ≤ 7 at hc
  have hh := bounded_update q words state.heap hbound (acc + rom.semantic.read .internal node)
    (state.heap (acc + rom.semantic.read .internal node) + state.register .fresh) hv
  interval_cases count <;> first | exact hbound | exact hh

theorem partialChildSum_le_childSum (cache : IndexedNodeCache Tool)
    (capacity : IndexedCapacity cache) (count : Nat) (parent : cache.NodeId)
    (hnodup : (cache.children.get parent).toList.Nodup) :
    partialChildSum cache capacity count parent ≤ cache.childSum capacity parent := by
  rw [partialChildSum, childSum_eq_finset cache capacity parent hnodup]
  apply Finset.sum_le_sum
  intro child hc
  split_ifs <;> omega

def RootRep (cache : IndexedNodeCache Tool) (root : cache.NodeId) (acc count : Nat)
    (capacity : IndexedCapacity cache) (state : State) : Prop :=
  state.heap acc = if root.val < count then capacity.get root else 0

theorem updatedValue_eq_normalizeStep (cache : IndexedNodeCache Tool) (rom : ROM)
    (hrom : TreeROMFor cache rom) (cap acc : Nat) (capacity : IndexedCapacity cache)
    (state : State) (node : cache.NodeId)
    (hnodup : (cache.children.get node).toList.Nodup)
    (horder : ∀ child ∈ (cache.children.get node).toList, child.val < node.val)
    (hrep : Represents cache cap acc node.val capacity state) :
    updatedValue rom cache.nodes.size cap acc node.val state =
      (cache.normalizeStep capacity node).get node := by
  rw [updatedValue, hrep.1 node, hrep.2 node,
    partialChildSum_full cache capacity node hnodup horder, indexed_normalizeStep_get]
  by_cases hi : 1 < (cache.decode node).card
  · simp only [(hrom.2 node).mpr hi, hi, and_self, ite_false, ite_true]
  · have hz : rom.read .internal (cache.nodes.size + node.val) = 0 :=
      not_ne_iff.mp (fun h => hi ((hrom.2 node).mp h))
    simp only [hz, hi, false_and, ite_true, ite_false]

theorem nodeBlock_rootRep (cache : IndexedNodeCache Tool) (rom : ROM)
    (hrom : TreeROMFor cache rom) (cap acc : Nat)
    (hdisjoint : Disjoint cache.nodes.size cap acc) (root : cache.NodeId)
    (hroot : ∀ child : cache.NodeId, cache.parents.get child = none ↔ child = root)
    (capacity : IndexedCapacity cache) (state : State) (node : cache.NodeId)
    (hvalue : updatedValue rom cache.nodes.size cap acc node.val state =
      (cache.normalizeStep capacity node).get node)
    (hrep : RootRep cache root acc node.val capacity state) :
    RootRep cache root acc (node.val + 1) (cache.normalizeStep capacity node)
      (execute rom (nodeBlock cache.nodes.size cap acc node.val) state) := by
  have hcap : acc ≠ cap + node.val := (hdisjoint node.val node.isLt 0 (by omega)).symm
  by_cases he : node = root
  · subst node
    have hp := (hroot root).mpr rfl
    have hz : state.heap acc = 0 := by simpa only [RootRep, lt_self_iff_false, ite_false] using hrep
    unfold RootRep
    rw [execute_nodeBlock_heap, hrom.1 root, hp]
    simp only [encodedNode, Nat.add_zero, Function.update_self, Function.update_of_ne hcap,
      hz, Nat.zero_add, hvalue, Nat.lt_add_one, ite_true]
  · have hp : cache.parents.get node ≠ none := fun hh => he ((hroot node).mp hh)
    have hnonzero : encodedNode cache (cache.parents.get node) ≠ 0 := by
      cases hh : cache.parents.get node with
      | none => exact (hp hh).elim
      | some parent => change parent.val + 1 ≠ 0; omega
    have hacc : acc ≠ acc + rom.read .internal node.val := by rw [hrom.1 node]; omega
    have hval : root.val ≠ node.val := fun hh => he (Fin.ext hh.symm)
    have hc : root.val < node.val + 1 ↔ root.val < node.val := by omega
    have hsame : (cache.normalizeStep capacity node).get root = capacity.get root := by
      rw [indexed_normalizeStep_get]
      simp only [Ne.symm he, and_false, ite_false]
    unfold RootRep at hrep ⊢
    rw [execute_nodeBlock_heap, Function.update_of_ne hacc, Function.update_of_ne hcap, hrep]
    simp only [hc, hsame]

theorem prepared_root_parent_iff (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    ∃ root : (prepareNormalization q full).indexed.NodeId,
      (prepareNormalization q full).indexed.decode root = Finset.univ ∧
      ∀ node : (prepareNormalization q full).indexed.NodeId,
        (prepareNormalization q full).indexed.parents.get node = none ↔ node = root := by
  obtain ⟨root, hr⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  refine ⟨root, hr, ?_⟩
  intro node
  rw [prepared_indexed_parent_none_iff q full hq hlaminar node]
  exact ⟨fun he => prepared_indexed_decode_injective q full (he.trans hr.symm), fun he => he ▸ hr⟩

theorem prepared_nodeBlock_safe (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (words cap acc : Nat)
    (hdisjoint : Disjoint (prepareNormalization q full).indexed.nodes.size cap acc)
    (root : (prepareNormalization q full).indexed.NodeId)
    (hroot : ∀ child : (prepareNormalization q full).indexed.NodeId,
      (prepareNormalization q full).indexed.parents.get child = none ↔ child = root)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (state : State) (hbound : CapacityPrefixBounded q words state.heap)
    (node : (prepareNormalization q full).indexed.NodeId)
    (hrep : Represents (prepareNormalization q full).indexed cap acc node.val capacity state)
    (hr : RootRep (prepareNormalization q full).indexed root acc node.val capacity state) :
    let cache := (prepareNormalization q full).indexed
    let block := nodeBlock cache.nodes.size cap acc node.val
    let after := execute (givenTreeROM q full).semantic block state
    CapacityThroughout q words (givenTreeROM q full) block state ∧
      Represents cache cap acc (node.val + 1) (cache.normalizeStep capacity node) after ∧
      RootRep cache root acc (node.val + 1) (cache.normalizeStep capacity node) after := by
  intro cache block after
  let rom := givenTreeROM q full
  have hrom := givenTreeROM_tree q full hq hlaminar
  have hnodup : ∀ parent : cache.NodeId, (cache.children.get parent).toList.Nodup :=
    indexNodes_children_nodup _ _
  have hmem : ∀ child parent : cache.NodeId,
      child ∈ cache.childIds parent ↔ cache.parents.get child = some parent := by
    intro child parent
    simp only [IndexedNodeCache.childIds, List.mem_toFinset, Array.mem_toList_iff]
    exact indexNodes_child_mem _ _ child parent
  have horder := prepared_child_index_lt q full hq hlaminar
  have hv := updatedValue_eq_normalizeStep cache rom.semantic hrom cap acc capacity state node
    (hnodup node) (horder node) hrep
  have ha := nodeBlock_represents cache rom.semantic hrom cap acc hdisjoint hnodup hmem horder
    capacity state node hrep
  have har := nodeBlock_rootRep cache rom.semantic hrom cap acc hdisjoint root hroot capacity state node hv hr
  have hnew (target : cache.NodeId) :
      (cache.normalizeStep capacity node).get target ≤ (cache.decode target).card :=
    (indexed_normalizeStep_le cache capacity node target).trans (hcard target)
  have hqcard (target : cache.NodeId) : (cache.decode target).card ≤ q := by
    simpa only [Fintype.card_fin] using Finset.card_le_univ (cache.decode target)
  have hacc : after.heap (acc + rom.semantic.read .internal node.val) ≤ q := by
    rw [hrom.1 node]
    cases hp : cache.parents.get node with
    | none =>
      change after.heap acc ≤ q
      rw [har]
      split_ifs
      · exact (hnew root).trans (hqcard root)
      · exact Nat.zero_le q
    | some parent =>
      change after.heap (acc + (parent.val + 1)) ≤ q
      rw [← Nat.add_assoc, ha.2 parent]
      exact (partialChildSum_le_childSum cache _ _ parent (hnodup parent)).trans
        ((prepared_indexed_childSum_le_card q full hq hlaminar _ hnew parent).trans (hqcard parent))
  refine ⟨?_, ha, har⟩
  have hvalue : updatedValue rom.semantic cache.nodes.size cap acc node.val state ≤ q := by
    rw [hv]
    exact (hnew node).trans (hqcard node)
  have hu := updateNode_capacityThroughout q words cache.nodes.size cap acc node.val rom state hbound hvalue
  apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hu
  apply pushParent_capacityThroughout q words acc node.val rom
  · simpa only [List.take_length] using hu _ le_rfl
  · rw [execute_updateNode_heap, execute_updateNode_fresh]
    have heq : after.heap (acc + rom.semantic.read .internal node.val) =
        (Function.update state.heap (cap + node.val)
          (updatedValue rom.semantic cache.nodes.size cap acc node.val state))
          (acc + rom.semantic.read .internal node.val) +
        updatedValue rom.semantic cache.nodes.size cap acc node.val state := by
      rw [execute_nodeBlock_heap, Function.update_self]
    rw [← heq]
    exact hacc

theorem prepared_nodes_capacityThroughout (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (words cap acc : Nat)
    (hdisjoint : Disjoint (prepareNormalization q full).indexed.nodes.size cap acc)
    (root : (prepareNormalization q full).indexed.NodeId)
    (hroot : ∀ child : (prepareNormalization q full).indexed.NodeId,
      (prepareNormalization q full).indexed.parents.get child = none ↔ child = root)
    (start remaining : Nat) (hsize : start + remaining ≤ (prepareNormalization q full).indexed.nodes.size)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (state : State) (hbound : CapacityPrefixBounded q words state.heap)
    (hrep : Represents (prepareNormalization q full).indexed cap acc start capacity state)
    (hr : RootRep (prepareNormalization q full).indexed root acc start capacity state) :
    CapacityThroughout q words (givenTreeROM q full)
      ((List.range' start remaining).flatMap
        (nodeBlock (prepareNormalization q full).indexed.nodes.size cap acc)) state := by
  induction remaining generalizing start capacity state with
  | zero =>
    intro count hc
    simpa only [List.range'_zero, List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hbound
  | succ remaining ih =>
    let cache := (prepareNormalization q full).indexed
    have hs : start < cache.nodes.size := by
      change start < (prepareNormalization q full).indexed.nodes.size
      omega
    let node : cache.NodeId := ⟨start, hs⟩
    obtain ⟨hblock, hnext, hrnext⟩ := prepared_nodeBlock_safe q full hq hlaminar words cap acc
      hdisjoint root hroot capacity hcard state hbound node hrep hr
    rw [List.range'_succ, List.flatMap_cons]
    apply UniformFreeTableSafety.capacityThroughout_append q words (givenTreeROM q full) _ _ state hblock
    apply ih (start := start + 1) (capacity := cache.normalizeStep capacity node)
      (state := execute (givenTreeROM q full).semantic (nodeBlock cache.nodes.size cap acc start) state)
    · omega
    · intro target
      exact (indexed_normalizeStep_le cache capacity node target).trans (hcard target)
    · simpa only [List.take_length] using hblock _ le_rfl
    · exact hnext
    · exact hrnext

/-- Arbitrary accumulator contents are overwritten before the node pass.
Only other leading words have an initial bound. The unique root condition
is derived from the prepared tree, never supplied by this caller. -/
theorem prepared_after_clear_capacityThroughout (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (words cap acc : Nat)
    (hdisjoint : Disjoint (prepareNormalization q full).indexed.nodes.size cap acc)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (state : State)
    (hagrees : ∀ node : (prepareNormalization q full).indexed.NodeId,
      state.heap (cap + node.val) = capacity.get node)
    (hother : ∀ address < words,
      (∀ index ≤ (prepareNormalization q full).indexed.nodes.size, address ≠ acc + index) →
        state.heap address ≤ q) :
    let cache := (prepareNormalization q full).indexed
    CapacityThroughout q words (givenTreeROM q full)
      ((List.range cache.nodes.size).flatMap (nodeBlock cache.nodes.size cap acc))
      (execute (givenTreeROM q full).semantic (clearWords acc (cache.nodes.size + 1)) state) := by
  intro cache
  obtain ⟨root, _, hroot⟩ := prepared_root_parent_iff q full hq hlaminar
  have hrep := clearWords_represents cache (givenTreeROM q full).semantic cap acc hdisjoint capacity state hagrees
  have hr : RootRep cache root acc 0 capacity
      (execute (givenTreeROM q full).semantic (clearWords acc (cache.nodes.size + 1)) state) := by
    have hz := clearIndices_value (givenTreeROM q full).semantic acc (List.range (cache.nodes.size + 1)) state 0
      (List.mem_range.mpr (by omega))
    simpa only [RootRep, clearWords, Nat.add_zero, Nat.not_lt_zero, ite_false] using hz
  have hh := prepared_nodes_capacityThroughout q full hq hlaminar words cap acc hdisjoint root hroot
    0 cache.nodes.size (by simp only [Nat.zero_add]; exact le_rfl) capacity hcard _
    (clearWords_bounded q words acc cache.nodes.size (givenTreeROM q full).semantic state hother) hrep hr
  simpa only [List.range_eq_range'] using hh

/-- The original all-prefix capacity target, including clock zero and
the actual clearing instructions, for any layout and any bounded scratch. -/
theorem prepared_program_capacityThroughout (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (words cap acc : Nat)
    (hdisjoint : Disjoint (prepareNormalization q full).indexed.nodes.size cap acc)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (state : State) (hbound : CapacityPrefixBounded q words state.heap)
    (hagrees : ∀ node : (prepareNormalization q full).indexed.NodeId,
      state.heap (cap + node.val) = capacity.get node) :
    CapacityThroughout q words (givenTreeROM q full)
      (program (prepareNormalization q full).indexed.nodes.size cap acc) state := by
  rw [program]
  apply UniformFreeTableSafety.capacityThroughout_append q words (givenTreeROM q full) _ _ state
    (clearIndices_capacityThroughout q words acc (givenTreeROM q full)
      (List.range ((prepareNormalization q full).indexed.nodes.size + 1)) state hbound)
  exact prepared_after_clear_capacityThroughout q full hq hlaminar words cap acc hdisjoint
    capacity hcard state hagrees (fun address ha _ => hbound address ha)

end PaperProofs.Structure.LaminarTree.PA17NormalizationSafety004
