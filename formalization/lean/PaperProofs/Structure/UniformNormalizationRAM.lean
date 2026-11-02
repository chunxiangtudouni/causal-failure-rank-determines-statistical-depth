module

public import PaperProofs.Structure.AlgorithmClaims
public import PaperProofs.Structure.IndexedCellRAM

/-! A dimension-only, bottom-up parent-push normalizer. The executable reads
the actual given-tree parent and degree words. No child list, cardinality,
internal flag or normalized capacity is compiled into its instructions. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.UniformNormalizationRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims

variable {Tool : Type*}

def clearBlock (address : Nat) : List Op :=
  [.base (.constant .index address), .base (.constant .value 0), .base (.storeHeap .index .value)]

def clearWords (base count : Nat) : List Op :=
  (List.range count).flatMap (fun index => clearBlock (base + index))

def updateNode (size capacityBase accumulatorBase node : Nat) : List Op :=
  [.base (.constant .index (size + node)), .base (.loadROM .internal .flag .index),
   .base (.constant .address (accumulatorBase + node + 1)), .base (.loadHeap .total .address),
   .base (.constant .index (capacityBase + node)), .base (.loadHeap .old .index),
   .base (.minimum .fresh .old .total), .base (.select .fresh .flag .fresh .old),
   .base (.storeHeap .index .fresh)]

def pushParent (accumulatorBase node : Nat) : List Op :=
  [.base (.constant .index node), .base (.loadROM .internal .index .index),
   .base (.constant .address accumulatorBase), .base (.add .address .address .index),
   .base (.loadHeap .total .address), .base (.add .total .total .fresh),
   .base (.storeHeap .address .total)]

def nodeBlock (size capacityBase accumulatorBase node : Nat) : List Op :=
  updateNode size capacityBase accumulatorBase node ++ pushParent accumulatorBase node

def program (size capacityBase accumulatorBase : Nat) : List Op :=
  clearWords accumulatorBase (size + 1) ++
    (List.range size).flatMap (nodeBlock size capacityBase accumulatorBase)

def updatedValue (rom : ROM) (size capacityBase accumulatorBase node : Nat) (state : State) : Nat :=
  if rom.read .internal (size + node) = 0 then state.heap (capacityBase + node)
  else min (state.heap (capacityBase + node)) (state.heap (accumulatorBase + node + 1))

theorem execute_clearBlock_heap (rom : ROM) (address : Nat) (state : State) :
    (execute rom (clearBlock address) state).heap = Function.update state.heap address 0 := rfl

theorem execute_updateNode_heap (rom : ROM) (size capacityBase accumulatorBase node : Nat) (state : State) :
    (execute rom (updateNode size capacityBase accumulatorBase node) state).heap =
      Function.update state.heap (capacityBase + node) (updatedValue rom size capacityBase accumulatorBase node state) := rfl

theorem execute_updateNode_fresh (rom : ROM) (size capacityBase accumulatorBase node : Nat) (state : State) :
    (execute rom (updateNode size capacityBase accumulatorBase node) state).register .fresh =
      updatedValue rom size capacityBase accumulatorBase node state := rfl

theorem execute_pushParent_heap (rom : ROM) (accumulatorBase node : Nat) (state : State) :
    (execute rom (pushParent accumulatorBase node) state).heap =
      Function.update state.heap (accumulatorBase + rom.read .internal node)
        (state.heap (accumulatorBase + rom.read .internal node) + state.register .fresh) := rfl

theorem execute_nodeBlock_heap (rom : ROM) (size capacityBase accumulatorBase node : Nat) (state : State) :
    let value := updatedValue rom size capacityBase accumulatorBase node state
    let changed := Function.update state.heap (capacityBase + node) value
    (execute rom (nodeBlock size capacityBase accumulatorBase node) state).heap =
      Function.update changed (accumulatorBase + rom.read .internal node)
        (changed (accumulatorBase + rom.read .internal node) + value) := by
  dsimp only
  rw [nodeBlock, IndexedClosureRAM.execute_append, execute_pushParent_heap, execute_updateNode_heap, execute_updateNode_fresh]

theorem program_length (size capacityBase accumulatorBase : Nat) :
    (program size capacityBase accumulatorBase).length = 19 * size + 3 := by
  have hc (address : Nat) : (clearBlock address).length = 3 := rfl
  have hn (node : Nat) : (nodeBlock size capacityBase accumulatorBase node).length = 16 := rfl
  simp only [program, clearWords, List.length_append, List.length_flatMap, hc, hn,
    List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem trace_flatMap_length {α : Type*} (entries : List α) (blocks : α → List Op) :
    (trace (entries.flatMap blocks)).length = (entries.map (fun entry => (trace (blocks entry)).length)).sum := by
  simp only [trace, List.flatMap_assoc, List.length_flatMap]

theorem program_trace_length (size capacityBase accumulatorBase : Nat) :
    (trace (program size capacityBase accumulatorBase)).length = 189 * size + 27 := by
  have hc (address : Nat) : (trace (clearBlock address)).length = 27 := rfl
  have hn (node : Nat) : (trace (nodeBlock size capacityBase accumulatorBase node)).length = 162 := rfl
  rw [program, IndexedClosureRAM.trace_append, List.length_append, clearWords, trace_flatMap_length, trace_flatMap_length]
  simp only [hc, hn,
    List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

def partialChildSum (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (count : Nat) (parent : cache.NodeId) : Nat :=
  ∑ child ∈ cache.childIds parent, if child.val < count then capacity.get child else 0

theorem partialChildSum_zero (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (parent : cache.NodeId) : partialChildSum cache capacity 0 parent = 0 := by
  simp only [partialChildSum, Nat.not_lt_zero, ite_false, Finset.sum_const_zero]

theorem partialChildSum_full (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (parent : cache.NodeId) (hnodup : (cache.children.get parent).toList.Nodup)
    (horder : ∀ child ∈ (cache.children.get parent).toList, child.val < parent.val) :
    partialChildSum cache capacity parent.val parent = cache.childSum capacity parent := by
  rw [childSum_eq_finset cache capacity parent hnodup]
  apply Finset.sum_congr rfl
  intro child hc
  have hm : child ∈ (cache.children.get parent).toList := List.mem_toFinset.mp hc
  exact ite_eq_left (horder child hm)

theorem partialChildSum_succ (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (node parent : cache.NodeId) :
    partialChildSum cache (cache.normalizeStep capacity node) (node.val + 1) parent =
      partialChildSum cache capacity node.val parent +
        if node ∈ cache.childIds parent then (cache.normalizeStep capacity node).get node else 0 := by
  classical
  have hf (child : cache.NodeId) :
      (if child.val < node.val + 1 then (cache.normalizeStep capacity node).get child else 0) =
        (if child.val < node.val then capacity.get child else 0) +
          if child = node then (cache.normalizeStep capacity node).get node else 0 := by
    by_cases heq : child = node
    · subst child
      simp only [Nat.lt_add_one, ite_true, lt_self_iff_false, ite_false, zero_add]
    · have hval : child.val ≠ node.val := fun hh => heq (Fin.ext hh)
      have hs : (cache.normalizeStep capacity node).get child = capacity.get child := by
        rw [indexed_normalizeStep_get]
        simp only [heq, and_false, ite_false]
      have hlt : child.val < node.val + 1 ↔ child.val < node.val := by omega
      simp only [hs, hlt, heq, ite_false, add_zero]
  unfold partialChildSum
  simp only [hf, Finset.sum_add_distrib, Finset.sum_ite_eq']

def Represents (cache : IndexedNodeCache Tool) (capacityBase accumulatorBase count : Nat)
    (capacity : IndexedCapacity cache) (state : State) : Prop :=
  (∀ node : cache.NodeId, state.heap (capacityBase + node.val) = capacity.get node) ∧
    ∀ parent : cache.NodeId, state.heap (accumulatorBase + parent.val + 1) =
      partialChildSum cache capacity count parent

def Disjoint (size capacityBase accumulatorBase : Nat) : Prop :=
  ∀ node < size, ∀ slot ≤ size, capacityBase + node ≠ accumulatorBase + slot

def TreeROMFor (cache : IndexedNodeCache Tool) (rom : ROM) : Prop :=
  (∀ node : cache.NodeId, rom.read .internal node.val = encodedNode cache (cache.parents.get node)) ∧
    ∀ node : cache.NodeId, rom.read .internal (cache.nodes.size + node.val) ≠ 0 ↔ 1 < (cache.decode node).card

theorem encodedNode_le (cache : IndexedNodeCache Tool) (node : Option cache.NodeId) :
    encodedNode cache node ≤ cache.nodes.size := by
  cases node with
  | none => exact Nat.zero_le _
  | some node => exact node.isLt

theorem encodedNode_eq_some (cache : IndexedNodeCache Tool) (node : Option cache.NodeId)
    (parent : cache.NodeId) : encodedNode cache node = parent.val + 1 ↔ node = some parent := by
  cases node with
  | none => simp [encodedNode]
  | some node => simp only [encodedNode, Nat.add_right_cancel_iff, Option.some.injEq, Fin.val_inj]

theorem clearIndices_frame (rom : ROM) (base : Nat) (indices : List Nat) (state : State)
    (address : Nat) (hframe : ∀ index ∈ indices, address ≠ base + index) :
    (execute rom (indices.flatMap (fun index => clearBlock (base + index))) state).heap address = state.heap address := by
  induction indices generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih _ (fun index hi => hframe index (List.mem_cons_of_mem _ hi)),
      execute_clearBlock_heap, Function.update_of_ne (hframe head List.mem_cons_self)]

theorem clearIndices_value (rom : ROM) (base : Nat) (indices : List Nat) (state : State)
    (index : Nat) (hindex : index ∈ indices) :
    (execute rom (indices.flatMap (fun index => clearBlock (base + index))) state).heap (base + index) = 0 := by
  induction indices generalizing state with
  | nil => cases hindex
  | cons head later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    by_cases hi : index ∈ later
    · exact ih _ hi
    · have heq : index = head := (List.mem_cons.mp hindex).resolve_right hi
      subst index
      rw [clearIndices_frame rom base later _ _ (by
        intro other hother heq
        exact hi ((Nat.add_left_cancel heq) ▸ hother)), execute_clearBlock_heap, Function.update_self]

theorem clearWords_represents (cache : IndexedNodeCache Tool) (rom : ROM)
    (capacityBase accumulatorBase : Nat) (hdisjoint : Disjoint cache.nodes.size capacityBase accumulatorBase)
    (capacity : IndexedCapacity cache) (state : State)
    (hcapacity : ∀ node : cache.NodeId, state.heap (capacityBase + node.val) = capacity.get node) :
    Represents cache capacityBase accumulatorBase 0 capacity
      (execute rom (clearWords accumulatorBase (cache.nodes.size + 1)) state) := by
  constructor
  · intro node
    rw [clearWords, clearIndices_frame rom accumulatorBase _ state _ (by
      intro index hi
      exact hdisjoint node.val node.isLt index (by have := List.mem_range.mp hi; omega))]
    exact hcapacity node
  · intro parent
    rw [partialChildSum_zero]
    have hh := clearIndices_value rom accumulatorBase (List.range (cache.nodes.size + 1)) state
      (parent.val + 1) (List.mem_range.mpr (by omega))
    simpa only [clearWords, Nat.add_assoc] using hh

theorem nodeBlock_represents (cache : IndexedNodeCache Tool) (rom : ROM)
    (hrom : TreeROMFor cache rom) (capacityBase accumulatorBase : Nat)
    (hdisjoint : Disjoint cache.nodes.size capacityBase accumulatorBase)
    (hnodup : ∀ parent : cache.NodeId, (cache.children.get parent).toList.Nodup)
    (hmem : ∀ child parent : cache.NodeId, child ∈ cache.childIds parent ↔ cache.parents.get child = some parent)
    (horder : ∀ parent child : cache.NodeId, child ∈ (cache.children.get parent).toList → child.val < parent.val)
    (capacity : IndexedCapacity cache) (state : State) (node : cache.NodeId)
    (hrep : Represents cache capacityBase accumulatorBase node.val capacity state) :
    Represents cache capacityBase accumulatorBase (node.val + 1) (cache.normalizeStep capacity node)
      (execute rom (nodeBlock cache.nodes.size capacityBase accumulatorBase node.val) state) := by
  classical
  have hvalue : updatedValue rom cache.nodes.size capacityBase accumulatorBase node.val state =
      (cache.normalizeStep capacity node).get node := by
    rw [updatedValue, hrep.1 node, hrep.2 node,
      partialChildSum_full cache capacity node (hnodup node) (horder node), indexed_normalizeStep_get]
    by_cases hi : 1 < (cache.decode node).card
    · simp only [(hrom.2 node).mpr hi, hi, and_self, ite_false, ite_true]
    · have hz : rom.read .internal (cache.nodes.size + node.val) = 0 :=
        not_ne_iff.mp (fun h => hi ((hrom.2 node).mp h))
      simp only [hz, hi, false_and, ite_true, ite_false]
  have hparentBound : rom.read .internal node.val ≤ cache.nodes.size := by
    rw [hrom.1 node]
    exact encodedNode_le cache _
  have haccNe (target : cache.NodeId) :
      capacityBase + node.val ≠ accumulatorBase + target.val + 1 := by
    simpa only [Nat.add_assoc] using hdisjoint node.val node.isLt (target.val + 1) (by omega)
  have hcapNe (target : cache.NodeId) :
      capacityBase + target.val ≠ accumulatorBase + rom.read .internal node.val :=
    hdisjoint target.val target.isLt _ hparentBound
  constructor
  · intro target
    rw [execute_nodeBlock_heap, Function.update_of_ne (hcapNe target), hvalue]
    by_cases heq : target = node
    · subst target
      rw [Function.update_self]
    · have hn : capacityBase + target.val ≠ capacityBase + node.val :=
        fun hh => heq (Fin.ext (Nat.add_left_cancel hh))
      rw [Function.update_of_ne hn, hrep.1 target, indexed_normalizeStep_get]
      simp only [heq, and_false, ite_false]
  · intro parent
    have hsame : accumulatorBase + parent.val + 1 = accumulatorBase + rom.read .internal node.val ↔
        node ∈ cache.childIds parent := by
      rw [Nat.add_assoc, Nat.add_left_cancel_iff, eq_comm, hrom.1 node, encodedNode_eq_some, hmem]
    rw [execute_nodeBlock_heap, hvalue, partialChildSum_succ]
    by_cases hm : node ∈ cache.childIds parent
    · rw [← (hsame.mpr hm), Function.update_self, Function.update_of_ne (haccNe parent).symm, hrep.2 parent,
        ite_eq_left hm]
    · rw [Function.update_of_ne (fun hh => hm (hsame.mp hh)), Function.update_of_ne (haccNe parent).symm,
        hrep.2 parent, ite_eq_right hm, Nat.add_zero]

theorem normalizeAlong_append (cache : IndexedNodeCache Tool) (left right : List cache.NodeId)
    (capacity : IndexedCapacity cache) :
    cache.normalizeAlong (left ++ right) capacity = cache.normalizeAlong right (cache.normalizeAlong left capacity) := by
  induction left generalizing capacity with
  | nil => rfl
  | cons head later ih => exact ih _

theorem normalizePrefix_succ (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (count : Nat) (hcount : count < cache.nodes.size) :
    cache.normalizeAlong ((List.finRange cache.nodes.size).take (count + 1)) capacity =
      cache.normalizeStep (cache.normalizeAlong ((List.finRange cache.nodes.size).take count) capacity) ⟨count, hcount⟩ := by
  have hi : count < (List.finRange cache.nodes.size).length := by simpa only [List.length_finRange] using hcount
  rw [List.take_succ_eq_append_getElem hi, normalizeAlong_append, List.getElem_finRange]
  rfl

theorem program_represents (cache : IndexedNodeCache Tool) (rom : ROM)
    (hrom : TreeROMFor cache rom) (capacityBase accumulatorBase : Nat)
    (hdisjoint : Disjoint cache.nodes.size capacityBase accumulatorBase)
    (hnodup : ∀ parent : cache.NodeId, (cache.children.get parent).toList.Nodup)
    (hmem : ∀ child parent : cache.NodeId, child ∈ cache.childIds parent ↔ cache.parents.get child = some parent)
    (horder : ∀ parent child : cache.NodeId, child ∈ (cache.children.get parent).toList → child.val < parent.val)
    (capacity : IndexedCapacity cache) (state : State)
    (hcapacity : ∀ node : cache.NodeId, state.heap (capacityBase + node.val) = capacity.get node) :
    Represents cache capacityBase accumulatorBase cache.nodes.size (cache.normalize capacity)
      (execute rom (program cache.nodes.size capacityBase accumulatorBase) state) := by
  let start := execute rom (clearWords accumulatorBase (cache.nodes.size + 1)) state
  have hstart : Represents cache capacityBase accumulatorBase 0 capacity start :=
    clearWords_represents cache rom capacityBase accumulatorBase hdisjoint capacity state hcapacity
  have hprefix : ∀ count ≤ cache.nodes.size,
      Represents cache capacityBase accumulatorBase count
        (cache.normalizeAlong ((List.finRange cache.nodes.size).take count) capacity)
        (execute rom ((List.range count).flatMap (nodeBlock cache.nodes.size capacityBase accumulatorBase)) start) := by
    intro count
    induction count with
    | zero => intro _; exact hstart
    | succ count ih =>
      intro hc
      have hlt : count < cache.nodes.size := by omega
      have hp := ih (by omega)
      have hs := nodeBlock_represents cache rom hrom capacityBase accumulatorBase hdisjoint hnodup hmem horder
        _ _ ⟨count, hlt⟩ hp
      simpa only [List.range_succ, List.flatMap_append, IndexedClosureRAM.execute_append,
        List.flatMap_cons, List.flatMap_nil, List.append_nil, normalizePrefix_succ cache capacity count hlt] using hs
  have ht := hprefix cache.nodes.size le_rfl
  have htake : (List.finRange cache.nodes.size).take cache.nodes.size = List.finRange cache.nodes.size := by
    simpa only [List.length_finRange] using (List.take_length (l := List.finRange cache.nodes.size))
  simpa only [program, IndexedClosureRAM.execute_append, start, htake, IndexedNodeCache.normalize] using ht

theorem nodeBlock_frame (rom : ROM) (size capacityBase accumulatorBase node : Nat) (state : State)
    (address : Nat) (hcap : address ≠ capacityBase + node)
    (hacc : address ≠ accumulatorBase + rom.read .internal node) :
    (execute rom (nodeBlock size capacityBase accumulatorBase node) state).heap address = state.heap address := by
  rw [execute_nodeBlock_heap, Function.update_of_ne hacc, Function.update_of_ne hcap]

theorem nodes_frame (rom : ROM) (size capacityBase accumulatorBase : Nat) (nodes : List Nat)
    (state : State) (address : Nat)
    (hcap : ∀ node ∈ nodes, address ≠ capacityBase + node)
    (hacc : ∀ node ∈ nodes, address ≠ accumulatorBase + rom.read .internal node) :
    (execute rom (nodes.flatMap (nodeBlock size capacityBase accumulatorBase)) state).heap address = state.heap address := by
  induction nodes generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append,
      ih _ (fun node hn => hcap node (List.mem_cons_of_mem _ hn))
        (fun node hn => hacc node (List.mem_cons_of_mem _ hn))]
    exact nodeBlock_frame rom size capacityBase accumulatorBase head state address
      (hcap head List.mem_cons_self) (hacc head List.mem_cons_self)

theorem program_frame (cache : IndexedNodeCache Tool) (rom : ROM) (hrom : TreeROMFor cache rom)
    (capacityBase accumulatorBase : Nat) (state : State) (address : Nat)
    (hcap : ∀ node < cache.nodes.size, address ≠ capacityBase + node)
    (hacc : ∀ slot ≤ cache.nodes.size, address ≠ accumulatorBase + slot) :
    (execute rom (program cache.nodes.size capacityBase accumulatorBase) state).heap address = state.heap address := by
  rw [program, IndexedClosureRAM.execute_append,
    nodes_frame rom cache.nodes.size capacityBase accumulatorBase _ _ address
      (fun node hn => hcap node (List.mem_range.mp hn)) (by
        intro node hn
        rw [hrom.1 ⟨node, List.mem_range.mp hn⟩]
        exact hacc _ (encodedNode_le cache _)), clearWords]
  exact clearIndices_frame rom accumulatorBase _ state address (fun index hi =>
    hacc index (by have := List.mem_range.mp hi; omega))

theorem givenTreeROM_parent (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    (givenTreeROM q full).semantic.read .internal node.val =
      encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get node) := by
  let cache := (prepareNormalization q full).indexed
  change ((List.finRange cache.nodes.size).map (fun node => encodedNode cache (cache.parents.get node)) ++
    (List.finRange cache.nodes.size).map (fun node => (cache.children.get node).size)).getD node.val 0 = _
  rw [List.getD_append _ _ _ _ (by simpa only [List.length_map, List.length_finRange] using node.isLt),
    List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_finRange] using node.isLt)]
  simp only [List.getElem_map, List.getElem_finRange]
  exact congrArg (fun index : cache.NodeId => encodedNode cache (cache.parents.get index)) (Fin.ext rfl)

theorem givenTreeROM_degree (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    (givenTreeROM q full).semantic.read .internal ((prepareNormalization q full).indexed.nodes.size + node.val) =
      ((prepareNormalization q full).indexed.children.get node).size := by
  let cache := (prepareNormalization q full).indexed
  change ((List.finRange cache.nodes.size).map (fun node => encodedNode cache (cache.parents.get node)) ++
    (List.finRange cache.nodes.size).map (fun node => (cache.children.get node).size)).getD (cache.nodes.size + node.val) 0 = _
  rw [List.getD_append_right _ _ _ _ (by simp only [List.length_map, List.length_finRange]; omega)]
  simp only [List.length_map, List.length_finRange, Nat.add_sub_cancel_left]
  rw [List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_finRange] using node.isLt)]
  simp only [List.getElem_map, List.getElem_finRange]
  exact congrArg (fun index : cache.NodeId => (cache.children.get index).size) (Fin.ext rfl)

theorem prepared_degree_internal (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (node : (prepareNormalization q full).indexed.NodeId) :
    ((prepareNormalization q full).indexed.children.get node).size ≠ 0 ↔
      1 < ((prepareNormalization q full).indexed.decode node).card := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  constructor
  · intro hne
    have hpos := Nat.pos_of_ne_zero hne
    let child := ((prepareNormalization q full).indexed.children.get node)[0]'hpos
    have hchild : child ∈ ((prepareNormalization q full).indexed.children.get node).toList :=
      Array.getElem_mem_toList hpos
    have hlt := prepared_indexed_child_card_lt q full hq hlaminar node child hchild
    have hc := Finset.card_pos.mpr (nodeFamily_nonempty_nodes full _ (prepared_indexed_node_mem q full child))
    omega
  · intro hi hz
    have hlist : ((prepareNormalization q full).indexed.children.get node).toList = [] :=
      List.eq_nil_of_length_eq_zero (by simpa only [Array.length_toList] using hz)
    have hids : (prepareNormalization q full).indexed.childIds node = ∅ := by
      simp only [IndexedNodeCache.childIds, hlist, List.toFinset_nil]
    have hcover := prepared_indexed_children_cover q full hq hlaminar node hi
    rw [hids, Finset.biUnion_empty] at hcover
    rw [← hcover, Finset.card_empty] at hi
    omega

theorem prepared_child_index_lt (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (parent child : (prepareNormalization q full).indexed.NodeId)
    (hchild : child ∈ ((prepareNormalization q full).indexed.children.get parent).toList) :
    child.val < parent.val := by
  have hcard := prepared_indexed_child_card_lt q full hq hlaminar parent child hchild
  by_contra hlt
  have hle : parent.val ≤ child.val := Nat.le_of_not_gt hlt
  rcases Nat.eq_or_lt_of_le hle with heq | hstrict
  · have heq' : parent = child := Fin.ext heq
    rw [heq'] at hcard
    exact Nat.lt_irrefl _ hcard
  · have hsorted := (prepared_order_sorted q full).rel_get_of_lt
      (a := ⟨parent.val, parent.isLt⟩) (b := ⟨child.val, child.isLt⟩) hstrict
    have hcardle : ((prepareNormalization q full).indexed.decode parent).card ≤
        ((prepareNormalization q full).indexed.decode child).card := by
      change (((prepareNormalization q full).order.toArray[parent.val])).card ≤
        (((prepareNormalization q full).order.toArray[child.val])).card
      simpa only [List.get_eq_getElem, List.getElem_toArray] using hsorted
    exact Nat.not_lt_of_ge hcardle hcard

theorem givenTreeROM_tree (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    TreeROMFor (prepareNormalization q full).indexed (givenTreeROM q full).semantic := by
  constructor
  · exact givenTreeROM_parent q full
  · intro node
    rw [givenTreeROM_degree]
    exact prepared_degree_internal q full hq hlaminar node

theorem prepared_program_represents (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (capacityBase accumulatorBase : Nat)
    (hdisjoint : Disjoint (prepareNormalization q full).indexed.nodes.size capacityBase accumulatorBase)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) (state : State)
    (hcapacity : ∀ node : (prepareNormalization q full).indexed.NodeId,
      state.heap (capacityBase + node.val) = capacity.get node) :
    Represents (prepareNormalization q full).indexed capacityBase accumulatorBase
      (prepareNormalization q full).indexed.nodes.size ((prepareNormalization q full).indexed.normalize capacity)
      (execute (givenTreeROM q full).semantic
        (program (prepareNormalization q full).indexed.nodes.size capacityBase accumulatorBase) state) := by
  apply program_represents _ _ (givenTreeROM_tree q full hq hlaminar) _ _ hdisjoint
    (indexNodes_children_nodup _ _) ?_ (prepared_child_index_lt q full hq hlaminar) capacity state hcapacity
  intro child parent
  simp only [IndexedNodeCache.childIds, List.mem_toFinset, Array.mem_toList_iff]
  exact indexNodes_child_mem _ _ child parent

def defaultProgram (size : Nat) : List Op := program size 0 (size + 1)

theorem default_disjoint (size : Nat) : Disjoint size 0 (size + 1) := by
  intro node hn slot _
  omega

theorem defaultProgram_preserves_tag (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (state : State) :
    let size := (prepareNormalization q full).indexed.nodes.size
    (execute (givenTreeROM q full).semantic (defaultProgram size) state).heap size = state.heap size := by
  intro size
  exact program_frame _ _ (givenTreeROM_tree q full hq hlaminar) 0 (size + 1) state size
    (by intro node hn; omega) (by intro slot hs; omega)

theorem defaultProgram_payload (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) (state : State)
    (hcapacity : HeapAgrees state.heap capacity) :
    HeapAgrees (execute (givenTreeROM q full).semantic
      (defaultProgram (prepareNormalization q full).indexed.nodes.size) state).heap
      ((prepareNormalization q full).indexed.normalize capacity) := by
  unfold HeapAgrees defaultProgram
  intro node
  have hh := (prepared_program_represents q full hq hlaminar 0 _ (default_disjoint _)
    capacity state (by intro target; simpa only [Nat.zero_add] using hcapacity target)).1 node
  simpa only [Nat.zero_add] using hh

theorem defaultProgram_slot (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (state : State)
    (hrep : IndexedCellRAM.SlotRep (prepareNormalization q full).indexed state.heap 0 entry) :
    IndexedCellRAM.slot (prepareNormalization q full).indexed
      (execute (givenTreeROM q full).semantic (defaultProgram (prepareNormalization q full).indexed.nodes.size) state).heap 0 =
      match entry with
      | .void => .void
      | .vector capacity => .vector ((prepareNormalization q full).indexed.normalize capacity) := by
  have ht := defaultProgram_preserves_tag q full hq hlaminar state
  dsimp only at ht
  cases entry with
  | void =>
    apply IndexedCellRAM.slot_eq_of_rep
    change (execute (givenTreeROM q full).semantic
      (defaultProgram (prepareNormalization q full).indexed.nodes.size) state).heap
        (0 + (prepareNormalization q full).indexed.nodes.size) = 0
    rw [Nat.zero_add, ht]
    simpa only [IndexedCellRAM.SlotRep, Nat.zero_add] using hrep
  | vector capacity =>
    apply IndexedCellRAM.slot_eq_of_rep
    constructor
    · rw [Nat.zero_add, ht]
      simpa only [Nat.zero_add] using hrep.1
    · intro node
      have hp := defaultProgram_payload q full hq hlaminar capacity state (by
        intro target
        simpa only [Nat.zero_add] using hrep.2 target)
      simpa only [Nat.zero_add] using hp node

theorem program_codeWords_length (size capacityBase accumulatorBase : Nat) :
    (haltingWords (program size capacityBase accumulatorBase)).length = 95 * size + 20 := by
  rw [IndexedClosureRAM.haltingWords, List.length_append, IndexedClosureRAM.programWords_length, program_length]
  have hh : haltWords.toArray.toList.length = 5 := rfl
  rw [hh]
  omega

theorem prepared_program_halting_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (capacityBase accumulatorBase : Nat)
    (hdisjoint : Disjoint (prepareNormalization q full).indexed.nodes.size capacityBase accumulatorBase)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) (state : State) (hpc : state.pc = 0)
    (hcapacity : ∀ node : (prepareNormalization q full).indexed.NodeId,
      state.heap (capacityBase + node.val) = capacity.get node) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ∃ final operations,
      HaltingRuns (givenTreeROM q full).semantic (program size capacityBase accumulatorBase) state final operations ∧
      (∀ node : (prepareNormalization q full).indexed.NodeId,
        final.heap (capacityBase + node.val) = ((prepareNormalization q full).indexed.normalize capacity).get node) ∧
      (∀ address : Nat,
        (∀ node < size, address ≠ capacityBase + node) →
        (∀ slot ≤ size, address ≠ accumulatorBase + slot) → final.heap address = state.heap address) ∧
      operations.length ≤ 222 * size := by
  intro size
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < size := by have := root.isLt; omega
  refine ⟨_, _, IndexedClosureRAM.execute_halts _ _ state hpc,
    (prepared_program_represents q full hq hlaminar capacityBase accumulatorBase hdisjoint capacity state hcapacity).1,
    ?_, ?_⟩
  · intro address hcap hacc
    exact program_frame _ _ (givenTreeROM_tree q full hq hlaminar) capacityBase accumulatorBase state address hcap hacc
  · rw [List.length_append, program_trace_length, IndexedClosureRAM.haltTrace_length]
    omega

end PaperProofs.Structure.LaminarTree.UniformNormalizationRAM
