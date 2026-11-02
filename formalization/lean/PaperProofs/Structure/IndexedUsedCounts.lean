module

public import PaperProofs.Structure.IndexedRAM
public import PaperProofs.Structure.IndexedDescent

/-!
The query's used counts are constructed by a real bottom-up RAM pass over
the same cached adjacency. Its input is the node-indexed used-singleton
bitmap (one bit per node, zero at internal nodes). This encoding is separate
from the mathematical Finset used for its correctness specification.
The pass does not evaluate intersections/cardinalities at runtime and does
not assume that the heap is preinitialized with the desired counts.
Full query/table execution, finite-word safety and initial bitmap encoding are
separate interfaces; no complexity guarantee is supplied as a data field.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedUsedCounts

open IndexedRAM IndexedDescent

def leafBitmap {q : Nat} (cache : IndexedNodeCache (Fin q)) (used : Finset (Fin q)) :
    IndexedCapacity cache :=
  Vector.ofFn (fun node => match (leafTools cache).get node with
    | none => 0
    | some tool => if tool ∈ used then 1 else 0)

theorem leafBitmap_bit {q : Nat} (cache : IndexedNodeCache (Fin q))
    (used : Finset (Fin q)) (node : cache.NodeId) : (leafBitmap cache used).get node ≤ 1 := by
  rw [leafBitmap, cache_get_ofFn]
  split
  · omega
  · split_ifs <;> omega

theorem leafBitmap_singleton {q : Nat} (cache : IndexedNodeCache (Fin q))
    (used : Finset (Fin q)) (node : cache.NodeId) (tool : Fin q)
    (hnode : cache.decode node = {tool}) :
    (leafBitmap cache used).get node = (used ∩ cache.decode node).card := by
  rw [leafBitmap, cache_get_ofFn, leafTools_get, hnode, singletonTool_singleton]
  by_cases htool : tool ∈ used <;> simp [htool]

theorem prepared_leafBitmap_leaf (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (used : Finset (Fin q)) (node : (prepareNormalization q full).indexed.NodeId)
    (hleaf : ¬ 1 < ((prepareNormalization q full).indexed.decode node).card) :
    (leafBitmap (prepareNormalization q full).indexed used).get node =
      (usedCounts (prepareNormalization q full).indexed used).get node := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hnonempty := nodeFamily_nonempty_nodes full _ (prepared_indexed_node_mem q full node)
  have hcard : ((prepareNormalization q full).indexed.decode node).card = 1 := by
    have hp := Finset.card_pos.mpr hnonempty
    omega
  obtain ⟨tool, hsingle⟩ := Finset.card_eq_one.mp hcard
  rw [usedCounts_get]
  exact leafBitmap_singleton _ used node tool hsingle

theorem prepared_count_childSum (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (used : Finset (Fin q))
    (parent : (prepareNormalization q full).indexed.NodeId)
    (hinternal : 1 < ((prepareNormalization q full).indexed.decode parent).card) :
    (prepareNormalization q full).indexed.childSum
      (usedCounts (prepareNormalization q full).indexed used) parent =
      (usedCounts (prepareNormalization q full).indexed used).get parent := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  rw [childSum_eq_finset _ _ parent (indexNodes_children_nodup _ _ parent)]
  simp_rw [usedCounts_get]
  have h := layout_used_count_eq_sum_children full hlaminar
    (prepared_indexed_node_mem q full parent) hinternal used
  change (used ∩ (prepareNormalization q full).indexed.decode parent).card =
    ∑ child ∈ children (nodeFamily full) ((prepareNormalization q full).indexed.decode parent),
      (used ∩ child).card at h
  rw [← prepared_indexed_children_decode q full hq hlaminar parent,
    Finset.sum_image (fun left _ right _ heq => prepared_indexed_decode_injective q full heq)] at h
  exact h.symm

def countTail (parent : Nat) : List Instruction :=
  [.constant .index parent, .loadROM .input .old .index,
    .select .fresh .flag .total .old, .storeHeap .index .fresh]

def countNode (parent offset degree : Nat) : List Instruction :=
  nodeHeader parent ++ (List.range degree).flatMap (childBlock offset) ++ countTail parent

def countNodes {Tool : Type*} (cache : IndexedNodeCache Tool) :
    List cache.NodeId → Nat → List Instruction
  | [], _ => []
  | parent :: later, offset => countNode parent.val offset (cache.children.get parent).size ++
      countNodes cache later (offset + (cache.children.get parent).size)

def countProgram {Tool : Type*} (cache : IndexedNodeCache Tool) : List Instruction :=
  countNodes cache (List.finRange cache.nodes.size) 0

def countROM {q : Nat} (cache : IndexedNodeCache (Fin q)) (used : Finset (Fin q)) : ROM :=
  (treeROM cache).withInput (leafBitmap cache used)

theorem execute_countTail_heap (rom : ROM) (parent : Nat) (state : State) :
    (execute rom (countTail parent) state).heap = Function.update state.heap parent
      (if state.register .flag = 0 then rom.read .input parent else state.register .total) := rfl

theorem execute_countNode_heap (rom : ROM) (parent offset degree : Nat) (state : State) :
    (execute rom (countNode parent offset degree) state).heap = Function.update state.heap parent
      (if rom.read .internal parent = 0 then rom.read .input parent else
        ((List.range degree).map (fun position => state.heap (rom.read .children (offset + position)))).sum) := by
  let headerState := execute rom (nodeHeader parent) state
  let childState := execute rom ((List.range degree).flatMap (childBlock offset)) headerState
  have hheap : childState.heap = state.heap :=
    (execute_childIndices_heap rom offset _ headerState).trans (execute_nodeHeader_heap rom parent state)
  have hflag : childState.register .flag = rom.read .internal parent :=
    (execute_childIndices_flag rom offset _ headerState).trans (execute_nodeHeader_flag rom parent state)
  have htotal : childState.register .total =
      ((List.range degree).map (fun position => state.heap (rom.read .children (offset + position)))).sum := by
    dsimp only [childState, headerState]
    rw [execute_childIndices_total, execute_nodeHeader_total, execute_nodeHeader_heap, Nat.zero_add]
  change (execute rom (nodeHeader parent ++
    (List.range degree).flatMap (childBlock offset) ++ countTail parent) state).heap = _
  rw [execute_append, execute_append]
  change (execute rom (countTail parent) childState).heap = _
  rw [execute_countTail_heap, hheap, hflag, htotal]

theorem countNodes_refines {Tool : Type*} (cache : IndexedNodeCache Tool)
    (counts : IndexedCapacity cache) (rom : ROM) (parents : List cache.NodeId) (offset : Nat)
    (state : State)
    (hsorted : parents.Pairwise (fun left right => left.val < right.val))
    (hchildrenBefore : ∀ parent child, child ∈ (cache.children.get parent).toList → child.val < parent.val)
    (hflags : InternalROMFor cache rom) (hchildren : ChildrenROMFor cache parents offset rom)
    (hleaf : ∀ parent, ¬ 1 < (cache.decode parent).card → rom.read .input parent.val = counts.get parent)
    (hsum : ∀ parent, 1 < (cache.decode parent).card → cache.childSum counts parent = counts.get parent)
    (houtside : ∀ node, node ∉ parents → state.heap node.val = counts.get node) :
    HeapAgrees (execute rom (countNodes cache parents offset) state).heap counts := by
  induction parents generalizing offset state with
  | nil => exact fun node => houtside node (by simp)
  | cons parent later ih =>
    obtain ⟨hhead, htail⟩ := List.pairwise_cons.mp hsorted
    have hchildNot (child : cache.NodeId) (hchild : child ∈ (cache.children.get parent).toList) :
        child ∉ parent :: later := by
      intro hm
      have hbefore := hchildrenBefore parent child hchild
      rcases List.mem_cons.mp hm with heq | hmem
      · subst child
        omega
      · have hafter := hhead child hmem
        omega
    have hactualSum :
        ((List.range (cache.children.get parent).size).map
          (fun position => state.heap (rom.read .children (offset + position)))).sum = cache.childSum counts parent := by
      apply congrArg List.sum
      apply List.ext_getElem
      · simp only [List.length_map, List.length_range, Array.length_toList]
      · intro position hleft _
        have hp : position < (cache.children.get parent).size := by
          simpa only [List.length_map, List.length_range] using hleft
        simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
        rw [hchildren.1 position hp]
        apply houtside
        apply hchildNot
        exact Array.getElem_mem_toList hp
    have hnode : (execute rom (countNode parent.val offset (cache.children.get parent).size) state).heap =
        Function.update state.heap parent.val (counts.get parent) := by
      rw [execute_countNode_heap, hactualSum]
      by_cases hinternal : 1 < (cache.decode parent).card
      · have hflag := (hflags parent).mpr hinternal
        rw [ite_eq_right hflag, hsum parent hinternal]
      · have hflag : rom.read .internal parent.val = 0 := by
          by_contra hne
          exact hinternal ((hflags parent).mp hne)
        rw [ite_eq_left hflag, hleaf parent hinternal]
    rw [countNodes, execute_append]
    apply ih _ _ htail hchildren.2
    intro node hn
    rw [hnode]
    by_cases heq : node = parent
    · subst node
      exact Function.update_self _ _ _
    · rw [Function.update_of_ne (fun h => heq (Fin.ext h))]
      exact houtside node (by simpa only [List.mem_cons, heq, false_or] using hn)

theorem countNode_trace_length (parent offset degree : Nat) :
    (primitiveTrace (countNode parent offset degree)).length = 69 + 60 * degree := by
  have ht : (primitiveTrace (countTail parent)).length = 42 := rfl
  rw [countNode, primitiveTrace_append, primitiveTrace_append, List.length_append,
    List.length_append, nodeHeader_trace_length, ht, primitiveTrace_length_flatMap]
  simp only [childBlock_trace_length, List.map_const', List.sum_replicate,
    List.length_range, Nat.nsmul_eq_mul]
  omega

theorem countNodes_trace_length {Tool : Type*} (cache : IndexedNodeCache Tool)
    (parents : List cache.NodeId) (offset : Nat) :
    (primitiveTrace (countNodes cache parents offset)).length = 69 * parents.length +
      60 * (parents.map (fun parent => (cache.children.get parent).size)).sum := by
  induction parents generalizing offset with
  | nil => rfl
  | cons parent later ih =>
    rw [countNodes, primitiveTrace_append, List.length_append, countNode_trace_length, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem prepared_countProgram_correct (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (initial : State) :
    HeapAgrees
      (execute (countROM (prepareNormalization q full).indexed used)
        (countProgram (prepareNormalization q full).indexed) initial).heap
      (usedCounts (prepareNormalization q full).indexed used) := by
  apply countNodes_refines
  · exact (List.pairwise_lt_finRange _)
  · exact prepared_child_index_lt q full hq hlaminar
  · exact ROM.withInput_flags _ _ (treeROM_flags _)
  · exact ROM.withInput_children _ _ _ _ (treeROM_children _)
  · intro parent hleaf
    change vectorMemory (leafBitmap (prepareNormalization q full).indexed used) parent.val = _
    rw [vectorMemory_at]
    exact prepared_leafBitmap_leaf q full hq used parent hleaf
  · exact prepared_count_childSum q full hq hlaminar used
  · intro node hn
    exact (hn (List.mem_finRange _)).elim

theorem prepared_countProgram_trace_le (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (primitiveTrace (countProgram (prepareNormalization q full).indexed)).length ≤
      129 * (prepareNormalization q full).indexed.nodes.size := by
  rw [countProgram, countNodes_trace_length, childArray_sum_finRange,
    prepared_indexed_edge_count q full hq hlaminar, List.length_finRange]
  omega

theorem prepared_countProgram_halts (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (used : Finset (Fin q))
    (initial : State) (hpc : initial.pc = 0) :
    ∃ final trace,
      HaltingRuns (countROM (prepareNormalization q full).indexed used)
        (countProgram (prepareNormalization q full).indexed) initial final trace ∧
      HeapAgrees final.heap (usedCounts (prepareNormalization q full).indexed used) ∧
      trace.length ≤ 135 * (prepareNormalization q full).indexed.nodes.size := by
  refine ⟨_, _, execute_halts _ _ initial hpc,
    prepared_countProgram_correct q full hq hlaminar used initial, ?_⟩
  rw [List.length_append, terminalTrace_length]
  have hb := prepared_countProgram_trace_le q full hq hlaminar
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hp : 0 < (prepareNormalization q full).indexed.nodes.size :=
    Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  omega

/-- A consumed tool changes only its cached singleton bit. Other bits,
including all internal-node bits, are preserved. -/
theorem leafBitmap_insert {q : Nat} (cache : IndexedNodeCache (Fin q))
    (hinjective : Function.Injective cache.decode) (used : Finset (Fin q))
    (tool : Fin q) (leaf : cache.NodeId) (hleaf : cache.decode leaf = {tool}) :
    leafBitmap cache (insert tool used) =
      (leafBitmap cache used).set leaf.val 1 leaf.isLt := by
  apply Vector.ext
  intro index hi
  let node : cache.NodeId := ⟨index, hi⟩
  change (leafBitmap cache (insert tool used)).get node =
    ((leafBitmap cache used).set leaf.val 1 leaf.isLt).get node
  rw [vector_set_get]
  by_cases heq : node = leaf
  · rw [heq]
    rw [leafBitmap, cache_get_ofFn, leafTools_get, hleaf, singletonTool_singleton]
    simp
  · rw [ite_eq_right heq, leafBitmap, cache_get_ofFn, leafBitmap, cache_get_ofFn]
    cases hl : (leafTools cache).get node with
    | none => rfl
    | some other =>
      have hother : other ≠ tool := by
        intro hs
        apply heq
        exact hinjective ((singletonTool_spec _ other (by simpa only [leafTools_get] using hl)).trans
          (hs ▸ hleaf.symm))
      simp only [Finset.mem_insert, hother, false_or]

def markUsedProgram (leaf : Nat) : List Instruction :=
  [.constant .index leaf, .constant .value 1, .storeHeap .index .value]

theorem execute_markUsedProgram_heap (rom : ROM) (leaf : Nat) (initial : State) :
    (execute rom (markUsedProgram leaf) initial).heap = Function.update initial.heap leaf 1 := rfl

theorem markUsedProgram_trace_length (leaf : Nat) :
    (primitiveTrace (markUsedProgram leaf)).length = 27 := rfl

theorem markUsedProgram_refines {q : Nat} (cache : IndexedNodeCache (Fin q))
    (hinjective : Function.Injective cache.decode) (used : Finset (Fin q))
    (tool : Fin q) (leaf : cache.NodeId) (hleaf : cache.decode leaf = {tool})
    (rom : ROM) (initial : State) (hagrees : HeapAgrees initial.heap (leafBitmap cache used)) :
    HeapAgrees (execute rom (markUsedProgram leaf.val) initial).heap (leafBitmap cache (insert tool used)) := by
  rw [leafBitmap_insert cache hinjective used tool leaf hleaf]
  intro node
  rw [execute_markUsedProgram_heap, vector_set_get]
  by_cases heq : node = leaf
  · subst node
    simp only [Function.update_self, ite_true]
  · rw [Function.update_of_ne (fun h => heq (Fin.ext h)), ite_eq_right heq]
    exact hagrees node

theorem prepared_markUsedProgram (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (used : Finset (Fin q)) (tool : Fin q) (rom : ROM)
    (initial : State) (hpc : initial.pc = 0)
    (hagrees : HeapAgrees initial.heap (leafBitmap (prepareNormalization q full).indexed used)) :
    let leaf := (IndexedStaticMetadata.buildPositive q full hq).toolNodes.get tool
    ∃ final trace,
      HaltingRuns rom (markUsedProgram leaf.val) initial final trace ∧
      HeapAgrees final.heap (leafBitmap (prepareNormalization q full).indexed (insert tool used)) ∧
      trace.length = 33 := by
  dsimp only
  refine ⟨_, _, execute_halts _ _ initial hpc, ?_, ?_⟩
  · apply markUsedProgram_refines _ (prepared_indexed_decode_injective q full) used tool
      _ (IndexedStaticMetadata.buildPositive_tool_decode q full hq tool) rom initial hagrees
  · rw [List.length_append, markUsedProgram_trace_length, terminalTrace_length]

end PaperProofs.Structure.LaminarTree.IndexedUsedCounts
