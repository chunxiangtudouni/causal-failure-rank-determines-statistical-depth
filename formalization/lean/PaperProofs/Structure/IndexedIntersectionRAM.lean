module

public import PaperProofs.Structure.IndexedClosureRAM

/-!
Actual coordinate-minimum followed by bottom-up normalization for the frozen
laminar closure lemma. Both input capacity payloads and VOID tags are read as
ordinary ROM words. Every minimum, write, child scan and HALT is charged.
This refines the full indexed intersection; finite-word packing and a whole
cell/table/query machine are separate obligations.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedIntersectionRAM

open IndexedRAM

variable {Tool : Type*}

def payload (cache : IndexedNodeCache Tool) (entry : IndexedEntry.FixedEntry cache) (index : Nat) : Nat :=
  match entry with
  | .void => 0
  | .vector capacity => if hi : index < cache.nodes.size then capacity.get ⟨index, hi⟩ else 0

def tag (cache : IndexedNodeCache Tool) : IndexedEntry.FixedEntry cache → Nat
  | .void => 0
  | .vector _ => 1

def minimumCapacity (cache : IndexedNodeCache Tool) (left right : IndexedEntry.FixedEntry cache) :
    IndexedCapacity cache := Vector.ofFn (fun node => min (payload cache left node.val) (payload cache right node.val))

def intersectionROM [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (left right : IndexedEntry.FixedEntry cache) : ROM :=
  { read := fun region index => match region with
    | .input => if index < cache.nodes.size then payload cache left index
        else if index = cache.nodes.size then tag cache left
        else if index = cache.nodes.size + 1 then tag cache right else 0
    | .internal => if index < cache.nodes.size then (treeROM cache).read .internal index
        else payload cache right (index - cache.nodes.size)
    | .children => (treeROM cache).read .children index }

def minimumBlock (size index : Nat) : List Instruction :=
  [.constant .index index, .loadROM .input .old .index,
    .constant .address (size + index), .loadROM .internal .fresh .address,
    .minimum .value .old .fresh, .storeHeap .index .value]

def minimumPass (size : Nat) : List Instruction := (List.range size).flatMap (minimumBlock size)

def tagTail (size : Nat) : List Instruction :=
  [.constant .index size, .loadROM .input .old .index,
    .constant .index (size + 1), .loadROM .input .fresh .index,
    .minimum .value .old .fresh, .constant .index size, .storeHeap .index .value]

def intersectionProgram (cache : IndexedNodeCache Tool) : List Instruction :=
  minimumPass cache.nodes.size ++ compileNodes cache (List.finRange cache.nodes.size) 0 ++ tagTail cache.nodes.size

def intersectionResult [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (left right : IndexedEntry.FixedEntry cache) (initial : State) : IndexedEntry.FixedEntry cache :=
  IndexedClosureRAM.decodeResult cache (execute (intersectionROM cache left right) (intersectionProgram cache) initial).heap

theorem minimumBlock_length (size index : Nat) : (minimumBlock size index).length = 6 := rfl

theorem minimumBlock_trace_length (size index : Nat) : (primitiveTrace (minimumBlock size index)).length = 60 := rfl

theorem tagTail_length (size : Nat) : (tagTail size).length = 7 := rfl

theorem tagTail_trace_length (size : Nat) : (primitiveTrace (tagTail size)).length = 68 := rfl

theorem minimumPass_length (size : Nat) : (minimumPass size).length = 6 * size := by
  simp only [minimumPass, List.length_flatMap, minimumBlock_length, List.map_const',
    List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem minimumPass_trace_length (size : Nat) : (primitiveTrace (minimumPass size)).length = 60 * size := by
  rw [minimumPass, primitiveTrace_length_flatMap]
  simp only [minimumBlock_trace_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem intersectionProgram_length (cache : IndexedNodeCache Tool) :
    (intersectionProgram cache).length = 14 * cache.nodes.size +
      6 * (∑ parent : cache.NodeId, (cache.children.get parent).size) + 7 := by
  simp only [intersectionProgram, List.length_append, minimumPass_length, compileNodes_length,
    List.length_finRange, childArray_sum_finRange, tagTail_length]
  omega

theorem intersectionProgram_trace_length (cache : IndexedNodeCache Tool) :
    (primitiveTrace (intersectionProgram cache)).length = 140 * cache.nodes.size +
      60 * (∑ parent : cache.NodeId, (cache.children.get parent).size) + 68 := by
  simp only [intersectionProgram, primitiveTrace_append, List.length_append, minimumPass_trace_length,
    compileNodes_trace_length, List.length_finRange, childArray_sum_finRange, tagTail_trace_length]
  omega

theorem execute_minimumBlock_heap (rom : ROM) (size index : Nat) (state : State) :
    (execute rom (minimumBlock size index) state).heap =
      Function.update state.heap index (min (rom.read .input index) (rom.read .internal (size + index))) := rfl

theorem execute_minimumIndices_heap (rom : ROM) (size : Nat) (indices : List Nat) (state : State) (index : Nat) :
    (execute rom (indices.flatMap (minimumBlock size)) state).heap index =
      if index ∈ indices then min (rom.read .input index) (rom.read .internal (size + index)) else state.heap index := by
  induction indices generalizing state with
  | nil => simp only [List.flatMap_nil, execute, List.not_mem_nil, ↓reduceIte]
  | cons head later ih =>
    rw [List.flatMap_cons, execute_append, ih, execute_minimumBlock_heap]
    by_cases heq : index = head
    · subst index
      simp only [List.mem_cons_self, ↓reduceIte, Function.update_self, ite_self]
    · simp only [List.mem_cons, heq, false_or, Function.update_of_ne heq]

theorem intersectionROM_flags [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (left right : IndexedEntry.FixedEntry cache) : InternalROMFor cache (intersectionROM cache left right) := by
  intro node
  simpa only [intersectionROM, node.isLt, ↓reduceIte] using treeROM_flags cache node

theorem intersectionROM_children [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (left right : IndexedEntry.FixedEntry cache) :
    ChildrenROMFor cache (List.finRange cache.nodes.size) 0 (intersectionROM cache left right) := by
  apply childrenROMFor_of_slice
  intro position _
  simp only [intersectionROM, treeROM, Nat.zero_add]

theorem execute_minimumPass_agrees [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (left right : IndexedEntry.FixedEntry cache) (initial : State) :
    HeapAgrees (execute (intersectionROM cache left right) (minimumPass cache.nodes.size) initial).heap
      (minimumCapacity cache left right) := by
  intro node
  rw [minimumPass, execute_minimumIndices_heap]
  simp only [List.mem_range, node.isLt, ↓reduceIte, intersectionROM,
    minimumCapacity, cache_get_ofFn]
  have hlarge : ¬cache.nodes.size + node.val < cache.nodes.size := by omega
  simp only [hlarge, ↓reduceIte, Nat.add_sub_cancel_left]

theorem execute_tagTail_heap (rom : ROM) (size : Nat) (state : State) :
    (execute rom (tagTail size) state).heap = Function.update state.heap size
      (min (rom.read .input size) (rom.read .input (size + 1))) := rfl

theorem execute_intersectionProgram_agrees [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (left right : IndexedEntry.FixedEntry cache) (initial : State) :
    HeapAgrees (execute (intersectionROM cache left right) (intersectionProgram cache) initial).heap
      (cache.normalize (minimumCapacity cache left right)) := by
  intro node
  rw [intersectionProgram, execute_append, execute_tagTail_heap]
  have hne : node.val ≠ cache.nodes.size := Nat.ne_of_lt node.isLt
  rw [Function.update_of_ne hne]
  rw [execute_append]
  exact (execute_compileNodes_refines cache _ _ _ _ _
    (execute_minimumPass_agrees cache left right initial) (intersectionROM_flags cache left right)
    (intersectionROM_children cache left right)) node

theorem execute_intersectionProgram_tag [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (left right : IndexedEntry.FixedEntry cache) (initial : State) :
    (execute (intersectionROM cache left right) (intersectionProgram cache) initial).heap cache.nodes.size =
      min (tag cache left) (tag cache right) := by
  rw [intersectionProgram, execute_append, execute_tagTail_heap, Function.update_self]
  have hne : cache.nodes.size + 1 ≠ cache.nodes.size := by omega
  simp only [intersectionROM, Nat.lt_irrefl, ↓reduceIte,
    Nat.not_succ_lt_self, hne, ↓reduceIte]

theorem minimumCapacity_vector (cache : IndexedNodeCache Tool) (left right : IndexedCapacity cache) :
    minimumCapacity cache (.vector left) (.vector right) =
      Vector.ofFn (fun node => min (left.get node) (right.get node)) := by
  apply Vector.ext
  intro index hi
  change (minimumCapacity cache (.vector left) (.vector right)).get ⟨index, hi⟩ =
    (Vector.ofFn (fun node => min (left.get node) (right.get node))).get ⟨index, hi⟩
  simp only [minimumCapacity, cache_get_ofFn, payload, hi, ↓reduceDIte]

theorem intersectionResult_eq [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (left right : IndexedEntry.FixedEntry cache) (initial : State) :
    intersectionResult cache left right initial = IndexedEntry.intersect cache left right := by
  have htag := execute_intersectionProgram_tag cache left right initial
  have hagrees := execute_intersectionProgram_agrees cache left right initial
  unfold intersectionResult IndexedClosureRAM.decodeResult
  rw [htag]
  cases left with
  | void => simp only [tag, Nat.zero_min, ↓reduceIte, IndexedEntry.intersect, IndexedEntry.coordinateMin, IndexedEntry.normalize]
  | vector left =>
    cases right with
    | void => simp only [tag, Nat.min_zero, ↓reduceIte, IndexedEntry.intersect, IndexedEntry.coordinateMin, IndexedEntry.normalize]
    | vector right =>
      simp only [tag, Nat.min_self, Nat.one_ne_zero, ↓reduceIte]
      rw [IndexedClosureRAM.readCapacity_eq cache _ _ hagrees, minimumCapacity_vector]
      rfl

theorem prepared_intersection_halting_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (left right : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (initial : State) (hpc : initial.pc = 0) :
    ∃ final operations,
      HaltingRuns (intersectionROM (prepareNormalization q full).indexed left right)
        (intersectionProgram (prepareNormalization q full).indexed) initial final operations ∧
      IndexedClosureRAM.decodeResult (prepareNormalization q full).indexed final.heap =
        IndexedEntry.intersect (prepareNormalization q full).indexed left right ∧
      operations.length ≤ 274 * (prepareNormalization q full).indexed.nodes.size := by
  refine ⟨_, _, execute_halts _ _ initial hpc, intersectionResult_eq _ left right initial, ?_⟩
  rw [List.length_append, terminalTrace_length, intersectionProgram_trace_length,
    prepared_indexed_edge_count q full hq hlaminar]
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hp : 0 < (prepareNormalization q full).indexed.nodes.size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  omega

/-- The semantic and complete O(t) machine guarantees for normalization are
combined under exactly the original coordinate bounds. The tree/ROM is the
shared prepared object, not rebuilt by the pass. -/
theorem prepared_normalization_correct_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hbounded : ∀ node, capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (initial : State) (hpc : initial.pc = 0) :
    ∃ final operations,
      HaltingRuns ((treeROM (prepareNormalization q full).indexed).withInput capacity)
        (normalizationProgram (prepareNormalization q full).indexed) initial final operations ∧
      HeapAgrees final.heap ((prepareNormalization q full).indexed.normalize capacity) ∧
      (prepareNormalization q full).indexed.capacityFamily
        (IndexedClosureRAM.readCapacity (prepareNormalization q full).indexed final.heap) =
        (prepareNormalization q full).indexed.capacityFamily capacity ∧
      IndexedNormalized (prepareNormalization q full).indexed
        (IndexedClosureRAM.readCapacity (prepareNormalization q full).indexed final.heap) ∧
      (∀ node, (IndexedClosureRAM.readCapacity (prepareNormalization q full).indexed final.heap).get node ≤ q) ∧
      operations.length ≤ 176 * (prepareNormalization q full).indexed.nodes.size := by
  have hsingle : ∀ node, ((prepareNormalization q full).indexed.decode node).card = 1 → capacity.get node ≤ 1 := by
    intro node hn
    simpa only [hn] using hbounded node
  obtain ⟨final, operations, hrun, hagrees, hcost⟩ :=
    prepared_haltingNormalization_run q full hq hlaminar capacity initial hpc
  refine ⟨final, operations, hrun, hagrees, ?_⟩
  rw [IndexedClosureRAM.readCapacity_eq _ _ _ hagrees]
  exact ⟨prepared_indexed_normalizeAlong_preserves q full hq hlaminar _ capacity,
    prepared_indexed_normalize_normalized q full hq hlaminar capacity hsingle,
    prepared_indexed_normalize_capacity_le_q q full hq hlaminar capacity hsingle, hcost⟩

/-- This version accepts every node support in the original family, as well
as empty eligibility. The finite NodeId lookup is a precomputed input;
parent traversal, zero checks, decrements, tag and HALT are the actual program. -/
theorem prepared_eligible_extension_correct_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hnormalized : IndexedEntry.IsNormalized (prepareNormalization q full).indexed entry)
    (initial : State) (hpc : initial.pc = 0) :
    let cache := (prepareNormalization q full).indexed
    let node := if eligible = ∅ then none else findNodeId cache.nodes eligible
    ∃ final operations,
      IndexedClosureRAM.HaltingRuns (IndexedClosureRAM.extensionROM cache entry node)
        (IndexedClosureRAM.extensionProgram cache.nodes.size 0) initial final operations ∧
      IndexedClosureRAM.decodeResult cache final.heap = IndexedEntry.extend cache eligible entry ∧
      (IndexedClosureRAM.decodeResult cache final.heap).denote cache = usedExtension eligible (entry.denote cache) ∧
      IndexedEntry.IsNormalized cache (IndexedClosureRAM.decodeResult cache final.heap) ∧
      (IndexedClosureRAM.decodeResult cache final.heap).Bounded q ∧
      operations.length ≤ 239 * cache.nodes.size := by
  dsimp only
  let cache := (prepareNormalization q full).indexed
  let node := if eligible = ∅ then none else findNodeId cache.nodes eligible
  have heq : IndexedStaticMetadata.extendAt cache node entry = IndexedEntry.extend cache eligible entry := by
    rw [IndexedStaticMetadata.extendAt_find_eq]
    exact IndexedAncestors.prepared_chainExtend_eq q full hq hlaminar eligible heligible entry
  obtain ⟨final, operations, hrun, hout, hcost⟩ :=
    IndexedClosureRAM.prepared_extension_halting_run q full hq hlaminar entry node initial hpc
  rw [heq] at hout
  refine ⟨final, operations, hrun, hout, ?_⟩
  rw [hout]
  have hn := IndexedEntry.prepared_extend_normalized q full hq hlaminar eligible heligible entry hnormalized
  exact ⟨IndexedEntry.prepared_extend_denote q full hq hlaminar eligible heligible entry hnormalized,
    hn, IndexedEntry.prepared_normalized_bounded q full hq hlaminar _ hn, hcost⟩

/-- Every nonempty support on the given tree has its existing NodeId.
This actual runtime interface accepts that NodeId directly: no support search
is performed by, or hidden in the cost of, the extension program. -/
theorem prepared_tree_node_extension_correct_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (node : (prepareNormalization q full).indexed.NodeId)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hnormalized : IndexedEntry.IsNormalized (prepareNormalization q full).indexed entry)
    (initial : State) (hpc : initial.pc = 0) :
    ∃ final operations,
      IndexedClosureRAM.HaltingRuns
        (IndexedClosureRAM.extensionROM (prepareNormalization q full).indexed entry (some node))
        (IndexedClosureRAM.extensionProgram (prepareNormalization q full).indexed.nodes.size 0) initial final operations ∧
      IndexedClosureRAM.decodeResult (prepareNormalization q full).indexed final.heap =
        IndexedEntry.extend (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.decode node) entry ∧
      (IndexedClosureRAM.decodeResult (prepareNormalization q full).indexed final.heap).denote
        (prepareNormalization q full).indexed =
        usedExtension ((prepareNormalization q full).indexed.decode node) (entry.denote (prepareNormalization q full).indexed) ∧
      IndexedEntry.IsNormalized (prepareNormalization q full).indexed
        (IndexedClosureRAM.decodeResult (prepareNormalization q full).indexed final.heap) ∧
      (IndexedClosureRAM.decodeResult (prepareNormalization q full).indexed final.heap).Bounded q ∧
      operations.length ≤ 239 * (prepareNormalization q full).indexed.nodes.size := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hmem := prepared_indexed_node_mem q full node
  have hne := (nodeFamily_nonempty_nodes full _ hmem).ne_empty
  have hfind : findNodeId (prepareNormalization q full).indexed.nodes
      ((prepareNormalization q full).indexed.decode node) = some node :=
    (findNodeId_eq_some_iff _ (prepared_indexed_nodes_nodup q full) _ node).mpr rfl
  have h := prepared_eligible_extension_correct_run q full hq hlaminar
    ((prepareNormalization q full).indexed.decode node) (Or.inr hmem) entry hnormalized initial hpc
  simpa only [hne, ↓reduceIte, hfind] using h

/-- Full intersection closure, including semantics, normalized-or-VOID output,
original q bound and the complete charged halting run. No result-correctness
or normalization oracle is a premise. -/
theorem prepared_intersection_correct_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (left right : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hleft : IndexedEntry.IsNormalized (prepareNormalization q full).indexed left)
    (initial : State) (hpc : initial.pc = 0) :
    ∃ final operations,
      HaltingRuns (intersectionROM (prepareNormalization q full).indexed left right)
        (intersectionProgram (prepareNormalization q full).indexed) initial final operations ∧
      IndexedClosureRAM.decodeResult (prepareNormalization q full).indexed final.heap =
        IndexedEntry.intersect (prepareNormalization q full).indexed left right ∧
      (IndexedClosureRAM.decodeResult (prepareNormalization q full).indexed final.heap).denote
        (prepareNormalization q full).indexed =
        left.denote (prepareNormalization q full).indexed ∩ right.denote (prepareNormalization q full).indexed ∧
      IndexedEntry.IsNormalized (prepareNormalization q full).indexed
        (IndexedClosureRAM.decodeResult (prepareNormalization q full).indexed final.heap) ∧
      (IndexedClosureRAM.decodeResult (prepareNormalization q full).indexed final.heap).Bounded q ∧
      operations.length ≤ 274 * (prepareNormalization q full).indexed.nodes.size := by
  obtain ⟨final, operations, hrun, hout, hcost⟩ :=
    prepared_intersection_halting_run q full hq hlaminar left right initial hpc
  refine ⟨final, operations, hrun, hout, ?_⟩
  rw [hout]
  have hn := IndexedEntry.prepared_intersect_normalized q full hq hlaminar left right hleft
  exact ⟨IndexedEntry.prepared_intersect_denote q full hq hlaminar left right,
    hn, IndexedEntry.prepared_normalized_bounded q full hq hlaminar _ hn, hcost⟩

/-- Input words for the raw extension compiler in `RawClosureRAM`, accepting a raw
q-bit eligibility set. The entry payload/tag are the only other dynamic input.
Cardinality and singleton-node metadata are prepared once from the same tree;
no eligible-dependent NodeId, rank, decremented coordinate or result appears
in this ROM. Its preprocessing cost remains an A06/A17 obligation. -/
def rawExtensionROM (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (eligible : Finset (Fin q)) : ROM :=
  let cache := (prepareNormalization q full).indexed
  { read := fun region index => match region with
    | .input => if index < cache.nodes.size then payload cache entry index
        else if index = cache.nodes.size then tag cache entry
        else if hi : cache.nodes.size + 1 ≤ index ∧ index < cache.nodes.size + 1 + q then
          if (⟨index - (cache.nodes.size + 1), by omega⟩ : Fin q) ∈ eligible then 1 else 0
        else 0
    | .internal => if hi : index < cache.nodes.size then
          (cache.metadata.cardinalities.get ⟨index, hi⟩)
        else if hi : 2 * cache.nodes.size ≤ index ∧ index < 2 * cache.nodes.size + q then
          (((IndexedStaticMetadata.buildPositive q full hq).toolNodes).get
            ⟨index - 2 * cache.nodes.size, by omega⟩).val + 1
        else 0
    | .children => (IndexedClosureRAM.parentWords cache).getD index 0 }

/-- Complete raw-support closure cost target for the original lemma.
The extension code is selected ONCE per prepared input tree, before the
eligibility set or capacity entry is supplied. Thus its input preparation
cannot hide a support lookup, an extension oracle, or the desired output.
The correct existing NodeId component and intersection machine do not by
themselves prove this stronger raw-support interface; `RawClosureRAM.rawClosureClaims`
proves it with an actual charged input scan and parent-pointer lookup. -/
def RawClosureClaims : Prop :=
  ∃ constant : Nat, 0 < constant ∧
    ∀ (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q), LaminarSchedule full →
      let cache := (prepareNormalization q full).indexed
      (∃ program : List IndexedClosureRAM.Op,
        (IndexedClosureRAM.haltingWords program).length ≤ constant * cache.nodes.size ∧
        ∀ (eligible : Finset (Fin q)), (eligible = ∅ ∨ eligible ∈ nodeFamily full) →
          ∀ entry : IndexedEntry.FixedEntry cache, IndexedEntry.IsNormalized cache entry →
            ∀ initial : State, initial.pc = 0 →
              ∃ final operations,
                IndexedClosureRAM.HaltingRuns (rawExtensionROM q full hq entry eligible)
                  program initial final operations ∧
                IndexedClosureRAM.decodeResult cache final.heap = IndexedEntry.extend cache eligible entry ∧
                (IndexedClosureRAM.decodeResult cache final.heap).denote cache =
                  usedExtension eligible (entry.denote cache) ∧
                IndexedEntry.IsNormalized cache (IndexedClosureRAM.decodeResult cache final.heap) ∧
                (IndexedClosureRAM.decodeResult cache final.heap).Bounded q ∧
                operations.length ≤ constant * cache.nodes.size) ∧
      (∀ left right : IndexedEntry.FixedEntry cache, IndexedEntry.IsNormalized cache left →
        IndexedEntry.IsNormalized cache right → ∀ initial : State, initial.pc = 0 →
          ∃ final operations,
            HaltingRuns (intersectionROM cache left right) (intersectionProgram cache) initial final operations ∧
            IndexedClosureRAM.decodeResult cache final.heap = IndexedEntry.intersect cache left right ∧
            (IndexedClosureRAM.decodeResult cache final.heap).denote cache = left.denote cache ∩ right.denote cache ∧
            IndexedEntry.IsNormalized cache (IndexedClosureRAM.decodeResult cache final.heap) ∧
            (IndexedClosureRAM.decodeResult cache final.heap).Bounded q ∧
            operations.length ≤ constant * cache.nodes.size)

end PaperProofs.Structure.LaminarTree.IndexedIntersectionRAM
