module

public import PaperProofs.Structure.UniformNormalizationRAM
public import PaperProofs.Structure.RawIncidenceLaminarRAM

/-! Dimension-only construction of cardinality, sentinel-parent and internal
metadata from the original given-tree ROM. Capacities, cardinalities and flags
are computed or loaded during actual RAM execution, never placed in code. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.UniformTreeMetadataRAM

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def cardAddress (base node : Nat) : Nat := base + node
def parentAddress (size base encoded : Nat) : Nat := base + size + encoded
def internalAddress (size base node : Nat) : Nat := base + 2 * size + 1 + node

def readBit (N q node tool : Nat) : List Op :=
  [.base (.constant .index (3 + N * q + node * q + tool)), .base (.loadROM .input .value .index),
    .base (.add .total .total .value)]

def nodeTail (size base node : Nat) : List Op :=
  [.base (.constant .index (cardAddress base node)), .base (.storeHeap .index .total),
   .base (.constant .index node), .base (.loadROM .internal .value .index),
   .base (.constant .index (parentAddress size base (node + 1))), .base (.storeHeap .index .value),
   .base (.constant .index (size + node)), .base (.loadROM .internal .flag .index),
   .base (.constant .old 0), .base (.constant .fresh 1), .base (.select .value .flag .fresh .old),
   .base (.constant .index (internalAddress size base node)), .base (.storeHeap .index .value)]

def nodeBlock (N q size base node : Nat) : List Op :=
  [.base (.constant .total 0)] ++ (List.range q).flatMap (readBit N q node) ++ nodeTail size base node

def program (N q size base : Nat) : List Op :=
  UniformNormalizationRAM.clearBlock (parentAddress size base 0) ++
    (List.range size).flatMap (nodeBlock N q size base)

def rowSum (rom : ROM) (N q node : Nat) : Nat :=
  ((List.range q).map (fun tool => rom.read .input (3 + N * q + node * q + tool))).sum

def internalValue (rom : ROM) (size node : Nat) : Nat := if rom.read .internal (size + node) = 0 then 0 else 1

theorem readBit_heap (rom : ROM) (N q node tool : Nat) (state : State) :
    (execute rom (readBit N q node tool) state).heap = state.heap := rfl

theorem readBit_total (rom : ROM) (N q node tool : Nat) (state : State) :
    (execute rom (readBit N q node tool) state).register .total =
      state.register .total + rom.read .input (3 + N * q + node * q + tool) := rfl

theorem readBits_heap (rom : ROM) (N q node : Nat) (tools : List Nat) (state : State) :
    (execute rom (tools.flatMap (readBit N q node)) state).heap = state.heap := by
  induction tools generalizing state with
  | nil => rfl
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, readBit_heap]

theorem readBits_total (rom : ROM) (N q node : Nat) (tools : List Nat) (state : State) :
    (execute rom (tools.flatMap (readBit N q node)) state).register .total =
      state.register .total + (tools.map (fun tool => rom.read .input (3 + N * q + node * q + tool))).sum := by
  induction tools generalizing state with
  | nil => simp only [List.flatMap_nil, IndexedClosureRAM.execute, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, readBit_total]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem nodeTail_heap (rom : ROM) (size base node : Nat) (state : State) :
    (execute rom (nodeTail size base node) state).heap =
      Function.update
        (Function.update (Function.update state.heap (cardAddress base node) (state.register .total))
          (parentAddress size base (node + 1)) (rom.read .internal node))
        (internalAddress size base node) (internalValue rom size node) := rfl

theorem nodeBlock_heap (rom : ROM) (N q size base node : Nat) (state : State) :
    (execute rom (nodeBlock N q size base node) state).heap =
      Function.update
        (Function.update (Function.update state.heap (cardAddress base node) (rowSum rom N q node))
          (parentAddress size base (node + 1)) (rom.read .internal node))
        (internalAddress size base node) (internalValue rom size node) := by
  rw [nodeBlock, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append, nodeTail_heap,
    readBits_heap, readBits_total]
  have hh : (execute rom [.base (.constant .total 0)] state).heap = state.heap := rfl
  have ht : (execute rom [.base (.constant .total 0)] state).register .total = 0 := rfl
  rw [hh, ht, Nat.zero_add]
  rfl

theorem nodeBlock_values (rom : ROM) (N q size base node : Nat) (hn : node < size) (state : State) :
    let result := execute rom (nodeBlock N q size base node) state
    result.heap (cardAddress base node) = rowSum rom N q node ∧
      result.heap (parentAddress size base (node + 1)) = rom.read .internal node ∧
      result.heap (internalAddress size base node) = internalValue rom size node := by
  dsimp only
  rw [nodeBlock_heap]
  have hcp : cardAddress base node ≠ parentAddress size base (node + 1) := by
    dsimp [cardAddress, parentAddress]; omega
  have hci : cardAddress base node ≠ internalAddress size base node := by
    dsimp [cardAddress, internalAddress]; omega
  have hpi : parentAddress size base (node + 1) ≠ internalAddress size base node := by
    dsimp [parentAddress, internalAddress]; omega
  simp only [Function.update_of_ne hci, Function.update_of_ne hcp,
    Function.update_of_ne hpi, Function.update_self, and_self]

def OutsideNode (size base address node : Nat) : Prop :=
  address ≠ cardAddress base node ∧ address ≠ parentAddress size base (node + 1) ∧
    address ≠ internalAddress size base node

theorem nodeBlock_frame (rom : ROM) (N q size base node : Nat) (state : State)
    (address : Nat) (hframe : OutsideNode size base address node) :
    (execute rom (nodeBlock N q size base node) state).heap address = state.heap address := by
  rw [nodeBlock_heap, Function.update_of_ne hframe.2.2, Function.update_of_ne hframe.2.1,
    Function.update_of_ne hframe.1]

theorem nodes_frame (rom : ROM) (N q size base : Nat) (nodes : List Nat) (state : State)
    (address : Nat) (hframe : ∀ node ∈ nodes, OutsideNode size base address node) :
    (execute rom (nodes.flatMap (nodeBlock N q size base)) state).heap address = state.heap address := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append,
      ih _ (fun other ho => hframe other (List.mem_cons_of_mem _ ho)), nodeBlock_frame rom N q size base node state address
        (hframe node List.mem_cons_self)]

theorem outside_other (size base node other : Nat) (hn : node < size) (ho : other < size) (hne : node ≠ other) :
    OutsideNode size base (cardAddress base node) other ∧
      OutsideNode size base (parentAddress size base (node + 1)) other ∧
      OutsideNode size base (internalAddress size base node) other := by
  dsimp [OutsideNode, cardAddress, parentAddress, internalAddress]
  omega

theorem nodes_values (rom : ROM) (N q size base : Nat) (nodes : List Nat)
    (hnodes : ∀ node ∈ nodes, node < size) (state : State) (target : Nat) (htarget : target ∈ nodes) :
    let result := execute rom (nodes.flatMap (nodeBlock N q size base)) state
    result.heap (cardAddress base target) = rowSum rom N q target ∧
      result.heap (parentAddress size base (target + 1)) = rom.read .internal target ∧
      result.heap (internalAddress size base target) = internalValue rom size target := by
  induction nodes generalizing state with
  | nil => cases htarget
  | cons node later ih =>
    dsimp only
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    by_cases ht : target ∈ later
    · exact ih (fun other ho => hnodes other (List.mem_cons_of_mem _ ho)) _ ht
    · have heq : target = node := (List.mem_cons.mp htarget).resolve_right ht
      subst target
      have ho (other : Nat) (hm : other ∈ later) := outside_other size base node other
        (hnodes node List.mem_cons_self) (hnodes other (List.mem_cons_of_mem _ hm))
        (fun hh => ht (hh ▸ hm))
      rw [nodes_frame rom N q size base later _ _ (fun other hm => (ho other hm).1),
        nodes_frame rom N q size base later _ _ (fun other hm => (ho other hm).2.1),
        nodes_frame rom N q size base later _ _ (fun other hm => (ho other hm).2.2)]
      exact nodeBlock_values rom N q size base node (hnodes node List.mem_cons_self) state

theorem program_values (rom : ROM) (N q size base : Nat) (state : State) (node : Nat) (hn : node < size) :
    let result := execute rom (program N q size base) state
    result.heap (cardAddress base node) = rowSum rom N q node ∧
      result.heap (parentAddress size base (node + 1)) = rom.read .internal node ∧
      result.heap (internalAddress size base node) = internalValue rom size node := by
  dsimp only
  rw [program, IndexedClosureRAM.execute_append]
  exact nodes_values rom N q size base (List.range size) (fun _ hm => List.mem_range.mp hm)
    _ node (List.mem_range.mpr hn)

theorem program_parent_zero (rom : ROM) (N q size base : Nat) (state : State) :
    (execute rom (program N q size base) state).heap (parentAddress size base 0) = 0 := by
  rw [program, IndexedClosureRAM.execute_append,
    nodes_frame rom N q size base _ _ _ (by
      intro node hn
      have hnode := List.mem_range.mp hn
      dsimp [OutsideNode, parentAddress, cardAddress, internalAddress]
      omega), UniformNormalizationRAM.execute_clearBlock_heap, Function.update_self]

theorem program_frame (rom : ROM) (N q size base : Nat) (state : State) (address : Nat)
    (hframe : address < base ∨ base + 3 * size < address) :
    (execute rom (program N q size base) state).heap address = state.heap address := by
  rw [program, IndexedClosureRAM.execute_append,
    nodes_frame rom N q size base _ _ address (by
      intro node hn
      have hnode := List.mem_range.mp hn
      dsimp [OutsideNode, parentAddress, cardAddress, internalAddress]
      omega), UniformNormalizationRAM.execute_clearBlock_heap, Function.update_of_ne (by
        dsimp [parentAddress]
        omega)]

theorem program_length (N q size base : Nat) :
    (program N q size base).length = (3 * q + 14) * size + 3 := by
  have hr (node tool : Nat) : (readBit N q node tool).length = 3 := rfl
  have ht (node : Nat) : (nodeTail size base node).length = 13 := rfl
  have hn (node : Nat) : (nodeBlock N q size base node).length = 3 * q + 14 := by
    simp only [nodeBlock, List.length_append, List.length_cons, List.length_nil,
      List.length_flatMap, hr, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul, ht]
    omega
  have hc : (UniformNormalizationRAM.clearBlock (parentAddress size base 0)).length = 3 := rfl
  simp only [program, List.length_append, hc, List.length_flatMap, hn, List.map_const', List.sum_replicate,
    List.length_range, Nat.nsmul_eq_mul]
  rw [Nat.mul_comm size (3 * q + 14)]
  omega

theorem program_trace_length (N q size base : Nat) :
    (trace (program N q size base)).length = (30 * q + 131) * size + 27 := by
  have hr (node tool : Nat) : (trace (readBit N q node tool)).length = 30 := rfl
  have ht (node : Nat) : (trace (nodeTail size base node)).length = 123 := rfl
  have hh : (trace [.base (.constant .total 0)]).length = 8 := rfl
  have hn (node : Nat) : (trace (nodeBlock N q size base node)).length = 30 * q + 131 := by
    rw [nodeBlock, IndexedClosureRAM.trace_append, IndexedClosureRAM.trace_append,
      List.length_append, List.length_append, hh, ht, UniformNormalizationRAM.trace_flatMap_length]
    simp only [hr, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
    omega
  have hc : (trace (UniformNormalizationRAM.clearBlock (parentAddress size base 0))).length = 27 := rfl
  rw [program, IndexedClosureRAM.trace_append, List.length_append, hc, UniformNormalizationRAM.trace_flatMap_length]
  simp only [hn, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  rw [Nat.mul_comm size (30 * q + 131)]
  omega

theorem nodeRows_eq_incidence (q : Nat) (full : List (Finset (Fin q))) :
    let cache := (prepareNormalization q full).indexed
    (List.finRange cache.nodes.size).flatMap (fun node => (List.finRange q).map
      (fun tool => bit (decide (tool ∈ cache.decode node)))) = incidence cache.nodes.toList := by
  intro cache
  have hn : (List.finRange cache.nodes.size).map cache.decode = cache.nodes.toList := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_finRange, Array.length_toList]
    · intro index hi _
      simp only [List.getElem_map, List.getElem_finRange, IndexedNodeCache.decode, Array.getElem_toList]
      congr 1
  rw [← hn, incidence, List.flatMap_map]

theorem givenTreeROM_node_bit (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) :
    (givenTreeROM q full).semantic.read .input (3 + full.length * q + node.val * q + tool.val) =
      bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) := by
  let cache := (prepareNormalization q full).indexed
  change (([full.length, q, cache.nodes.size] ++ incidence full) ++
    (List.finRange cache.nodes.size).flatMap (fun node => (List.finRange q).map
      (fun tool => bit (decide (tool ∈ cache.decode node))))).getD
        (3 + full.length * q + node.val * q + tool.val) 0 = _
  rw [nodeRows_eq_incidence q full, List.getD_append_right _ _ _ _ (by
    simp only [List.length_append, List.length_cons, List.length_nil, RawIncidenceLaminarRAM.incidence_length]
    omega)]
  simp only [List.length_append, List.length_cons, List.length_nil, RawIncidenceLaminarRAM.incidence_length]
  have hoff : 3 + full.length * q + node.val * q + tool.val - (3 + full.length * q) = node.val * q + tool.val := by omega
  rw [hoff, RawIncidenceLaminarRAM.incidence_getD q cache.nodes.toList node.val
    (by simpa only [Array.length_toList] using node.isLt) tool]
  rfl

theorem bit_row_card (q : Nat) (support : Finset (Fin q)) :
    ((List.finRange q).map (fun tool => bit (decide (tool ∈ support)))).sum = support.card := by
  classical
  rw [← List.sum_toFinset _ (List.nodup_finRange q), List.toFinset_finRange]
  simp [bit]

theorem rowSum_eq_card (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) :
    rowSum (givenTreeROM q full).semantic full.length q node.val =
      ((prepareNormalization q full).indexed.decode node).card := by
  rw [rowSum]
  have hm : (List.range q).map (fun tool => (givenTreeROM q full).semantic.read .input
        (3 + full.length * q + node.val * q + tool)) =
      (List.finRange q).map (fun tool => bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node))) := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_finRange]
    · intro index hi _
      have hiq : index < q := by simpa only [List.length_map, List.length_range] using hi
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
      exact givenTreeROM_node_bit q full node ⟨index, hiq⟩
  rw [hm, bit_row_card]

theorem prepared_program_values (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (base : Nat) (state : State)
    (node : (prepareNormalization q full).indexed.NodeId) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size base) state
    result.heap (cardAddress base node.val) = (cache.decode node).card ∧
      result.heap (parentAddress cache.nodes.size base (node.val + 1)) = encodedNode cache (cache.parents.get node) ∧
      result.heap (internalAddress cache.nodes.size base node.val) = if 1 < (cache.decode node).card then 1 else 0 := by
  dsimp only
  have hv := program_values (givenTreeROM q full).semantic full.length q
    (prepareNormalization q full).indexed.nodes.size base state node.val node.isLt
  rw [rowSum_eq_card q full node, UniformNormalizationRAM.givenTreeROM_parent q full node] at hv
  refine ⟨hv.1, hv.2.1, hv.2.2.trans ?_⟩
  have hflag := (UniformNormalizationRAM.givenTreeROM_tree q full hq hlaminar).2 node
  by_cases hi : 1 < ((prepareNormalization q full).indexed.decode node).card
  · simp only [internalValue, hflag.mpr hi, hi, ite_false, ite_true]
  · have hz : (givenTreeROM q full).semantic.read .internal
        ((prepareNormalization q full).indexed.nodes.size + node.val) = 0 :=
      not_ne_iff.mp (fun hh => hi (hflag.mp hh))
    simp only [internalValue, hz, hi, ite_true, ite_false]

def MetadataCorrect (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (heap : Nat → Nat) : Prop :=
  let cache := (prepareNormalization q full).indexed
  heap (parentAddress cache.nodes.size base 0) = 0 ∧
    ∀ node : cache.NodeId,
      heap (cardAddress base node.val) = (cache.decode node).card ∧
        heap (parentAddress cache.nodes.size base (node.val + 1)) = encodedNode cache (cache.parents.get node) ∧
        heap (internalAddress cache.nodes.size base node.val) = if 1 < (cache.decode node).card then 1 else 0

theorem prepared_program_metadata (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (base : Nat) (state : State) :
    MetadataCorrect q full base (execute (givenTreeROM q full).semantic
      (program full.length q (prepareNormalization q full).indexed.nodes.size base) state).heap :=
  ⟨program_parent_zero _ _ _ _ _ state, prepared_program_values q full hq hlaminar base state⟩

theorem metadata_parentWord (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (heap : Nat → Nat)
    (hmetadata : MetadataCorrect q full base heap) (index : Nat)
    (hindex : index ≤ (prepareNormalization q full).indexed.nodes.size) :
    heap (parentAddress (prepareNormalization q full).indexed.nodes.size base index) =
      parentWord (prepareNormalization q full).indexed index := by
  cases index with
  | zero => simpa only [parentWord_zero] using hmetadata.1
  | succ index =>
    let node : (prepareNormalization q full).indexed.NodeId := ⟨index, by omega⟩
    exact ((hmetadata.2 node).2.1).trans (parentWord_node _ node).symm

theorem metadata_card_bound (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (heap : Nat → Nat)
    (hmetadata : MetadataCorrect q full base heap) (node : (prepareNormalization q full).indexed.NodeId) :
    heap (cardAddress base node.val) ≤ q := by
  rw [(hmetadata.2 node).1]
  simpa only [Fintype.card_fin] using Finset.card_le_univ ((prepareNormalization q full).indexed.decode node)

theorem program_codeWords_length (N q size base : Nat) :
    (haltingWords (program N q size base)).length = (15 * q + 70) * size + 20 := by
  rw [IndexedClosureRAM.haltingWords, List.length_append, IndexedClosureRAM.programWords_length, program_length]
  have hh : haltWords.toArray.toList.length = 5 := rfl
  rw [hh]
  simp only [Nat.mul_add, Nat.add_mul, Nat.mul_assoc]
  omega

theorem prepared_program_halting_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (base : Nat) (state : State) (hpc : state.pc = 0) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ∃ final operations,
      HaltingRuns (givenTreeROM q full).semantic (program full.length q size base) state final operations ∧
      MetadataCorrect q full base final.heap ∧
      (∀ address : Nat, address < base ∨ base + 3 * size < address → final.heap address = state.heap address) ∧
      operations.length ≤ 164 * (q * size + size) := by
  intro size
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < size := by have := root.isLt; omega
  refine ⟨_, _, IndexedClosureRAM.execute_halts _ _ state hpc,
    prepared_program_metadata q full hq hlaminar base state, ?_, ?_⟩
  · intro address hframe
    exact program_frame _ _ _ _ _ state address hframe
  · rw [List.length_append, program_trace_length, IndexedClosureRAM.haltTrace_length]
    simp only [Nat.add_mul, Nat.mul_assoc, Nat.mul_add]
    omega

end PaperProofs.Structure.LaminarTree.UniformTreeMetadataRAM
