module

public import Structure.PA17_StageMap_001

/-! A17: query counts directly from the original node incidences and the
actual raw used bitmap. No singleton bitmap or count array is supplied.
Every node/tool pair uses ROM loads, select and addition. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryCounts008

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def bitBlock (N q size node tool : Nat) : List Op :=
  [.base (.constant .index (3 + N * q + node * q + tool)), .base (.loadROM .input .old .index),
   .base (.constant .index (4 + N * q + size * q + tool)), .base (.loadROM .input .flag .index),
   .base (.constant .fresh 0), .base (.select .value .flag .old .fresh),
   .base (.add .total .total .value)]

def contribution (rom : ROM) (N q size node tool : Nat) : Nat :=
  if rom.read .input (4 + N * q + size * q + tool) = 0 then 0
  else rom.read .input (3 + N * q + node * q + tool)

def rowCount (rom : ROM) (N q size node : Nat) : Nat :=
  ((List.range q).map (contribution rom N q size node)).sum

def nodeTail (base node : Nat) : List Op :=
  [.base (.constant .index (base + node)), .base (.storeHeap .index .total)]

def nodeBlock (N q size base node : Nat) : List Op :=
  [.base (.constant .total 0)] ++ (List.range q).flatMap (bitBlock N q size node) ++ nodeTail base node

def program (N q size base : Nat) : List Op :=
  (List.range size).flatMap (nodeBlock N q size base)

theorem givenTreeROM_input_length (q : Nat) (full : List (Finset (Fin q))) :
    (givenTreeROM q full).input.length =
      3 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q := by
  simp only [givenTreeROM, List.length_append, List.length_cons, List.length_nil,
    RawIncidenceLaminarRAM.incidence_length, List.length_flatMap, List.length_map,
    List.length_finRange, List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]

theorem queryROM_tree_input_read (q : Nat) (full : List (Finset (Fin q)))
    (stage : Nat) (used : Finset (Fin q)) (address : Nat) (ha : address < (givenTreeROM q full).input.length) :
    (queryROM q full stage used).semantic.read .input address = (givenTreeROM q full).semantic.read .input address := by
  change (((givenTreeROM q full).input ++ [stage]) ++ _).getD address 0 = (givenTreeROM q full).input.getD address 0
  rw [List.getD_append _ _ _ _ (by simp only [List.length_append, List.length_cons, List.length_nil]; omega),
    List.getD_append _ _ _ _ ha]

theorem queryROM_node_bit (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) :
    (queryROM q full stage used).semantic.read .input (3 + full.length * q + node.val * q + tool.val) =
      bit (decide (tool ∈ (prepareNormalization q full).indexed.decode node)) := by
  rw [queryROM_tree_input_read q full stage used _ (by
    rw [givenTreeROM_input_length]
    have hm := Nat.mul_le_mul_right q (Nat.succ_le_of_lt node.isLt)
    rw [Nat.succ_mul] at hm
    omega), UniformTreeMetadataRAM.givenTreeROM_node_bit q full node tool]

theorem queryROM_used_bit (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (tool : Fin q) :
    (queryROM q full stage used).semantic.read .input
      (4 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q + tool.val) =
      bit (decide (tool ∈ used)) := by
  change (((givenTreeROM q full).input ++ [stage]) ++
    (List.finRange q).map (fun tool => bit (decide (tool ∈ used)))).getD _ 0 = _
  rw [List.getD_append_right _ _ _ _ (by
    rw [List.length_append, givenTreeROM_input_length]
    simp only [List.length_cons, List.length_nil]
    omega)]
  rw [List.length_append, givenTreeROM_input_length]
  simp only [List.length_cons, List.length_nil]
  have hoff : 4 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q + tool.val -
      (3 + full.length * q + (prepareNormalization q full).indexed.nodes.size * q + (1 + 0)) = tool.val := by omega
  rw [hoff, List.getD_eq_getElem _ _ (by simpa only [List.length_map, List.length_finRange] using tool.isLt)]
  simp only [List.getElem_map, List.getElem_finRange]
  congr 3

theorem bitBlock_heap (rom : ROM) (N q size node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q size node tool) state).heap = state.heap := rfl

theorem bitBlock_total (rom : ROM) (N q size node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q size node tool) state).register .total =
      state.register .total + contribution rom N q size node tool := rfl

theorem bits_heap (rom : ROM) (N q size node : Nat) (tools : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q size node)) state).heap = state.heap := by
  induction tools generalizing state with
  | nil => rfl
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, bitBlock_heap]

theorem bits_total (rom : ROM) (N q size node : Nat) (tools : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q size node)) state).register .total =
      state.register .total + (tools.map (contribution rom N q size node)).sum := by
  induction tools generalizing state with
  | nil => simp only [List.flatMap_nil, IndexedClosureRAM.execute, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, bitBlock_total]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem prepared_contribution (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q) :
    contribution (queryROM q full stage used).semantic full.length q
      (prepareNormalization q full).indexed.nodes.size node.val tool.val =
      bit (decide (tool ∈ used ∩ (prepareNormalization q full).indexed.decode node)) := by
  rw [contribution, queryROM_used_bit q full stage used tool, queryROM_node_bit q full stage used node tool]
  by_cases hu : tool ∈ used <;> simp [bit, hu]

theorem prepared_rowCount (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId) :
    rowCount (queryROM q full stage used).semantic full.length q
      (prepareNormalization q full).indexed.nodes.size node.val = (IndexedDescent.usedCounts
        (prepareNormalization q full).indexed used).get node := by
  rw [rowCount, IndexedDescent.usedCounts_get]
  have hm : (List.range q).map (contribution (queryROM q full stage used).semantic full.length q
      (prepareNormalization q full).indexed.nodes.size node.val) =
      (List.finRange q).map (fun tool => bit (decide (tool ∈ used ∩ (prepareNormalization q full).indexed.decode node))) := by
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range, List.length_finRange]
    · intro index hi _
      have ht : index < q := by simpa only [List.length_map, List.length_range] using hi
      simp only [List.getElem_map, List.getElem_range, List.getElem_finRange]
      exact prepared_contribution q full stage used node ⟨index, ht⟩
  rw [hm, UniformTreeMetadataRAM.bit_row_card]

theorem nodeTail_heap (rom : ROM) (base node : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (nodeTail base node) state).heap =
      Function.update state.heap (base + node) (state.register .total) := rfl

theorem nodeBlock_heap (rom : ROM) (N q size base node : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (nodeBlock N q size base node) state).heap =
      Function.update state.heap (base + node) (rowCount rom N q size node) := by
  rw [nodeBlock, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append, nodeTail_heap, bits_heap, bits_total]
  have ht : (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state).register .total = 0 := rfl
  rw [ht, Nat.zero_add]
  rfl

theorem nodeBlock_frame (rom : ROM) (N q size base node : Nat) (state : State) (address : Nat)
    (ha : address ≠ base + node) :
    (IndexedClosureRAM.execute rom (nodeBlock N q size base node) state).heap address = state.heap address := by
  rw [nodeBlock_heap, Function.update_of_ne ha]

theorem nodes_frame (rom : ROM) (N q size base : Nat) (nodes : List Nat) (state : State) (address : Nat)
    (ha : ∀ node ∈ nodes, address ≠ base + node) :
    (IndexedClosureRAM.execute rom (nodes.flatMap (nodeBlock N q size base)) state).heap address = state.heap address := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append,
      ih _ (fun other ho => ha other (List.mem_cons_of_mem _ ho)),
      nodeBlock_frame rom N q size base node state address (ha node List.mem_cons_self)]

theorem nodes_value (rom : ROM) (N q size base : Nat) (nodes : List Nat) (node : Nat)
    (hm : node ∈ nodes) (state : State) :
    (IndexedClosureRAM.execute rom (nodes.flatMap (nodeBlock N q size base)) state).heap (base + node) =
      rowCount rom N q size node := by
  induction nodes generalizing state with
  | nil => cases hm
  | cons other later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    by_cases hl : node ∈ later
    · exact ih hl _
    · have heq : node = other := (List.mem_cons.mp hm).resolve_right hl
      rw [nodes_frame _ _ _ _ _ later _ _ (by
        intro next hn he
        exact hl ((Nat.add_left_cancel he) ▸ hn)), ← heq, nodeBlock_heap, Function.update_self]

def CountsCorrect (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (base : Nat) (heap : Nat → Nat) : Prop :=
  ∀ node : (prepareNormalization q full).indexed.NodeId,
    heap (base + node.val) = ((IndexedDescent.usedCounts (prepareNormalization q full).indexed used).get node)

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (base : Nat) (state : State) :
    CountsCorrect q full used base (IndexedClosureRAM.execute (queryROM q full stage used).semantic
      (program full.length q (prepareNormalization q full).indexed.nodes.size base) state).heap := by
  intro node
  rw [program, nodes_value _ _ _ _ _ _ node.val (List.mem_range.mpr node.isLt), prepared_rowCount]

theorem bitBlock_noStore (N q size node tool : Nat) :
    ∀ op ∈ bitBlock N q size node tool, PA17StageMap001.NoStore op := by
  intro op hm
  simp only [bitBlock, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem nodeTail_take_frame (rom : ROM) (base node count : Nat) (state : State)
    (address : Nat) (hframe : address ≠ base + node) :
    (IndexedClosureRAM.execute rom ((nodeTail base node).take count) state).heap address = state.heap address := by
  cases count with
  | zero => rfl
  | succ count =>
    cases count with
    | zero => rfl
    | succ count =>
      have heq : (nodeTail base node).take (count + 1 + 1) = nodeTail base node := by
        simp only [nodeTail, List.take_succ_cons, List.take_nil]
      rw [heq, nodeTail_heap, Function.update_of_ne hframe]

theorem nodeBlock_take_frame (rom : ROM) (N q size base node count : Nat) (state : State)
    (address : Nat) (hframe : address ≠ base + node) :
    (IndexedClosureRAM.execute rom ((nodeBlock N q size base node).take count) state).heap address = state.heap address := by
  rw [nodeBlock, List.take_append, IndexedClosureRAM.execute_append, nodeTail_take_frame _ _ _ _ _ _ hframe]
  apply congrFun
  apply PA17StageMap001.execute_noStore_heap
  intro op hm
  have hs := List.mem_of_mem_take hm
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap] at hs
  rcases hs with rfl | ⟨tool, _, hn⟩
  · trivial
  · exact bitBlock_noStore N q size node tool op hn

theorem nodes_take_frame (rom : ROM) (N q size base : Nat) (nodes : List Nat) (count : Nat) (state : State)
    (address : Nat) (hframe : ∀ node ∈ nodes, address ≠ base + node) :
    (IndexedClosureRAM.execute rom ((nodes.flatMap (nodeBlock N q size base)).take count) state).heap address = state.heap address := by
  induction nodes generalizing count state with
  | nil => simp only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute]
  | cons node later ih =>
    rw [List.flatMap_cons, List.take_append, IndexedClosureRAM.execute_append,
      ih _ _ (fun other ho => hframe other (List.mem_cons_of_mem _ ho)),
      nodeBlock_take_frame _ _ _ _ _ _ _ _ _ (hframe node List.mem_cons_self)]

theorem program_take_frame (rom : ROM) (N q size base count : Nat) (state : State)
    (address : Nat) (hframe : address < base ∨ base + size ≤ address) :
    (IndexedClosureRAM.execute rom ((program N q size base).take count) state).heap address = state.heap address := by
  exact nodes_take_frame rom N q size base (List.range size) count state address (by
    intro node hm
    have hn := List.mem_range.mp hm
    omega)

def nodeRead (N q size base node : Nat) : List Op :=
  [.base (.constant .total 0)] ++ (List.range q).flatMap (bitBlock N q size node) ++
    [.base (.constant .index (base + node))]

theorem nodeBlock_split (N q size base node : Nat) :
    nodeBlock N q size base node = nodeRead N q size base node ++ [.base (.storeHeap .index .total)] := by
  simp [nodeBlock, nodeTail, nodeRead, List.append_assoc]

theorem nodeRead_noStore (N q size base node : Nat) :
    ∀ op ∈ nodeRead N q size base node, PA17StageMap001.NoStore op := by
  intro op hm
  simp only [nodeRead, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap] at hm
  rcases hm with (rfl | ⟨tool, _, hm⟩) | rfl
  · trivial
  · exact bitBlock_noStore N q size node tool op hm
  · trivial

theorem nodeBlock_prefix_heap (rom : ROM) (N q size base node count : Nat)
    (hc : count < (nodeBlock N q size base node).length) (state : State) :
    (IndexedClosureRAM.execute rom ((nodeBlock N q size base node).take count) state).heap = state.heap := by
  have hl : (nodeBlock N q size base node).length = (nodeRead N q size base node).length + 1 := by
    rw [nodeBlock_split, List.length_append]
    rfl
  rw [nodeBlock_split, List.take_append_of_le_length (show count ≤ (nodeRead N q size base node).length from by omega)]
  exact PA17StageMap001.execute_noStore_heap rom _
    (fun op hm => nodeRead_noStore N q size base node op (List.mem_of_mem_take hm)) state

theorem nodeBlock_take_capacity (rom : ROM) (N q size base node capWords count : Nat)
    (hv : rowCount rom N q size node ≤ q) (state : State)
    (hcap : CapacityPrefixBounded q capWords state.heap) :
    CapacityPrefixBounded q capWords (IndexedClosureRAM.execute rom ((nodeBlock N q size base node).take count) state).heap := by
  by_cases hc : count < (nodeBlock N q size base node).length
  · rw [nodeBlock_prefix_heap rom N q size base node count hc state]
    exact hcap
  · rw [List.take_of_length_le (by omega), nodeBlock_heap]
    intro address ha
    by_cases heq : address = base + node
    · rw [heq, Function.update_self]
      exact hv
    · rw [Function.update_of_ne heq]
      exact hcap address ha

theorem nodes_take_capacity (rom : ROM) (N q size base capWords : Nat) (nodes : List Nat)
    (hvalues : ∀ node ∈ nodes, rowCount rom N q size node ≤ q) (count : Nat) (state : State)
    (hcap : CapacityPrefixBounded q capWords state.heap) :
    CapacityPrefixBounded q capWords
      (IndexedClosureRAM.execute rom ((nodes.flatMap (nodeBlock N q size base)).take count) state).heap := by
  induction nodes generalizing count state with
  | nil => simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hcap
  | cons node later ih =>
    rw [List.flatMap_cons, List.take_append, IndexedClosureRAM.execute_append]
    exact ih (fun other ho => hvalues other (List.mem_cons_of_mem _ ho)) _ _
      (nodeBlock_take_capacity rom N q size base node capWords count (hvalues node List.mem_cons_self) state hcap)

theorem prepared_rowCount_le (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId) :
    rowCount (queryROM q full stage used).semantic full.length q
      (prepareNormalization q full).indexed.nodes.size node.val ≤ q := by
  rw [prepared_rowCount, IndexedDescent.usedCounts_get]
  simpa only [Fintype.card_fin] using Finset.card_le_univ (used ∩ (prepareNormalization q full).indexed.decode node)

theorem prepared_program_capacityThroughout (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (used : Finset (Fin q)) (base capWords : Nat) (state : State)
    (hcap : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords (queryROM q full stage used)
      (program full.length q (prepareNormalization q full).indexed.nodes.size base) state := by
  intro count _
  exact nodes_take_capacity _ _ _ _ _ _ (List.range (prepareNormalization q full).indexed.nodes.size)
    (fun node hm => prepared_rowCount_le q full stage used ⟨node, List.mem_range.mp hm⟩) count state hcap

theorem program_length (N q size base : Nat) : (program N q size base).length = (7 * q + 3) * size := by
  have hb (node tool : Nat) : (bitBlock N q size node tool).length = 7 := rfl
  have ht (node : Nat) : (nodeTail base node).length = 2 := rfl
  have hn (node : Nat) : (nodeBlock N q size base node).length = 7 * q + 3 := by
    simp only [nodeBlock, List.length_append, List.length_cons, List.length_nil, List.length_flatMap, hb, ht,
      List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
    omega
  simp only [program, List.length_flatMap, hn, List.map_const', List.sum_replicate,
    List.length_range, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem program_trace_length (N q size base : Nat) : (trace (program N q size base)).length = (69 * q + 27) * size := by
  have hb (node tool : Nat) : (trace (bitBlock N q size node tool)).length = 69 := rfl
  have ht (node : Nat) : (trace (nodeTail base node)).length = 19 := rfl
  have hi : (trace [.base (.constant .total 0)]).length = 8 := rfl
  have hn (node : Nat) : (trace (nodeBlock N q size base node)).length = 69 * q + 27 := by
    rw [nodeBlock, trace_append, trace_append, List.length_append, List.length_append, hi, ht,
      UniformNormalizationRAM.trace_flatMap_length]
    simp only [hb, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
    omega
  rw [program, UniformNormalizationRAM.trace_flatMap_length]
  simp only [hn, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem program_codeWords_length (N q size base : Nat) :
    (haltingWords (program N q size base)).length = (35 * q + 15) * size + 5 := by
  rw [haltingWords_length, program_length]
  ring

theorem program_trace_le (N q size base : Nat) (hsize : 0 < size) :
    (trace (program N q size base) ++ haltTrace).length ≤ 102 * queryWork q size := by
  rw [List.length_append, program_trace_length, haltTrace_length]
  dsimp [queryWork]
  nlinarith

theorem program_trace_pos_le (N q size base : Nat) (hq : 0 < q) (hsize : 0 < size) :
    (trace (program N q size base) ++ haltTrace).length ≤ 102 * q * size := by
  rw [List.length_append, program_trace_length, haltTrace_length]
  have hm : size ≤ q * size := Nat.le_mul_of_pos_left size hq
  nlinarith

theorem program_code_le (N q size base : Nat) (hsize : 0 < size) :
    (haltingWords (program N q size base)).length ≤ 55 * queryWork q size := by
  rw [program_codeWords_length]
  dsimp [queryWork]
  nlinarith

theorem totalQueryCost_le (N q size base : Nat) (hsize : 0 < size) :
    totalQueryCost q (program N q size base) ≤ 160 * queryWork q size := by
  rw [totalQueryCost, program_codeWords_length, List.length_append, program_trace_length, haltTrace_length]
  dsimp [queryWork]
  nlinarith

theorem prepared_halting_run (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (base : Nat) (state : State) (hpc : state.pc = 0) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ∃ final operations,
      HaltingRuns (queryROM q full stage used).semantic (program full.length q size base) state final operations ∧
      CountsCorrect q full used base final.heap ∧
      (∀ address, address < base ∨ base + size ≤ address → final.heap address = state.heap address) ∧
      operations.length ≤ 102 * queryWork q size := by
  intro size
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  refine ⟨_, _, IndexedClosureRAM.execute_halts _ _ state hpc,
    prepared_program_correct q full stage used base state, ?_, program_trace_le _ _ _ _ hsize⟩
  intro address ha
  simpa only [List.take_length] using program_take_frame (queryROM q full stage used).semantic full.length q size base
    (program full.length q size base).length state address ha

end PaperProofs.Structure.LaminarTree.PA17QueryCounts008
