module

public import Structure.PA17_MetadataAssembly_003
import Mathlib.Tactic.IntervalCases

/-! A17: actual node-to-singleton-tool labels, computed from original node
incidence rows. A runtime counter tests cardinality one; no semantic card,
leaf lookup or tool answer is an input. The unique singleton removes min' tie
dependence in IndexedDescent.leafTools. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17LeafLabels005

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def encodeTool {q : Nat} : Option (Fin q) → Nat
  | none => 0
  | some tool => tool.val + 1

def readValue (rom : ROM) (N q node tool : Nat) : Nat :=
  rom.read .input (3 + N * q + node * q + tool)

def bitBlock (N q node tool : Nat) : List Op :=
  [.base (.constant .index (3 + N * q + node * q + tool)),
   .base (.loadROM .input .flag .index), .base (.constant .old (tool + 1)),
   .base (.select .value .flag .old .value), .base (.add .total .total .flag)]

def nodeTail (base node : Nat) : List Op :=
  [.base (.constant .old 1), .subtract .flag .total .old, .subtract .index .old .total,
   .base (.add .flag .flag .index), .base (.constant .old 0),
   .base (.select .value .flag .old .value),
   .base (.constant .index (base + node)), .base (.storeHeap .index .value)]

def nodeBlock (N q base node : Nat) : List Op :=
  [.base (.constant .total 0), .base (.constant .value 0)] ++
    (List.range q).flatMap (bitBlock N q node) ++ nodeTail base node

def program (N q size base : Nat) : List Op :=
  (List.range size).flatMap (nodeBlock N q base)

theorem bitBlock_heap (rom : ROM) (N q node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q node tool) state).heap = state.heap := rfl

theorem bitBlock_total (rom : ROM) (N q node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q node tool) state).register .total =
      state.register .total + readValue rom N q node tool := rfl

theorem bitBlock_value (rom : ROM) (N q node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q node tool) state).register .value =
      if readValue rom N q node tool = 0 then state.register .value else tool + 1 := rfl

theorem bits_heap (rom : ROM) (N q node : Nat) (tools : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q node)) state).heap = state.heap := by
  induction tools generalizing state with
  | nil => rfl
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, bitBlock_heap]

theorem bits_total (rom : ROM) (N q node : Nat) (tools : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q node)) state).register .total =
      state.register .total + (tools.map (readValue rom N q node)).sum := by
  induction tools generalizing state with
  | nil => simp only [List.flatMap_nil, IndexedClosureRAM.execute, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, bitBlock_total]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem bits_value_none (rom : ROM) (N q node : Nat) (tools : List Nat)
    (hzero : ∀ tool ∈ tools, readValue rom N q node tool = 0) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q node)) state).register .value = state.register .value := by
  induction tools generalizing state with
  | nil => rfl
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append,
      ih (fun other ho => hzero other (List.mem_cons_of_mem _ ho)), bitBlock_value,
      ite_eq_left (hzero tool List.mem_cons_self)]

theorem bits_value_some (rom : ROM) (N q node : Nat) (tools : List Nat)
    (target : Nat) (hmem : target ∈ tools) (hnzero : readValue rom N q node target ≠ 0)
    (hunique : ∀ tool ∈ tools, readValue rom N q node tool ≠ 0 → tool = target) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q node)) state).register .value = target + 1 := by
  induction tools generalizing state with
  | nil => cases hmem
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    by_cases htl : target ∈ later
    · exact ih htl (fun other ho => hunique other (List.mem_cons_of_mem _ ho)) _
    · have heq : target = tool := (List.mem_cons.mp hmem).resolve_right htl
      rw [bits_value_none rom N q node later (by
        intro other ho
        by_contra hne
        have hs := hunique other (List.mem_cons_of_mem _ ho) hne
        exact htl (hs ▸ ho)), bitBlock_value, ← heq, ite_eq_right hnzero]

theorem nodeTail_heap (rom : ROM) (base node : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (nodeTail base node) state).heap =
      Function.update state.heap (base + node)
        (if state.register .total = 1 then state.register .value else 0) := by
  change Function.update state.heap (base + node)
    (if (state.register .total - 1) + (1 - state.register .total) = 0 then state.register .value else 0) = _
  have hz : (state.register .total - 1) + (1 - state.register .total) = 0 ↔ state.register .total = 1 := by omega
  simp only [hz]

theorem nodeBlock_heap (rom : ROM) (N q base node : Nat) (state : State) :
    let start := IndexedClosureRAM.execute rom [.base (.constant .total 0), .base (.constant .value 0)] state
    let middle := IndexedClosureRAM.execute rom ((List.range q).flatMap (bitBlock N q node)) start
    (IndexedClosureRAM.execute rom (nodeBlock N q base node) state).heap =
      Function.update state.heap (base + node)
        (if middle.register .total = 1 then middle.register .value else 0) := by
  intro start middle
  rw [nodeBlock, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append, nodeTail_heap, bits_heap]
  rfl

theorem prepared_bits_total (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) (state : State) :
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      ((List.range q).flatMap (bitBlock full.length q node.val)) state).register .total =
      state.register .total + ((prepareNormalization q full).indexed.decode node).card := by
  rw [bits_total]
  exact congrArg (state.register .total + ·) (UniformTreeMetadataRAM.rowSum_eq_card q full node)

theorem prepared_bits_value_singleton (q : Nat) (full : List (Finset (Fin q)))
    (node : (prepareNormalization q full).indexed.NodeId) (tool : Fin q)
    (hsingle : (prepareNormalization q full).indexed.decode node = {tool}) (state : State) :
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      ((List.range q).flatMap (bitBlock full.length q node.val)) state).register .value = tool.val + 1 := by
  apply bits_value_some _ _ _ _ _ tool.val (List.mem_range.mpr tool.isLt)
  · change (givenTreeROM q full).semantic.read .input _ ≠ 0
    rw [UniformTreeMetadataRAM.givenTreeROM_node_bit q full node tool, hsingle]
    simp [bit]
  · intro other ho hne
    have hother : other < q := List.mem_range.mp ho
    have hn : (⟨other, hother⟩ : Fin q) ∈ (prepareNormalization q full).indexed.decode node := by
      by_contra hn
      apply hne
      change (givenTreeROM q full).semantic.read .input _ = 0
      rw [UniformTreeMetadataRAM.givenTreeROM_node_bit q full node ⟨other, hother⟩]
      simp [bit, hn]
    rw [hsingle, Finset.mem_singleton] at hn
    exact congrArg Fin.val hn

theorem prepared_nodeBlock_result (q : Nat) (full : List (Finset (Fin q))) (base : Nat)
    (node : (prepareNormalization q full).indexed.NodeId) (state : State) :
    let cache := (prepareNormalization q full).indexed
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic (nodeBlock full.length q base node.val) state).heap
      (base + node.val) = encodeTool ((IndexedDescent.leafTools cache).get node) := by
  intro cache
  rw [nodeBlock_heap, Function.update_self]
  let start := IndexedClosureRAM.execute (givenTreeROM q full).semantic
    [.base (.constant .total 0), .base (.constant .value 0)] state
  have hs : start.register .total = 0 := rfl
  change (if (IndexedClosureRAM.execute _ _ start).register .total = 1 then _ else 0) = _
  rw [prepared_bits_total q full node start, hs, Nat.zero_add, IndexedDescent.leafTools_get]
  cases ht : IndexedDescent.singletonTool (cache.decode node) with
  | none =>
    have hc : (cache.decode node).card ≠ 1 := by
      intro hc
      obtain ⟨tool, hsingle⟩ := Finset.card_eq_one.mp hc
      rw [hsingle, IndexedDescent.singletonTool_singleton] at ht
      cases ht
    rw [ite_eq_right hc]
    rfl
  | some tool =>
    have hsingle := IndexedDescent.singletonTool_spec (cache.decode node) tool ht
    have hc : (cache.decode node).card = 1 := by rw [hsingle]; exact Finset.card_singleton tool
    rw [ite_eq_left hc, prepared_bits_value_singleton q full node tool hsingle start]
    rfl

theorem nodeBlock_frame (rom : ROM) (N q base node : Nat) (state : State) (address : Nat)
    (ha : address ≠ base + node) :
    (IndexedClosureRAM.execute rom (nodeBlock N q base node) state).heap address = state.heap address := by
  rw [nodeBlock_heap, Function.update_of_ne ha]

theorem nodes_frame (rom : ROM) (N q base : Nat) (nodes : List Nat) (state : State) (address : Nat)
    (ha : ∀ node ∈ nodes, address ≠ base + node) :
    (IndexedClosureRAM.execute rom (nodes.flatMap (nodeBlock N q base)) state).heap address = state.heap address := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append,
      ih _ (fun other ho => ha other (List.mem_cons_of_mem _ ho)),
      nodeBlock_frame rom N q base node state address (ha node List.mem_cons_self)]

theorem prepared_nodes_result (q : Nat) (full : List (Finset (Fin q))) (base : Nat)
    (nodes : List Nat) (node : (prepareNormalization q full).indexed.NodeId)
    (hm : node.val ∈ nodes) (state : State) :
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic (nodes.flatMap (nodeBlock full.length q base)) state).heap
      (base + node.val) = encodeTool ((IndexedDescent.leafTools (prepareNormalization q full).indexed).get node) := by
  induction nodes generalizing state with
  | nil => cases hm
  | cons other later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    by_cases hl : node.val ∈ later
    · exact ih hl _
    · have heq : node.val = other := (List.mem_cons.mp hm).resolve_right hl
      rw [nodes_frame _ _ _ _ later _ _ (by
        intro next hn he
        have hsame : node.val = next := Nat.add_left_cancel he
        exact hl (hsame ▸ hn)), ← heq]
      exact prepared_nodeBlock_result q full base node state

def LabelsCorrect (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (heap : Nat → Nat) : Prop :=
  ∀ node : (prepareNormalization q full).indexed.NodeId,
    heap (base + node.val) = encodeTool ((IndexedDescent.leafTools (prepareNormalization q full).indexed).get node)

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (state : State) :
    LabelsCorrect q full base (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      (program full.length q (prepareNormalization q full).indexed.nodes.size base) state).heap := by
  intro node
  exact prepared_nodes_result q full base _ node (List.mem_range.mpr node.isLt) state

theorem bitBlock_noStore (N q node tool : Nat) : ∀ op ∈ bitBlock N q node tool, PA17StageMap001.NoStore op := by
  intro op hm
  simp only [bitBlock, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl <;> trivial

theorem nodeTail_take_frame (rom : ROM) (base node count : Nat) (state : State)
    (address : Nat) (hframe : address ≠ base + node) :
    (IndexedClosureRAM.execute rom ((nodeTail base node).take count) state).heap address = state.heap address := by
  by_cases hc : count < 8
  · interval_cases count <;> rfl
  · rw [List.take_of_length_le (show (nodeTail base node).length ≤ count from by change 8 ≤ count; omega),
      nodeTail_heap, Function.update_of_ne hframe]

theorem nodeBlock_take_frame (rom : ROM) (N q base node count : Nat) (state : State)
    (address : Nat) (hframe : address ≠ base + node) :
    (IndexedClosureRAM.execute rom ((nodeBlock N q base node).take count) state).heap address = state.heap address := by
  rw [nodeBlock, List.take_append, IndexedClosureRAM.execute_append, nodeTail_take_frame _ _ _ _ _ _ hframe]
  apply congrFun
  apply PA17StageMap001.execute_noStore_heap
  intro op hm
  have hs := List.mem_of_mem_take hm
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap] at hs
  rcases hs with (rfl | rfl) | ⟨tool, _, hn⟩
  · trivial
  · trivial
  · exact bitBlock_noStore N q node tool op hn

theorem nodes_take_frame (rom : ROM) (N q base : Nat) (nodes : List Nat) (count : Nat) (state : State)
    (address : Nat) (hframe : ∀ node ∈ nodes, address ≠ base + node) :
    (IndexedClosureRAM.execute rom ((nodes.flatMap (nodeBlock N q base)).take count) state).heap address = state.heap address := by
  induction nodes generalizing count state with
  | nil => simp only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute]
  | cons node later ih =>
    rw [List.flatMap_cons, List.take_append, IndexedClosureRAM.execute_append,
      ih _ _ (fun other ho => hframe other (List.mem_cons_of_mem _ ho)),
      nodeBlock_take_frame _ _ _ _ _ _ _ _ (hframe node List.mem_cons_self)]

theorem program_take_frame (rom : ROM) (N q size base count : Nat) (state : State)
    (address : Nat) (hframe : address < base ∨ base + size ≤ address) :
    (IndexedClosureRAM.execute rom ((program N q size base).take count) state).heap address = state.heap address := by
  exact nodes_take_frame rom N q base (List.range size) count state address (by
    intro node hm
    have hn := List.mem_range.mp hm
    omega)

theorem program_capacityThroughout (rom : PhysicalROM) (N q size base capWords : Nat)
    (hbase : capWords ≤ base) (state : State) (hcap : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords rom (program N q size base) state := by
  intro count _ address ha
  rw [program_take_frame rom.semantic N q size base count state address (Or.inl (by omega))]
  exact hcap address ha

def labelBase (N q size : Nat) : Nat :=
  PA17MetadataAssembly003.workspaceBase N size (PA17MetadataAssembly003.capacityWords N q size)

def concreteProgram (N q size : Nat) : List Op := program N q size (labelBase N q size)

theorem concrete_leading_take_frame (rom : ROM) (N q size count : Nat) (state : State)
    (address : Nat) (ha : address < labelBase N q size) :
    (IndexedClosureRAM.execute rom ((concreteProgram N q size).take count) state).heap address = state.heap address :=
  program_take_frame rom N q size _ count state address (Or.inl ha)

theorem table_before_labelBase (N q size address : Nat) (ha : address < tableWords N q size) :
    address < labelBase N q size := by
  have hc := PA17MetadataAssembly003.tableWords_le_capacityWords N q size
  dsimp [labelBase, PA17MetadataAssembly003.workspaceBase, PA17MetadataAssembly003.stageBase]
  omega

theorem concrete_table_take_frame (rom : ROM) (N q size count : Nat) (state : State)
    (address : Nat) (ha : address < tableWords N q size) :
    (IndexedClosureRAM.execute rom ((concreteProgram N q size).take count) state).heap address = state.heap address :=
  concrete_leading_take_frame rom N q size count state address (table_before_labelBase N q size address ha)

theorem concrete_metadata_take_frame (rom : ROM) (N q size count : Nat) (state : State)
    (address : Nat) (ha : address ≤ PA17MetadataAssembly003.capacityWords N q size + 3 * size) :
    (IndexedClosureRAM.execute rom ((concreteProgram N q size).take count) state).heap address = state.heap address := by
  apply concrete_leading_take_frame
  dsimp [labelBase, PA17MetadataAssembly003.workspaceBase, PA17MetadataAssembly003.stageBase]
  omega

theorem metadata_before_labelBase (N q size node encoded : Nat) (hn : node < size) (he : encoded ≤ size) :
    UniformTreeMetadataRAM.cardAddress (PA17MetadataAssembly003.capacityWords N q size) node < labelBase N q size ∧
    UniformTreeMetadataRAM.parentAddress size (PA17MetadataAssembly003.capacityWords N q size) encoded < labelBase N q size ∧
    UniformTreeMetadataRAM.internalAddress size (PA17MetadataAssembly003.capacityWords N q size) node < labelBase N q size := by
  dsimp [UniformTreeMetadataRAM.cardAddress, UniformTreeMetadataRAM.parentAddress, UniformTreeMetadataRAM.internalAddress,
    labelBase, PA17MetadataAssembly003.workspaceBase, PA17MetadataAssembly003.stageBase]
  omega

theorem stage_before_labelBase (N q size stage : Nat) (hs : stage < N) :
    PA17MetadataAssembly003.stageBase size (PA17MetadataAssembly003.capacityWords N q size) + stage < labelBase N q size := by
  dsimp [labelBase, PA17MetadataAssembly003.workspaceBase]
  omega

theorem concrete_stage_take_frame (rom : ROM) (N q size count : Nat) (state : State)
    (stage : Nat) (hs : stage < N) :
    let address := PA17MetadataAssembly003.stageBase size (PA17MetadataAssembly003.capacityWords N q size) + stage
    (IndexedClosureRAM.execute rom ((concreteProgram N q size).take count) state).heap address = state.heap address :=
  concrete_leading_take_frame rom N q size count state _ (stage_before_labelBase N q size stage hs)

theorem indexWords_le (N q size : Nat) : PA17MetadataAssembly003.indexWords N size + size ≤ 4 * (N + q + size + 1) := by
  dsimp [PA17MetadataAssembly003.indexWords]
  omega

theorem bitBlock_length (N q node tool : Nat) : (bitBlock N q node tool).length = 5 := rfl
theorem bitBlock_trace_length (N q node tool : Nat) : (trace (bitBlock N q node tool)).length = 50 := rfl

theorem nodeBlock_length (N q base node : Nat) : (nodeBlock N q base node).length = 5 * q + 10 := by
  have ht : (nodeTail base node).length = 8 := rfl
  simp only [nodeBlock, List.length_append, List.length_cons, List.length_nil, List.length_flatMap,
    bitBlock_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul, ht]
  omega

theorem nodeBlock_trace_length (N q base node : Nat) : (trace (nodeBlock N q base node)).length = 50 * q + 96 := by
  have hi : (trace [.base (.constant .total 0), .base (.constant .value 0)]).length = 16 := rfl
  have ht : (trace (nodeTail base node)).length = 80 := rfl
  rw [nodeBlock, trace_append, trace_append, List.length_append, List.length_append, hi, ht,
    UniformNormalizationRAM.trace_flatMap_length]
  simp only [bitBlock_trace_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem program_length (N q size base : Nat) : (program N q size base).length = (5 * q + 10) * size := by
  simp only [program, List.length_flatMap, nodeBlock_length, List.map_const', List.sum_replicate,
    List.length_range, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem program_trace_length (N q size base : Nat) : (trace (program N q size base)).length = (50 * q + 96) * size := by
  rw [program, UniformNormalizationRAM.trace_flatMap_length]
  simp only [nodeBlock_trace_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem program_codeWords_length (N q size base : Nat) :
    (haltingWords (program N q size base)).length = (25 * q + 50) * size + 5 := by
  rw [haltingWords_length, program_length]
  ring

theorem program_trace_le (N q size base : Nat) (hq : 0 < q) (hsize : 0 < size) :
    (trace (program N q size base) ++ haltTrace).length ≤ 152 * q * size := by
  rw [List.length_append, program_trace_length, haltTrace_length]
  have hm : size ≤ q * size := Nat.le_mul_of_pos_left size hq
  nlinarith

theorem program_code_le (N q size base : Nat) (hq : 0 < q) (hsize : 0 < size) :
    (haltingWords (program N q size base)).length ≤ 80 * q * size := by
  rw [program_codeWords_length]
  have hm : size ≤ q * size := Nat.le_mul_of_pos_left size hq
  nlinarith

theorem prepared_halting_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (base : Nat) (state : State) (hpc : state.pc = 0) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ∃ final operations,
      HaltingRuns (givenTreeROM q full).semantic (program full.length q size base) state final operations ∧
      LabelsCorrect q full base final.heap ∧
      (∀ address, address < base ∨ base + size ≤ address → final.heap address = state.heap address) ∧
      operations.length ≤ 152 * q * size := by
  intro size
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  refine ⟨_, _, IndexedClosureRAM.execute_halts _ _ state hpc, prepared_program_correct q full base state,
    ?_, program_trace_le _ _ _ _ hq hsize⟩
  intro address ha
  simpa only [List.take_length] using program_take_frame (givenTreeROM q full).semantic full.length q size base
    (program full.length q size base).length state address ha

end PaperProofs.Structure.LaminarTree.PA17LeafLabels005
