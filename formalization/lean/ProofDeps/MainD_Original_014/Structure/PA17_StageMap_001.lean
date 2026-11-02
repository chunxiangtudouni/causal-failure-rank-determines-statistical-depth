module

public import PaperProofs.Structure.UniformTreeMetadataRAM

/-! A17: the dimension-only stage-to-node RAM pass. No stage lookup data is
an input. Every stage/node comparison reads both original q-bit rows. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17StageMap001

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def bitBlock (N q stage node tool : Nat) : List Op :=
  [.base (.constant .index (3 + stage * q + tool)),
   .base (.loadROM .input .old .index),
   .base (.constant .index (3 + N * q + node * q + tool)),
   .base (.loadROM .input .fresh .index),
   .subtract .flag .old .fresh, .subtract .index .fresh .old,
   .base (.add .flag .flag .index), .base (.add .total .total .flag)]

def difference (rom : ROM) (N q stage node tool : Nat) : Nat :=
  let left := rom.read .input (3 + stage * q + tool)
  let right := rom.read .input (3 + N * q + node * q + tool)
  (left - right) + (right - left)

def mismatch (rom : ROM) (N q stage node : Nat) : Nat :=
  ((List.range q).map (difference rom N q stage node)).sum

def nodeTail (node : Nat) : List Op :=
  [.base (.constant .old (node + 1)), .base (.select .value .total .value .old)]

def nodeBlock (N q stage node : Nat) : List Op :=
  [.base (.constant .total 0)] ++ (List.range q).flatMap (bitBlock N q stage node) ++ nodeTail node

def stageTail (base stage : Nat) : List Op :=
  [.base (.constant .index (base + stage)), .base (.storeHeap .index .value)]

def stageBlock (N q size base stage : Nat) : List Op :=
  [.base (.constant .value 0)] ++ (List.range size).flatMap (nodeBlock N q stage) ++ stageTail base stage

def program (N q size base : Nat) : List Op :=
  (List.range N).flatMap (stageBlock N q size base)

theorem bitBlock_heap (rom : ROM) (N q stage node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q stage node tool) state).heap = state.heap := rfl

theorem bitBlock_value (rom : ROM) (N q stage node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q stage node tool) state).register .value = state.register .value := rfl

theorem bitBlock_total (rom : ROM) (N q stage node tool : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (bitBlock N q stage node tool) state).register .total =
      state.register .total + difference rom N q stage node tool := rfl

theorem bits_heap (rom : ROM) (N q stage node : Nat) (tools : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q stage node)) state).heap = state.heap := by
  induction tools generalizing state with
  | nil => rfl
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, bitBlock_heap]

theorem bits_value (rom : ROM) (N q stage node : Nat) (tools : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q stage node)) state).register .value = state.register .value := by
  induction tools generalizing state with
  | nil => rfl
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, bitBlock_value]

theorem bits_total (rom : ROM) (N q stage node : Nat) (tools : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (tools.flatMap (bitBlock N q stage node)) state).register .total =
      state.register .total + (tools.map (difference rom N q stage node)).sum := by
  induction tools generalizing state with
  | nil => simp only [List.flatMap_nil, IndexedClosureRAM.execute, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, bitBlock_total]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem nodeBlock_heap (rom : ROM) (N q stage node : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (nodeBlock N q stage node) state).heap = state.heap := by
  rw [nodeBlock, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  change (IndexedClosureRAM.execute rom ((List.range q).flatMap (bitBlock N q stage node))
    (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state)).heap = _
  rw [bits_heap]
  rfl

theorem nodeBlock_value (rom : ROM) (N q stage node : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (nodeBlock N q stage node) state).register .value =
      if mismatch rom N q stage node = 0 then node + 1 else state.register .value := by
  rw [nodeBlock, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  change (if (IndexedClosureRAM.execute rom ((List.range q).flatMap (bitBlock N q stage node))
      (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state)).register .total = 0 then node + 1
    else (IndexedClosureRAM.execute rom ((List.range q).flatMap (bitBlock N q stage node))
      (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state)).register .value) = _
  rw [bits_total, bits_value]
  have hi : (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state).register .total = 0 := rfl
  have hv : (IndexedClosureRAM.execute rom [.base (.constant .total 0)] state).register .value = state.register .value := rfl
  rw [hi, hv, Nat.zero_add]
  rfl

theorem nodes_heap (rom : ROM) (N q stage : Nat) (nodes : List Nat) (state : State) :
    (IndexedClosureRAM.execute rom (nodes.flatMap (nodeBlock N q stage)) state).heap = state.heap := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, nodeBlock_heap]

theorem nodes_value_none (rom : ROM) (N q stage : Nat) (nodes : List Nat)
    (hnone : ∀ node ∈ nodes, mismatch rom N q stage node ≠ 0) (state : State) :
    (IndexedClosureRAM.execute rom (nodes.flatMap (nodeBlock N q stage)) state).register .value = state.register .value := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih (fun other ho => hnone other (List.mem_cons_of_mem _ ho)),
      nodeBlock_value, ite_eq_right (hnone node List.mem_cons_self)]

theorem nodes_value_some (rom : ROM) (N q stage : Nat) (nodes : List Nat)
    (target : Nat) (hmem : target ∈ nodes) (hzero : mismatch rom N q stage target = 0)
    (hunique : ∀ node ∈ nodes, mismatch rom N q stage node = 0 → node = target) (state : State) :
    (IndexedClosureRAM.execute rom (nodes.flatMap (nodeBlock N q stage)) state).register .value = target + 1 := by
  induction nodes generalizing state with
  | nil => cases hmem
  | cons node later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    by_cases htl : target ∈ later
    · exact ih htl (fun other ho => hunique other (List.mem_cons_of_mem _ ho)) _
    · have heq : target = node := (List.mem_cons.mp hmem).resolve_right htl
      rw [nodes_value_none rom N q stage later (by
        intro other ho hz
        have hs := hunique other (List.mem_cons_of_mem _ ho) hz
        exact htl (hs ▸ ho)), nodeBlock_value, ← heq, ite_eq_left hzero]

theorem difference_eq_zero_iff (rom : ROM) (N q stage node tool : Nat) :
    difference rom N q stage node tool = 0 ↔
      rom.read .input (3 + stage * q + tool) = rom.read .input (3 + N * q + node * q + tool) := by
  dsimp only [difference]
  omega

theorem mismatch_eq_zero_iff (rom : ROM) (N q stage node : Nat) :
    mismatch rom N q stage node = 0 ↔
      ∀ tool < q, rom.read .input (3 + stage * q + tool) = rom.read .input (3 + N * q + node * q + tool) := by
  rw [mismatch, List.sum_eq_zero_iff]
  simp only [List.mem_map, List.mem_range, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂]
  exact forall_congr' (fun tool => forall_congr' (fun _ => difference_eq_zero_iff rom N q stage node tool))

theorem givenTreeROM_stage_bit (q : Nat) (full : List (Finset (Fin q)))
    (stage : Fin full.length) (tool : Fin q) :
    (givenTreeROM q full).semantic.read .input (3 + stage.val * q + tool.val) =
      bit (decide (tool ∈ full[stage.val])) := by
  let cache := (prepareNormalization q full).indexed
  change (([full.length, q, cache.nodes.size] ++ incidence full) ++ _).getD _ 0 = _
  rw [List.getD_append _ _ _ _ (by
    simp only [List.length_append, List.length_cons, List.length_nil, RawIncidenceLaminarRAM.incidence_length]
    have hmul := Nat.mul_le_mul_right q (Nat.succ_le_of_lt stage.isLt)
    rw [Nat.succ_mul] at hmul
    omega), List.getD_append_right _ _ _ _ (by simp only [List.length_cons, List.length_nil]; omega)]
  simp only [List.length_cons, List.length_nil]
  have hoff : 3 + stage.val * q + tool.val - 3 = stage.val * q + tool.val := by omega
  rw [hoff, RawIncidenceLaminarRAM.incidence_getD q full stage.val stage.isLt tool]

theorem bit_decide_injective {left right : Prop} [Decidable left] [Decidable right] :
    bit (decide left) = bit (decide right) ↔ (left ↔ right) := by
  by_cases hl : left <;> by_cases hr : right <;> simp [bit, hl, hr]

theorem prepared_mismatch_eq_zero_iff (q : Nat) (full : List (Finset (Fin q)))
    (stage : Fin full.length) (node : (prepareNormalization q full).indexed.NodeId) :
    mismatch (givenTreeROM q full).semantic full.length q stage.val node.val = 0 ↔
      (prepareNormalization q full).indexed.decode node = full[stage.val] := by
  rw [mismatch_eq_zero_iff]
  constructor
  · intro h
    apply Finset.ext
    intro tool
    have hh := h tool.val tool.isLt
    rw [givenTreeROM_stage_bit q full stage tool, UniformTreeMetadataRAM.givenTreeROM_node_bit q full node tool,
      bit_decide_injective] at hh
    exact hh.symm
  · intro heq tool ht
    rw [givenTreeROM_stage_bit q full stage ⟨tool, ht⟩,
      UniformTreeMetadataRAM.givenTreeROM_node_bit q full node ⟨tool, ht⟩, heq]

theorem stageTail_heap (rom : ROM) (base stage : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (stageTail base stage) state).heap =
      Function.update state.heap (base + stage) (state.register .value) := rfl

theorem stageBlock_heap (rom : ROM) (N q size base stage : Nat) (state : State) :
    (IndexedClosureRAM.execute rom (stageBlock N q size base stage) state).heap =
      Function.update state.heap (base + stage)
        ((IndexedClosureRAM.execute rom ((List.range size).flatMap (nodeBlock N q stage))
          (IndexedClosureRAM.execute rom [.base (.constant .value 0)] state)).register .value) := by
  rw [stageBlock, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  rw [stageTail_heap, nodes_heap]
  rfl

theorem prepared_stageBlock_result (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (base : Nat) (stage : Fin full.length) (state : State) :
    let cache := (prepareNormalization q full).indexed
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic (stageBlock full.length q cache.nodes.size base stage.val) state).heap
      (base + stage.val) = encodedNode cache (IndexedQuery.storedStageNode q full hq stage) := by
  intro cache
  rw [stageBlock_heap, Function.update_self]
  let start := IndexedClosureRAM.execute (givenTreeROM q full).semantic [.base (.constant .value 0)] state
  change (IndexedClosureRAM.execute _ _ start).register .value = _
  cases hs : IndexedQuery.storedStageNode q full hq stage with
  | none =>
    have hempty : full[stage.val] = ∅ :=
      (IndexedStaticMetadata.buildPositive_stage_none_iff q full hq stage).mp hs
    have hn : ∀ node ∈ List.range cache.nodes.size,
        mismatch (givenTreeROM q full).semantic full.length q stage.val node ≠ 0 := by
      intro node hm hz
      have heq := (prepared_mismatch_eq_zero_iff q full stage ⟨node, List.mem_range.mp hm⟩).mp hz
      let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
      have hne := nodeFamily_nonempty_nodes full _ (prepared_indexed_node_mem q full ⟨node, List.mem_range.mp hm⟩)
      rw [heq, hempty] at hne
      exact Finset.not_nonempty_empty hne
    rw [nodes_value_none _ _ _ _ _ hn]
    rfl
  | some target =>
    have ht : cache.decode target = full[stage.val] :=
      ((IndexedStaticMetadata.buildPositive_stage_some_iff q full hq stage target).mp hs).2
    have hz := (prepared_mismatch_eq_zero_iff q full stage target).mpr ht
    have hu : ∀ node ∈ List.range cache.nodes.size,
        mismatch (givenTreeROM q full).semantic full.length q stage.val node = 0 → node = target.val := by
      intro node hm hzero
      have hn := (prepared_mismatch_eq_zero_iff q full stage ⟨node, List.mem_range.mp hm⟩).mp hzero
      have heq := prepared_indexed_decode_injective q full (hn.trans ht.symm)
      exact congrArg Fin.val heq
    exact nodes_value_some _ _ _ _ _ target.val (List.mem_range.mpr target.isLt) hz hu start

theorem stageBlock_frame (rom : ROM) (N q size base stage : Nat) (state : State)
    (address : Nat) (hframe : address ≠ base + stage) :
    (IndexedClosureRAM.execute rom (stageBlock N q size base stage) state).heap address = state.heap address := by
  rw [stageBlock_heap, Function.update_of_ne hframe]

theorem stages_frame (rom : ROM) (N q size base : Nat) (stages : List Nat) (state : State)
    (address : Nat) (hframe : ∀ stage ∈ stages, address ≠ base + stage) :
    (IndexedClosureRAM.execute rom (stages.flatMap (stageBlock N q size base)) state).heap address = state.heap address := by
  induction stages generalizing state with
  | nil => rfl
  | cons stage later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append,
      ih _ (fun other ho => hframe other (List.mem_cons_of_mem _ ho)),
      stageBlock_frame rom N q size base stage state address (hframe stage List.mem_cons_self)]

theorem prepared_stages_values (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (base : Nat) (stages : List Nat) (hstages : ∀ stage ∈ stages, stage < full.length)
    (target : Fin full.length) (hmem : target.val ∈ stages) (state : State) :
    let cache := (prepareNormalization q full).indexed
    (IndexedClosureRAM.execute (givenTreeROM q full).semantic
      (stages.flatMap (stageBlock full.length q cache.nodes.size base)) state).heap (base + target.val) =
      encodedNode cache (IndexedQuery.storedStageNode q full hq target) := by
  intro cache
  induction stages generalizing state with
  | nil => cases hmem
  | cons stage later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    by_cases ht : target.val ∈ later
    · exact ih (fun other ho => hstages other (List.mem_cons_of_mem _ ho)) ht _
    · have heq : target.val = stage := (List.mem_cons.mp hmem).resolve_right ht
      rw [stages_frame _ _ _ _ _ later _ _ (by
        intro other ho he
        have hsame : target.val = other := Nat.add_left_cancel he
        exact ht (hsame ▸ ho)), ← heq]
      exact prepared_stageBlock_result q full hq base target state

def StageMapCorrect (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (base : Nat) (heap : Nat → Nat) : Prop :=
  ∀ stage : Fin full.length, heap (base + stage.val) =
    encodedNode (prepareNormalization q full).indexed (IndexedQuery.storedStageNode q full hq stage)

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (base : Nat) (state : State) :
    StageMapCorrect q full hq base
      (IndexedClosureRAM.execute (givenTreeROM q full).semantic
        (program full.length q (prepareNormalization q full).indexed.nodes.size base) state).heap := by
  intro stage
  exact prepared_stages_values q full hq base (List.range full.length)
    (fun _ hm => List.mem_range.mp hm) stage (List.mem_range.mpr stage.isLt) state

theorem program_frame (rom : ROM) (N q size base : Nat) (state : State)
    (address : Nat) (hframe : address < base ∨ base + N ≤ address) :
    (IndexedClosureRAM.execute rom (program N q size base) state).heap address = state.heap address := by
  exact stages_frame rom N q size base (List.range N) state address (by
    intro stage hm
    have hs := List.mem_range.mp hm
    omega)

def NoStore : Op → Prop
  | .base (.storeHeap _ _) => False
  | _ => True

theorem noStore_heap (rom : ROM) (op : Op) (hn : NoStore op) (state : State) :
    (op.execute rom state).heap = state.heap := by
  cases op with
  | subtract target left right => rfl
  | base instruction =>
    cases instruction <;> first | rfl | exact False.elim hn

theorem execute_noStore_heap (rom : ROM) (ops : List Op) (hn : ∀ op ∈ ops, NoStore op) (state : State) :
    (IndexedClosureRAM.execute rom ops state).heap = state.heap := by
  induction ops generalizing state with
  | nil => rfl
  | cons op later ih =>
    rw [IndexedClosureRAM.execute, ih (fun other ho => hn other (List.mem_cons_of_mem _ ho)),
      noStore_heap rom op (hn op List.mem_cons_self)]

theorem nodeBlock_noStore (N q stage node : Nat) :
    ∀ op ∈ nodeBlock N q stage node, NoStore op := by
  intro op hm
  simp only [nodeBlock, List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap] at hm
  rcases hm with (rfl | ⟨tool, _, hm⟩) | hm
  · trivial
  · simp only [bitBlock, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial
  · simp only [nodeTail, List.mem_cons, List.mem_nil_iff, or_false] at hm
    rcases hm with rfl | rfl <;> trivial

theorem stageTail_take_frame (rom : ROM) (base stage count : Nat) (state : State)
    (address : Nat) (hframe : address ≠ base + stage) :
    (IndexedClosureRAM.execute rom ((stageTail base stage).take count) state).heap address = state.heap address := by
  cases count with
  | zero => rfl
  | succ count =>
    cases count with
    | zero => rfl
    | succ count =>
      have heq : (stageTail base stage).take (count + 1 + 1) = stageTail base stage := by
        simp only [stageTail, List.take_succ_cons, List.take_nil]
      rw [heq]
      rw [stageTail_heap, Function.update_of_ne hframe]

theorem stageBlock_take_frame (rom : ROM) (N q size base stage count : Nat) (state : State)
    (address : Nat) (hframe : address ≠ base + stage) :
    (IndexedClosureRAM.execute rom ((stageBlock N q size base stage).take count) state).heap address = state.heap address := by
  rw [stageBlock, List.take_append, IndexedClosureRAM.execute_append, stageTail_take_frame _ _ _ _ _ _ hframe]
  apply congrFun
  apply execute_noStore_heap
  intro op hm
  have hs := List.mem_of_mem_take hm
  simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap] at hs
  rcases hs with rfl | ⟨node, _, hn⟩
  · trivial
  · exact nodeBlock_noStore N q stage node op hn

theorem stages_take_frame (rom : ROM) (N q size base : Nat) (stages : List Nat) (count : Nat) (state : State)
    (address : Nat) (hframe : ∀ stage ∈ stages, address ≠ base + stage) :
    (IndexedClosureRAM.execute rom ((stages.flatMap (stageBlock N q size base)).take count) state).heap address = state.heap address := by
  induction stages generalizing count state with
  | nil => simp only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute]
  | cons stage later ih =>
    rw [List.flatMap_cons, List.take_append, IndexedClosureRAM.execute_append,
      ih _ _ (fun other ho => hframe other (List.mem_cons_of_mem _ ho)),
      stageBlock_take_frame _ _ _ _ _ _ _ _ _ (hframe stage List.mem_cons_self)]

theorem program_take_frame (rom : ROM) (N q size base count : Nat) (state : State)
    (address : Nat) (hframe : address < base ∨ base + N ≤ address) :
    (IndexedClosureRAM.execute rom ((program N q size base).take count) state).heap address = state.heap address := by
  exact stages_take_frame rom N q size base (List.range N) count state address (by
    intro stage hm
    have hs := List.mem_range.mp hm
    omega)

theorem program_capacityThroughout (rom : PhysicalROM) (N q size base capWords : Nat)
    (hbase : capWords ≤ base) (state : State) (hcap : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords rom (program N q size base) state := by
  intro count _ address ha
  rw [program_take_frame rom.semantic N q size base count state address (Or.inl (by omega))]
  exact hcap address ha

theorem bitBlock_length (N q stage node tool : Nat) :
    (bitBlock N q stage node tool).length = 8 := rfl

theorem bitBlock_trace_length (N q stage node tool : Nat) :
    (trace (bitBlock N q stage node tool)).length = 82 := rfl

theorem nodeBlock_length (N q stage node : Nat) :
    (nodeBlock N q stage node).length = 8 * q + 3 := by
  simp only [nodeBlock, List.length_append, List.length_cons, List.length_nil,
    List.length_flatMap, bitBlock_length, List.map_const', List.sum_replicate,
    List.length_range, Nat.nsmul_eq_mul, nodeTail]
  omega

theorem nodeBlock_trace_length (N q stage node : Nat) :
    (trace (nodeBlock N q stage node)).length = 82 * q + 28 := by
  have hi : (trace [.base (.constant .total 0)]).length = 8 := rfl
  have ht : (trace (nodeTail node)).length = 20 := rfl
  rw [nodeBlock, trace_append, trace_append, List.length_append, List.length_append, hi, ht,
    UniformNormalizationRAM.trace_flatMap_length]
  simp only [bitBlock_trace_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem stageBlock_length (N q size base stage : Nat) :
    (stageBlock N q size base stage).length = (8 * q + 3) * size + 3 := by
  simp only [stageBlock, List.length_append, List.length_cons, List.length_nil,
    List.length_flatMap, nodeBlock_length, List.map_const', List.sum_replicate,
    List.length_range, Nat.nsmul_eq_mul, stageTail]
  ring

theorem stageBlock_trace_length (N q size base stage : Nat) :
    (trace (stageBlock N q size base stage)).length = (82 * q + 28) * size + 27 := by
  have hi : (trace [.base (.constant .value 0)]).length = 8 := rfl
  have ht : (trace (stageTail base stage)).length = 19 := rfl
  rw [stageBlock, trace_append, trace_append, List.length_append, List.length_append, hi, ht,
    UniformNormalizationRAM.trace_flatMap_length]
  simp only [nodeBlock_trace_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  ring

theorem program_length (N q size base : Nat) :
    (program N q size base).length = N * ((8 * q + 3) * size + 3) := by
  simp only [program, List.length_flatMap, stageBlock_length, List.map_const', List.sum_replicate,
    List.length_range, Nat.nsmul_eq_mul]

theorem program_trace_length (N q size base : Nat) :
    (trace (program N q size base)).length = N * ((82 * q + 28) * size + 27) := by
  rw [program, UniformNormalizationRAM.trace_flatMap_length]
  simp only [stageBlock_trace_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]

theorem program_codeWords_length (N q size base : Nat) :
    (haltingWords (program N q size base)).length = 5 * N * ((8 * q + 3) * size + 3) + 5 := by
  rw [haltingWords, List.length_append, IndexedClosureRAM.programWords_length, program_length]
  have hh : haltWords.toArray.toList.length = 5 := rfl
  rw [hh]
  ring

theorem program_trace_le (N q size base : Nat) (hsize : 0 < size) :
    (trace (program N q size base) ++ haltTrace).length ≤ 160 * work N q size := by
  rw [List.length_append, program_trace_length, haltTrace_length]
  have hlocal : (82 * q + 28) * size + 27 ≤ 137 * (q + 1) * size := by nlinarith
  have hmul := Nat.mul_le_mul_left N hlocal
  dsimp [work]
  nlinarith

theorem prepared_program_halting_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (base : Nat) (state : State) (hpc : state.pc = 0) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ∃ final operations,
      HaltingRuns (givenTreeROM q full).semantic (program full.length q size base) state final operations ∧
      StageMapCorrect q full hq base final.heap ∧
      (∀ address, address < base ∨ base + full.length ≤ address → final.heap address = state.heap address) ∧
      operations.length ≤ 160 * work full.length q size := by
  intro size
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  refine ⟨_, _, IndexedClosureRAM.execute_halts _ _ state hpc,
    prepared_program_correct q full hq base state, ?_, program_trace_le _ _ _ _ hsize⟩
  intro address ha
  exact program_frame _ _ _ _ _ state address ha

end PaperProofs.Structure.LaminarTree.PA17StageMap001
