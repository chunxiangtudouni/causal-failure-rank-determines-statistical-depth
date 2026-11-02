module

public import PaperProofs.Structure.PA17_QuerySelection_010

/-! Read-only, fixed-unroll descent on the runtime-built firstSlackChild
pointers. This follows the original IndexedDescent.descend, including its
precise first-child tie and failure when that child's result is none. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QuerySelection010b

open IndexedRAM IndexedClosureRAM AlgorithmClaims IndexedDescent
open PA17LeafLabels005

def LabelsFor {q : Nat} (cache : IndexedNodeCache (Fin q))
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (leafBase : Nat) (heap : Nat → Nat) : Prop :=
  ∀ node : cache.NodeId, heap (leafBase + node.val) = encodeTool (leaves.get node)

def CandidatesFor {q : Nat} (cache : IndexedNodeCache (Fin q)) (counts capacity : IndexedCapacity cache)
    (childBase : Nat) (heap : Nat → Nat) : Prop :=
  heap childBase = 0 ∧ ∀ node : cache.NodeId,
    heap (childBase + (node.val + 1)) = encodedNode cache (firstSlackChild cache counts capacity node)

def block (leafBase childBase : Nat) : List Op :=
  [.subtract .index .address .total,
   .base (.constant .old leafBase), .base (.add .index .old .index), .base (.loadHeap .flag .index),
   .base (.constant .old 0), .base (.select .flag .address .flag .old),
   .base (.select .value .flag .flag .value),
   .base (.constant .index childBase), .base (.add .index .index .address), .base (.loadHeap .fresh .index),
   .base (.select .address .flag .old .fresh)]

theorem block_heap (rom : ROM) (leafBase childBase : Nat) (state : State) :
    (execute rom (block leafBase childBase) state).heap = state.heap := rfl

theorem block_total (rom : ROM) (leafBase childBase : Nat) (state : State) :
    (execute rom (block leafBase childBase) state).register .total = state.register .total := rfl

theorem block_address (rom : ROM) (leafBase childBase : Nat) (state : State) :
    (execute rom (block leafBase childBase) state).register .address =
      if (if state.register .address = 0 then 0 else state.heap (leafBase + (state.register .address - state.register .total))) = 0 then
        state.heap (childBase + state.register .address) else 0 := rfl

theorem block_value (rom : ROM) (leafBase childBase : Nat) (state : State) :
    (execute rom (block leafBase childBase) state).register .value =
      if (if state.register .address = 0 then 0 else state.heap (leafBase + (state.register .address - state.register .total))) = 0 then
        state.register .value else
        (if state.register .address = 0 then 0 else state.heap (leafBase + (state.register .address - state.register .total))) := rfl

theorem block_stopped (rom : ROM) (leafBase childBase : Nat) (state : State)
    (haddress : state.register .address = 0) (hsentinel : state.heap childBase = 0) :
    (execute rom (block leafBase childBase) state).register .address = 0 ∧
      (execute rom (block leafBase childBase) state).register .value = state.register .value := by
  rw [block_address, block_value, haddress]
  simp only [ite_true, Nat.add_zero, hsentinel, and_self]

theorem block_node {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache)
    (leafBase childBase : Nat) (state : State)
    (hlabels : LabelsFor cache leaves leafBase state.heap) (hcandidates : CandidatesFor cache counts capacity childBase state.heap)
    (node : cache.NodeId) (haddress : state.register .address = node.val + 1) (htotal : state.register .total = 1) :
    (execute rom (block leafBase childBase) state).register .address =
      (match leaves.get node with | none => encodedNode cache (firstSlackChild cache counts capacity node) | some _ => 0) ∧
    (execute rom (block leafBase childBase) state).register .value =
      (match leaves.get node with | none => state.register .value | some tool => tool.val + 1) := by
  rw [block_address, block_value, haddress, htotal, Nat.add_sub_cancel, hlabels node, hcandidates.2 node]
  have hn : node.val + 1 ≠ 0 := by omega
  rw [ite_eq_right hn]
  cases hl : leaves.get node with
  | none => simp only [encodeTool, ite_true, and_self]
  | some tool =>
    have ht : tool.val + 1 ≠ 0 := by omega
    simp only [encodeTool, ht, ite_false, and_self]

def loop (leafBase childBase fuel : Nat) : List Op :=
  (List.replicate fuel (block leafBase childBase)).flatten

theorem loop_heap (rom : ROM) (leafBase childBase fuel : Nat) (state : State) :
    (execute rom (loop leafBase childBase fuel) state).heap = state.heap := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rw [loop, List.replicate_succ, List.flatten_cons, IndexedClosureRAM.execute_append]
    exact (ih _).trans (block_heap rom leafBase childBase state)

theorem loop_stopped (rom : ROM) (leafBase childBase fuel : Nat) (state : State)
    (haddress : state.register .address = 0) (hsentinel : state.heap childBase = 0) :
    (execute rom (loop leafBase childBase fuel) state).register .address = 0 ∧
      (execute rom (loop leafBase childBase fuel) state).register .value = state.register .value := by
  induction fuel generalizing state with
  | zero => exact ⟨haddress, rfl⟩
  | succ fuel ih =>
    have hb := block_stopped rom leafBase childBase state haddress hsentinel
    have hi := ih (execute rom (block leafBase childBase) state) hb.1 hsentinel
    rw [loop, List.replicate_succ, List.flatten_cons, IndexedClosureRAM.execute_append]
    exact ⟨hi.1, hi.2.trans hb.2⟩

theorem loop_node {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache)
    (leafBase childBase fuel : Nat) (state : State)
    (hlabels : LabelsFor cache leaves leafBase state.heap) (hcandidates : CandidatesFor cache counts capacity childBase state.heap)
    (node : cache.NodeId) (haddress : state.register .address = node.val + 1) (htotal : state.register .total = 1)
    (hvalue : state.register .value = 0) :
    (execute rom (loop leafBase childBase fuel) state).register .value =
      encodeTool (descend cache leaves counts capacity fuel node) := by
  induction fuel generalizing state node with
  | zero => exact hvalue
  | succ fuel ih =>
    let after := execute rom (block leafBase childBase) state
    have hb := block_node cache rom leaves counts capacity leafBase childBase state hlabels hcandidates node haddress htotal
    have ht : after.register .total = 1 := (block_total rom leafBase childBase state).trans htotal
    rw [loop, List.replicate_succ, List.flatten_cons, IndexedClosureRAM.execute_append]
    change (execute rom (loop leafBase childBase fuel) after).register .value = _
    cases hl : leaves.get node with
    | some tool =>
      have ha : after.register .address = 0 := by simpa only [hl] using hb.1
      have hv : after.register .value = tool.val + 1 := by simpa only [hl] using hb.2
      rw [(loop_stopped rom leafBase childBase fuel after ha hcandidates.1).2, hv]
      rw [descend, hl]
      rfl
    | none =>
      have ha : after.register .address = encodedNode cache (firstSlackChild cache counts capacity node) := by simpa only [hl] using hb.1
      have hv' : after.register .value = state.register .value := by simpa only [hl] using hb.2
      have hv : after.register .value = 0 := hv'.trans hvalue
      rw [descend, hl]
      cases hc : firstSlackChild cache counts capacity node with
      | none =>
        have haz : after.register .address = 0 := by simpa only [hc, encodedNode] using ha
        exact (loop_stopped rom leafBase childBase fuel after haz hcandidates.1).2.trans hv
      | some child =>
        exact ih after hlabels hcandidates child (by simpa only [hc, encodedNode] using ha) ht hv

theorem loop_option {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (leaves : Vector (Option (Fin q)) cache.nodes.size) (counts capacity : IndexedCapacity cache)
    (leafBase childBase : Nat) (state : State)
    (hlabels : LabelsFor cache leaves leafBase state.heap) (hcandidates : CandidatesFor cache counts capacity childBase state.heap)
    (node : Option cache.NodeId) (haddress : state.register .address = encodedNode cache node)
    (htotal : state.register .total = 1) (hvalue : state.register .value = 0) :
    (execute rom (loop leafBase childBase cache.nodes.size) state).register .value =
      encodeTool (node.bind (selectAt cache leaves counts capacity)) := by
  cases node with
  | none => exact (loop_stopped rom leafBase childBase cache.nodes.size state haddress hcandidates.1).2.trans hvalue
  | some node =>
    exact loop_node cache rom leaves counts capacity leafBase childBase cache.nodes.size state
      hlabels hcandidates node haddress htotal hvalue

theorem loop_total (rom : ROM) (leafBase childBase fuel : Nat) (state : State) :
    (execute rom (loop leafBase childBase fuel) state).register .total = state.register .total := by
  induction fuel generalizing state with
  | zero => rfl
  | succ fuel ih =>
    rw [loop, List.replicate_succ, List.flatten_cons, IndexedClosureRAM.execute_append]
    exact (ih _).trans (block_total rom leafBase childBase state)

def addOffset (fuel : Nat) : List Op := List.replicate fuel (.base (.add .address .address .value))

theorem addOffset_effect (rom : ROM) (fuel : Nat) (state : State) :
    (execute rom (addOffset fuel) state).heap = state.heap ∧
      (execute rom (addOffset fuel) state).register .value = state.register .value ∧
      (execute rom (addOffset fuel) state).register .address = state.register .address + fuel * state.register .value := by
  induction fuel generalizing state with
  | zero => exact ⟨rfl, rfl, by simp only [Nat.zero_mul, Nat.add_zero]; rfl⟩
  | succ fuel ih =>
    rw [addOffset, List.replicate_succ, IndexedClosureRAM.execute]
    have hh := ih (Op.execute rom (.base (.add .address .address .value)) state)
    refine ⟨hh.1, hh.2.1, ?_⟩
    change (execute rom (addOffset fuel) (Op.execute rom (.base (.add .address .address .value)) state)).register .address = _
    rw [hh.2.2]
    change state.register .address + state.register .value + fuel * state.register .value = _
    rw [Nat.add_mul, Nat.one_mul]
    omega

def preludeStart (header : Nat) : List Op :=
  [.base (.constant .index header), .base (.loadHeap .address .index),
   .base (.constant .index (header + 6)), .base (.loadHeap .value .index)]

def preludeTail (payloadPointer : Nat) : List Op :=
  [.base (.constant .old 1), .base (.add .address .address .old),
   .base (.constant .index payloadPointer), .base (.storeHeap .index .address)]

def prelude (size header payloadPointer : Nat) : List Op :=
  preludeStart header ++ addOffset (size + 1) ++ preludeTail payloadPointer

theorem preludeTail_heap (rom : ROM) (payloadPointer : Nat) (state : State) :
    (execute rom (preludeTail payloadPointer) state).heap =
      Function.update state.heap payloadPointer (state.register .address + 1) := rfl

theorem prelude_heap (rom : ROM) (size header payloadPointer : Nat) (state : State) :
    (execute rom (prelude size header payloadPointer) state).heap = Function.update state.heap payloadPointer
      (state.heap header + (size + 1) * state.heap (header + 6) + 1) := by
  rw [prelude, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append, preludeTail_heap,
    (addOffset_effect rom (size + 1) (execute rom (preludeStart header) state)).1,
    (addOffset_effect rom (size + 1) (execute rom (preludeStart header) state)).2.2]
  rfl

def descentInit (header : Nat) : List Op :=
  [.base (.constant .index (header + 1)), .base (.loadHeap .address .index),
   .base (.constant .total 1), .base (.constant .value 0)]

theorem descentInit_heap (rom : ROM) (header : Nat) (state : State) :
    (execute rom (descentInit header) state).heap = state.heap := rfl

theorem descentInit_registers (rom : ROM) (header : Nat) (state : State) :
    (execute rom (descentInit header) state).register .address = state.heap (header + 1) ∧
      (execute rom (descentInit header) state).register .total = 1 ∧
      (execute rom (descentInit header) state).register .value = 0 := ⟨rfl, rfl, rfl⟩

def finish (header payloadPointer toolAddress : Nat) : List Op :=
  [.base (.constant .index payloadPointer), .base (.loadHeap .fresh .index), .subtract .index .fresh .total,
   .base (.loadHeap .flag .index), .base (.constant .old 0), .base (.select .value .flag .value .old),
   .base (.constant .index (header + 7)), .base (.loadHeap .flag .index),
   .base (.select .value .flag .value .old), .base (.constant .index toolAddress), .base (.storeHeap .index .value),
   .base (.add .index .value .old)]

def masked (header payloadPointer : Nat) (state : State) : Nat :=
  if state.heap (header + 7) = 0 then 0 else
    if state.heap (state.heap payloadPointer - state.register .total) = 0 then 0 else state.register .value

theorem finish_heap (rom : ROM) (header payloadPointer toolAddress : Nat) (state : State) :
    (execute rom (finish header payloadPointer toolAddress) state).heap =
      Function.update state.heap toolAddress (masked header payloadPointer state) := rfl

theorem finish_index (rom : ROM) (header payloadPointer toolAddress : Nat) (state : State) :
    (execute rom (finish header payloadPointer toolAddress) state).register .index = masked header payloadPointer state := rfl

def core (size countBase leafBase header childBase : Nat) : List Op :=
  let payloadPointer := childBase + size + 1
  prelude size header payloadPointer ++
    PA17QuerySelection010.program size countBase payloadPointer childBase ++
    descentInit header ++ loop leafBase childBase size

def program (size countBase leafBase header childBase : Nat) : List Op :=
  core size countBase leafBase header childBase ++ finish header (childBase + size + 1) (childBase + size + 2)

theorem core_frame {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (hrom : PA17QuerySelection010.ParentROMFor cache rom)
    (countBase leafBase header childBase : Nat) (state : State) (address : Nat) (ha : address < childBase) :
    (execute rom (core cache.nodes.size countBase leafBase header childBase) state).heap address = state.heap address := by
  rw [core, IndexedClosureRAM.execute_append, loop_heap, IndexedClosureRAM.execute_append,
    descentInit_heap, IndexedClosureRAM.execute_append,
    PA17QuerySelection010.program_frame cache rom hrom countBase _ childBase _ address (by intro encoded _; omega),
    prelude_heap, Function.update_of_ne (by omega)]

theorem core_pointer {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (hrom : PA17QuerySelection010.ParentROMFor cache rom)
    (countBase leafBase header childBase : Nat) (state : State) :
    (execute rom (core cache.nodes.size countBase leafBase header childBase) state).heap (childBase + cache.nodes.size + 1) =
      state.heap header + (cache.nodes.size + 1) * state.heap (header + 6) + 1 := by
  rw [core, IndexedClosureRAM.execute_append, loop_heap, IndexedClosureRAM.execute_append,
    descentInit_heap, IndexedClosureRAM.execute_append,
    PA17QuerySelection010.program_frame cache rom hrom countBase _ childBase _ _ (by intro encoded he; omega),
    prelude_heap, Function.update_self]

theorem core_total {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (countBase leafBase header childBase : Nat) (state : State) :
    (execute rom (core cache.nodes.size countBase leafBase header childBase) state).register .total = 1 := by
  rw [core, IndexedClosureRAM.execute_append, loop_total, IndexedClosureRAM.execute_append]
  rfl

theorem prepared_core_result (q : Nat) (full : List (Finset (Fin q))) (queryStage : Nat) (used : Finset (Fin q))
    (counts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (countBase leafBase header childBase payloadBase : Nat)
    (hcountBase : countBase + (prepareNormalization q full).indexed.nodes.size ≤ childBase)
    (hleafBase : leafBase + (prepareNormalization q full).indexed.nodes.size ≤ childBase)
    (hheader : header + 7 < childBase)
    (hpayloadBase : payloadBase + (prepareNormalization q full).indexed.nodes.size ≤ childBase)
    (state : State)
    (hpointer : state.heap header + ((prepareNormalization q full).indexed.nodes.size + 1) * state.heap (header + 6) + 1 = payloadBase)
    (hcounts : ∀ node : (prepareNormalization q full).indexed.NodeId, state.heap (countBase + node.val) = counts.get node)
    (hcapacity : ∀ node : (prepareNormalization q full).indexed.NodeId, state.heap (payloadBase + node.val) = capacity.get node)
    (hlabels : LabelsFor (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed) leafBase state.heap)
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (hnode : state.heap (header + 1) = encodedNode (prepareNormalization q full).indexed node) :
    let cache := (prepareNormalization q full).indexed
    (execute (queryROM q full queryStage used).semantic
      (core cache.nodes.size countBase leafBase header childBase) state).register .value =
        encodeTool (node.bind (selectAt cache (leafTools cache) counts capacity)) := by
  intro cache
  change countBase + cache.nodes.size ≤ childBase at hcountBase
  change leafBase + cache.nodes.size ≤ childBase at hleafBase
  change payloadBase + cache.nodes.size ≤ childBase at hpayloadBase
  let rom := (queryROM q full queryStage used).semantic
  let pointer := childBase + cache.nodes.size + 1
  let imported := execute rom (prelude cache.nodes.size header pointer) state
  let pushed := execute rom (PA17QuerySelection010.program cache.nodes.size countBase pointer childBase) imported
  let started := execute rom (descentInit header) pushed
  have hrom : PA17QuerySelection010.ParentROMFor cache rom := fun n => UniformNormalizationRAM.givenTreeROM_parent q full n
  have hi : PA17QuerySelection010.Inputs cache counts capacity countBase pointer payloadBase imported.heap := by
    constructor
    · rw [prelude_heap, Function.update_self]
      exact hpointer
    · intro n
      rw [prelude_heap, Function.update_of_ne (by dsimp [pointer]; have := n.isLt; omega),
        Function.update_of_ne (by dsimp [pointer]; have := n.isLt; omega)]
      exact ⟨hcounts n, hcapacity n⟩
  have hd : PA17QuerySelection010.SourcesDisjoint cache.nodes.size countBase pointer payloadBase childBase := by
    constructor
    · intro encoded he
      dsimp [pointer]
      omega
    · intro n hn encoded he
      constructor <;> omega
  have hf (address : Nat) (ha : address < childBase) : pushed.heap address = state.heap address := by
    rw [PA17QuerySelection010.program_frame cache rom hrom countBase pointer childBase imported address (by intro encoded _; omega),
      prelude_heap, Function.update_of_ne (by dsimp [pointer]; omega)]
  have hc : CandidatesFor cache counts capacity childBase started.heap := by
    constructor
    · exact PA17QuerySelection010.program_sentinel rom cache.nodes.size countBase pointer childBase imported
    · intro n
      exact PA17QuerySelection010.prepared_program_candidate q full queryStage used counts capacity
        countBase pointer payloadBase childBase hd imported hi n
  have hl : LabelsFor cache (leafTools cache) leafBase started.heap := by
    intro n
    rw [show started.heap = pushed.heap from rfl, hf (leafBase + n.val) (by have := n.isLt; omega)]
    exact hlabels n
  have hs := descentInit_registers rom header pushed
  have ha : started.register .address = encodedNode cache node := hs.1.trans ((hf (header + 1) (by omega)).trans hnode)
  have heq : execute rom (core cache.nodes.size countBase leafBase header childBase) state =
      execute rom (loop leafBase childBase cache.nodes.size) started := by
    simp only [core, IndexedClosureRAM.execute_append]
    rfl
  rw [heq]
  exact loop_option cache rom (leafTools cache) counts capacity leafBase childBase started hl hc node ha hs.2.1 hs.2.2

theorem program_frame {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM)
    (hrom : PA17QuerySelection010.ParentROMFor cache rom)
    (countBase leafBase header childBase : Nat) (state : State) (address : Nat) (ha : address < childBase) :
    (execute rom (program cache.nodes.size countBase leafBase header childBase) state).heap address = state.heap address := by
  rw [program, IndexedClosureRAM.execute_append, finish_heap, Function.update_of_ne (by omega)]
  exact core_frame cache rom hrom countBase leafBase header childBase state address ha

theorem prepared_program_selectEntry (q : Nat) (full : List (Finset (Fin q))) (queryStage : Nat) (used : Finset (Fin q))
    (counts : IndexedCapacity (prepareNormalization q full).indexed)
    (countBase leafBase header childBase sourceSlot : Nat)
    (hcountBase : countBase + (prepareNormalization q full).indexed.nodes.size ≤ childBase)
    (hleafBase : leafBase + (prepareNormalization q full).indexed.nodes.size ≤ childBase)
    (hheader : header + 7 < childBase)
    (hsource : (sourceSlot + 1) * ((prepareNormalization q full).indexed.nodes.size + 1) ≤ childBase)
    (state : State)
    (hslot : state.heap header + ((prepareNormalization q full).indexed.nodes.size + 1) * state.heap (header + 6) =
      sourceSlot * ((prepareNormalization q full).indexed.nodes.size + 1))
    (hcounts : ∀ node : (prepareNormalization q full).indexed.NodeId, state.heap (countBase + node.val) = counts.get node)
    (hlabels : LabelsFor (prepareNormalization q full).indexed (leafTools (prepareNormalization q full).indexed) leafBase state.heap)
    (node : Option (prepareNormalization q full).indexed.NodeId)
    (hnode : state.heap (header + 1) = encodedNode (prepareNormalization q full).indexed node) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (queryROM q full queryStage used).semantic (program cache.nodes.size countBase leafBase header childBase) state
    let expected := if state.heap (header + 7) = 0 then 0 else
      encodeTool (IndexedQuery.selectEntry cache (leafTools cache) counts node (readEntry cache.nodes.size sourceSlot state.heap))
    result.register .index = expected ∧ result.heap (childBase + cache.nodes.size + 2) = expected := by
  intro cache result expected
  let rom := (queryROM q full queryStage used).semantic
  let payloadBase := sourceSlot * (cache.nodes.size + 1) + 1
  let capacity : IndexedCapacity cache := Vector.ofFn (fun n => state.heap (payloadBase + n.val))
  let walked := execute rom (core cache.nodes.size countBase leafBase header childBase) state
  have hrom : PA17QuerySelection010.ParentROMFor cache rom := fun n => UniformNormalizationRAM.givenTreeROM_parent q full n
  have hsource' : payloadBase + cache.nodes.size ≤ childBase := by
    change (sourceSlot + 1) * (cache.nodes.size + 1) ≤ childBase at hsource
    dsimp [payloadBase]
    rw [Nat.add_mul, Nat.one_mul] at hsource
    omega
  have hvalue := prepared_core_result q full queryStage used counts capacity countBase leafBase header childBase payloadBase
    hcountBase hleafBase hheader hsource' state (by dsimp [payloadBase]; rw [hslot]) hcounts
    (by
      intro n
      change state.heap (payloadBase + n.val) = (Vector.ofFn (fun x : cache.NodeId => state.heap (payloadBase + x.val))).get n
      rw [cache_get_ofFn]) hlabels node hnode
  have hm : masked header (childBase + cache.nodes.size + 1) walked = expected := by
    change (if walked.heap (header + 7) = 0 then 0 else
      if walked.heap (walked.heap (childBase + cache.nodes.size + 1) - walked.register .total) = 0 then 0 else walked.register .value) = _
    rw [core_frame cache rom hrom countBase leafBase header childBase state (header + 7) hheader,
      core_pointer cache rom hrom countBase leafBase header childBase state,
      core_total cache rom countBase leafBase header childBase state, hslot, Nat.add_sub_cancel,
      core_frame cache rom hrom countBase leafBase header childBase state (sourceSlot * (cache.nodes.size + 1)) (by
        dsimp [payloadBase] at hsource'
        omega), hvalue]
    dsimp only [expected]
    rw [readEntry]
    by_cases hf : state.heap (header + 7) = 0
    · simp only [hf, ite_true]
    · simp only [hf, ite_false]
      by_cases ht : state.heap (sourceSlot * (cache.nodes.size + 1)) = 0
      · simp only [ht, ite_true, IndexedQuery.selectEntry, encodeTool]
      · simp only [ht, ite_false, IndexedQuery.selectEntry]
        rfl
  have heq : result = execute rom (finish header (childBase + cache.nodes.size + 1) (childBase + cache.nodes.size + 2)) walked := by
    dsimp only [result, program]
    rw [IndexedClosureRAM.execute_append]
  rw [heq]
  rw [finish_index, finish_heap, Function.update_self]
  exact ⟨hm, hm⟩

set_option maxRecDepth 10000 in
theorem block_trace_length (leafBase childBase : Nat) : (trace (block leafBase childBase)).length = 115 := rfl

theorem loop_trace_length (leafBase childBase fuel : Nat) :
    (trace (loop leafBase childBase fuel)).length = 115 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [loop, List.replicate_succ, List.flatten_cons, trace_append, List.length_append, block_trace_length]
    change 115 + (trace (loop leafBase childBase fuel)).length = _
    rw [ih]
    omega

theorem addOffset_trace_length (fuel : Nat) : (trace (addOffset fuel)).length = 11 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [addOffset, List.replicate_succ]
    change (trace ([.base (.add .address .address .value)] ++ addOffset fuel)).length = _
    rw [trace_append, List.length_append]
    change 11 + (trace (addOffset fuel)).length = _
    rw [ih]
    omega

theorem prelude_trace_length (size header payloadPointer : Nat) :
    (trace (prelude size header payloadPointer)).length = 11 * size + 87 := by
  rw [prelude, trace_append, trace_append, List.length_append, List.length_append, addOffset_trace_length]
  have hh : (trace (preludeStart header)).length = 38 := rfl
  have ht : (trace (preludeTail payloadPointer)).length = 38 := rfl
  rw [hh, ht]
  omega

theorem core_trace_length (size countBase leafBase header childBase : Nat) :
    (trace (core size countBase leafBase header childBase)).length = 324 * size + 149 := by
  simp only [core, trace_append, List.length_append, prelude_trace_length,
    PA17QuerySelection010.program_trace_length, loop_trace_length]
  have hi : (trace (descentInit header)).length = 35 := rfl
  rw [hi]
  omega

set_option maxRecDepth 10000 in
theorem finish_trace_length (header payloadPointer toolAddress : Nat) :
    (trace (finish header payloadPointer toolAddress)).length = 122 := rfl

theorem program_trace_length (size countBase leafBase header childBase : Nat) :
    (trace (program size countBase leafBase header childBase)).length = 324 * size + 271 := by
  rw [program, trace_append, List.length_append, core_trace_length, finish_trace_length]

theorem program_halting (rom : ROM) (size countBase leafBase header childBase : Nat)
    (hsize : 0 < size) (state : State) (hpc : state.pc = 0) :
    HaltingRuns rom (program size countBase leafBase header childBase) state
      (execute rom (program size countBase leafBase header childBase) state)
      (trace (program size countBase leafBase header childBase) ++ haltTrace) ∧
      (trace (program size countBase leafBase header childBase) ++ haltTrace).length ≤ 601 * size := by
  refine ⟨execute_halts _ _ state hpc, ?_⟩
  rw [List.length_append, program_trace_length, haltTrace_length]
  omega

end PaperProofs.Structure.LaminarTree.PA17QuerySelection010b
