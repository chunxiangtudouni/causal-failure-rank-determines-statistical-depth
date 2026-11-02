module

public import PaperProofs.Structure.IndexedRAM
public import PaperProofs.Structure.IndexedAncestors
public import PaperProofs.Structure.IndexedStaticMetadata

/-!
Actual ancestor-decrement program for frozen laminar-proofs.tex:80--112.
The normalizer's RAM is reused, with only ordinary saturating subtraction
added. No set, ancestor, rank or extension operation is a machine primitive.
All parent steps are explicit code and remain charged after the root sentinel.
The complete loop and decoded extension output refine the existing indexed
capacity operation. Intersection, full-cell/query execution and finite-word
safety remain separate obligations, not assumptions or data fields.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedClosureRAM

open IndexedRAM

inductive Op where
  | base (instruction : Instruction)
  | subtract (target left right : Register)

abbrev Event := Primitive ⊕ Unit

def Op.execute (rom : ROM) : Op → State → State
  | .base instruction, state => instruction.execute rom state
  | .subtract target left right, state =>
      { state with
        register := Function.update state.register target (state.register left - state.register right)
        pc := state.pc + 5 }

def Op.trace : Op → List Event
  | .base instruction => instruction.trace.map Sum.inl
  | .subtract _ _ _ =>
      (List.replicate 5 Primitive.instructionWordRead ++
        [Primitive.decode, Primitive.pcAdd, Primitive.registerRead, Primitive.registerRead]).map Sum.inl ++
          [Sum.inr (), Sum.inl .registerWrite]

def execute (rom : ROM) : List Op → State → State
  | [], state => state
  | op :: rest, state => execute rom rest (op.execute rom state)

def trace (program : List Op) : List Event := program.flatMap Op.trace

theorem execute_append (rom : ROM) (left right : List Op) (state : State) :
    execute rom (left ++ right) state = execute rom right (execute rom left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons head rest ih => exact ih _

theorem trace_append (left right : List Op) : trace (left ++ right) = trace left ++ trace right :=
  List.flatMap_append

theorem execute_base (rom : ROM) (program : List Instruction) (state : State) :
    execute rom (program.map Op.base) state = IndexedRAM.execute rom program state := by
  induction program generalizing state with
  | nil => rfl
  | cons instruction rest ih => exact ih _

theorem trace_base_length (program : List Instruction) :
    (trace (program.map Op.base)).length = (primitiveTrace program).length := by
  induction program with
  | nil => rfl
  | cons instruction rest ih =>
    simp only [List.map_cons, trace, primitiveTrace, List.flatMap_cons, List.length_append,
      Op.trace, List.length_map] at *
    exact congrArg (instruction.trace.length + ·) ih

theorem execute_pc (rom : ROM) (program : List Op) (state : State) :
    (execute rom program state).pc = state.pc + 5 * program.length := by
  induction program generalizing state with
  | nil => simp only [execute, List.length_nil, Nat.mul_zero, Nat.add_zero]
  | cons instruction rest ih =>
    rw [execute, ih]
    have hp : (instruction.execute rom state).pc = state.pc + 5 := by
      cases instruction <;> rfl
    rw [hp]
    simp only [List.length_cons]
    omega

def Op.encodeWords : Op → Vector Nat 5
  | .base instruction => instruction.encodeWords
  | .subtract target left right => ⟨#[8, target.word, left.word, right.word, 0], rfl⟩

def Op.decodeWords (words : Vector Nat 5) : Option Op :=
  if words[0] = 8 then do
    let target ← Register.fromWord words[1]
    let left ← Register.fromWord words[2]
    let right ← Register.fromWord words[3]
    return .subtract target left right
  else (Instruction.decodeWords words).map Op.base

theorem Op.decodeWords_encodeWords (op : Op) : Op.decodeWords op.encodeWords = some op := by
  cases op with
  | base instruction =>
    have htag : instruction.encodeWords[0] ≠ 8 := by cases instruction <;> simp [Instruction.encodeWords]
    simp only [Op.encodeWords, Op.decodeWords, htag, ↓reduceIte, Instruction.decodeWords_encodeWords, Option.map_some]
  | subtract target left right =>
    simp [Op.encodeWords, Op.decodeWords, Register.fromWord_word]

theorem Op.decodeWords_halt : Op.decodeWords haltWords = none := rfl

def programWords (program : List Op) : List Nat := program.flatMap (fun op => op.encodeWords.toArray.toList)

def haltingWords (program : List Op) : List Nat := programWords program ++ haltWords.toArray.toList

theorem programWords_length (program : List Op) : (programWords program).length = 5 * program.length := by
  induction program with
  | nil => rfl
  | cons op rest ih =>
    simp only [programWords, List.flatMap_cons, List.length_append, Array.length_toList,
      Vector.size_toArray, List.length_cons] at *
    omega

theorem programWords_fetch (program : List Op) (index position : Nat)
    (hindex : index < program.length) (hposition : position < 5) :
    (programWords program).getD (5 * index + position) 0 =
      ((program[index]'hindex).encodeWords.toArray.toList).getD position 0 := by
  induction program generalizing index with
  | nil => simp only [List.length_nil] at hindex; omega
  | cons op later ih =>
    have hhead : op.encodeWords.toArray.toList.length = 5 := by
      simp only [Array.length_toList, Vector.size_toArray]
    cases index with
    | zero =>
      simp only [programWords, List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getD_append _ _ _ _ (hhead.symm ▸ hposition)
    | succ index =>
      have htail : index < later.length := Nat.lt_of_succ_lt_succ hindex
      have hlarge : op.encodeWords.toArray.toList.length ≤ 5 * (index + 1) + position := by omega
      simp only [programWords, List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getD_append_right _ _ _ _ hlarge, hhead]
      have hsub : 5 * (index + 1) + position - 5 = 5 * index + position := by omega
      rw [hsub]
      exact ih index htail

theorem fetchWords_halting_body (program : List Op) (index : Nat) (hindex : index < program.length) :
    fetchWords (haltingWords program) (5 * index) = (program[index]'hindex).encodeWords := by
  apply Vector.ext
  intro position hposition
  change (Vector.ofFn _).get ⟨position, hposition⟩ = ((program[index]'hindex).encodeWords).get ⟨position, hposition⟩
  rw [cache_get_ofFn]
  change (programWords program ++ haltWords.toArray.toList).getD (5 * index + position) 0 = _
  rw [List.getD_append _ _ _ _ (by rw [programWords_length]; omega),
    programWords_fetch program index position hindex hposition,
    List.getD_eq_getElem _ 0 (by simpa only [Array.length_toList, Vector.size_toArray] using hposition)]
  rfl

theorem decode_halting_body (program : List Op) (index : Nat) (hindex : index < program.length) :
    Op.decodeWords (fetchWords (haltingWords program) (5 * index)) = some (program[index]'hindex) := by
  rw [fetchWords_halting_body program index hindex, Op.decodeWords_encodeWords]

theorem haltingWords_length (program : List Op) : (haltingWords program).length = 5 * program.length + 5 := by
  rw [haltingWords, List.length_append, programWords_length]
  rfl

/-- Parent node IDs are encoded as i+1; 0 is the terminal sentinel. The
sentinel's ROM cell is stored too, so no branch hides a memory operation. -/
def encodedNode {Tool : Type*} (cache : IndexedNodeCache Tool) : Option cache.NodeId → Nat
  | none => 0
  | some node => node.val + 1

def parentWord {Tool : Type*} (cache : IndexedNodeCache Tool) (index : Nat) : Nat :=
  if h : 0 < index ∧ index ≤ cache.nodes.size then
    encodedNode cache (cache.parents.get ⟨index - 1, by omega⟩) else 0

theorem parentWord_zero {Tool : Type*} (cache : IndexedNodeCache Tool) : parentWord cache 0 = 0 := by
  simp only [parentWord, Nat.lt_irrefl, false_and, ↓reduceDIte]

theorem parentWord_node {Tool : Type*} (cache : IndexedNodeCache Tool) (node : cache.NodeId) :
    parentWord cache (node.val + 1) = encodedNode cache (cache.parents.get node) := by
  have hh : 0 < node.val + 1 ∧ node.val + 1 ≤ cache.nodes.size := ⟨by omega, node.isLt⟩
  unfold parentWord
  rw [dite_eq_left hh]
  rfl

def ancestorBlock (parentOffset : Nat) : List Op :=
  [.subtract .index .address .total,
    .base (.loadHeap .value .index), .base (.constant .old 0),
    .base (.select .fresh .value .flag .old),
    .base (.select .flag .address .fresh .flag),
    .subtract .fresh .value .total,
    .base (.select .fresh .address .fresh .value),
    .base (.storeHeap .index .fresh),
    .base (.constant .index parentOffset), .base (.add .index .index .address),
    .base (.loadROM .children .address .index)]

theorem ancestorBlock_heap (rom : ROM) (parentOffset : Nat) (state : State) :
    (execute rom (ancestorBlock parentOffset) state).heap =
      Function.update state.heap (state.register .address - state.register .total)
        (if state.register .address = 0 then state.heap (state.register .address - state.register .total)
          else state.heap (state.register .address - state.register .total) - state.register .total) := rfl

theorem ancestorBlock_flag (rom : ROM) (parentOffset : Nat) (state : State) :
    (execute rom (ancestorBlock parentOffset) state).register .flag =
      if state.register .address = 0 then state.register .flag else
        if state.heap (state.register .address - state.register .total) = 0 then 0 else state.register .flag := rfl

theorem ancestorBlock_parent (rom : ROM) (parentOffset : Nat) (state : State) :
    (execute rom (ancestorBlock parentOffset) state).register .address =
      rom.read .children (parentOffset + state.register .address) := rfl

theorem ancestorBlock_one (rom : ROM) (parentOffset : Nat) (state : State) :
    (execute rom (ancestorBlock parentOffset) state).register .total = state.register .total := rfl

theorem ancestorBlock_length (parentOffset : Nat) : (ancestorBlock parentOffset).length = 11 := rfl

theorem ancestorBlock_trace_length (parentOffset : Nat) : (trace (ancestorBlock parentOffset)).length = 118 := rfl

def ancestorLoop (parentOffset fuel : Nat) : List Op :=
  (List.replicate fuel (ancestorBlock parentOffset)).flatten

theorem ancestorLoop_length (parentOffset fuel : Nat) :
    (ancestorLoop parentOffset fuel).length = 11 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [ancestorLoop, List.replicate_succ, List.flatten_cons, List.length_append, ancestorBlock_length]
    change 11 + (ancestorLoop parentOffset fuel).length = _
    rw [ih]
    omega

theorem ancestorLoop_trace_length (parentOffset fuel : Nat) :
    (trace (ancestorLoop parentOffset fuel)).length = 118 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [ancestorLoop, List.replicate_succ, List.flatten_cons, trace_append, List.length_append,
      ancestorBlock_trace_length]
    change 118 + (trace (ancestorLoop parentOffset fuel)).length = _
    rw [ih]
    omega

def extensionInit (size : Nat) : List Op :=
  [.base (.constant .index size), .base (.loadROM .input .flag .index),
    .base (.constant .index (size + 1)), .base (.loadROM .input .address .index),
    .base (.constant .old 0), .base (.select .flag .address .flag .old), .base (.constant .total 1)]

def extensionTail (size : Nat) : List Op :=
  [.base (.constant .index size), .base (.storeHeap .index .flag)]

def extensionProgram (size parentOffset : Nat) : List Op :=
  (copyProgram size).map Op.base ++ extensionInit size ++ ancestorLoop parentOffset size ++ extensionTail size

theorem extensionProgram_length (size parentOffset : Nat) :
    (extensionProgram size parentOffset).length = 14 * size + 9 := by
  rw [extensionProgram]
  simp only [List.length_append, List.length_map, copyProgram_length, extensionInit,
    extensionTail, List.length_cons, List.length_nil, ancestorLoop_length]
  omega

theorem extensionProgram_trace_length (size parentOffset : Nat) :
    (trace (extensionProgram size parentOffset)).length = 148 * size + 85 := by
  have hi : (trace (extensionInit size)).length = 66 := rfl
  have ht : (trace (extensionTail size)).length = 19 := rfl
  simp only [extensionProgram, trace_append, List.length_append, trace_base_length,
    copyProgram_trace_length, hi, ancestorLoop_trace_length, ht]
  omega

theorem extensionProgram_withHalt_trace_le (size parentOffset : Nat) (hsize : 0 < size) :
    (trace (extensionProgram size parentOffset)).length + terminalTrace.length ≤ 239 * size := by
  rw [extensionProgram_trace_length, terminalTrace_length]
  omega

theorem extensionProgram_codeWords (size parentOffset : Nat) :
    (haltingWords (extensionProgram size parentOffset)).length = 70 * size + 50 := by
  rw [haltingWords_length, extensionProgram_length]
  omega

structure WalkState {Tool : Type*} (cache : IndexedNodeCache Tool) where
  heap : Nat → Nat
  flag : Nat
  current : Option cache.NodeId

def walkStep {Tool : Type*} {cache : IndexedNodeCache Tool} (state : WalkState cache) : WalkState cache :=
  match state.current with
  | none => state
  | some node => {
      heap := Function.update state.heap node.val (state.heap node.val - 1)
      flag := if state.heap node.val = 0 then 0 else state.flag
      current := cache.parents.get node }

def walk {Tool : Type*} {cache : IndexedNodeCache Tool} : Nat → WalkState cache → WalkState cache
  | 0, state => state
  | fuel + 1, state => walk fuel (walkStep state)

def Represents {Tool : Type*} {cache : IndexedNodeCache Tool} (machine : State) (value : WalkState cache) : Prop :=
  machine.heap = value.heap ∧ machine.register .flag = value.flag ∧
    machine.register .address = encodedNode cache value.current ∧ machine.register .total = 1

def ParentROMFor {Tool : Type*} (cache : IndexedNodeCache Tool) (offset : Nat) (rom : ROM) : Prop :=
  rom.read .children offset = 0 ∧
    ∀ node : cache.NodeId, rom.read .children (offset + (node.val + 1)) = encodedNode cache (cache.parents.get node)

theorem ancestorBlock_represents {Tool : Type*} (cache : IndexedNodeCache Tool) (rom : ROM)
    (offset : Nat) (hrom : ParentROMFor cache offset rom) (machine : State) (value : WalkState cache)
    (hvalue : Represents machine value) :
    Represents (execute rom (ancestorBlock offset) machine) (walkStep value) := by
  obtain ⟨hh, hf, ha, hone⟩ := hvalue
  cases hc : value.current with
  | none =>
    have haddr : machine.register .address = 0 := ha.trans (by rw [hc]; rfl)
    have hheap : (execute rom (ancestorBlock offset) machine).heap = value.heap := by
      rw [ancestorBlock_heap, haddr]
      simp only [Nat.zero_sub, ite_true, hh]
      exact Function.update_eq_self _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [walkStep, hc] using hheap
    · simpa only [walkStep, hc, ancestorBlock_flag, haddr, ite_true] using hf
    · simpa only [walkStep, hc, ancestorBlock_parent, haddr, Nat.add_zero, encodedNode] using hrom.1
    · exact (ancestorBlock_one rom offset machine).trans hone
  | some node =>
    have haddr : machine.register .address = node.val + 1 := ha.trans (by rw [hc]; rfl)
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [walkStep, hc, ancestorBlock_heap, haddr, hone, hh, Nat.add_sub_cancel,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    · simp only [walkStep, hc, ancestorBlock_flag, haddr, hone, hh, hf, Nat.add_sub_cancel,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
    · simpa only [walkStep, hc, ancestorBlock_parent, haddr] using hrom.2 node
    · exact (ancestorBlock_one rom offset machine).trans hone

theorem ancestorLoop_represents {Tool : Type*} (cache : IndexedNodeCache Tool) (rom : ROM)
    (offset fuel : Nat) (hrom : ParentROMFor cache offset rom) (machine : State) (value : WalkState cache)
    (hvalue : Represents machine value) :
    Represents (execute rom (ancestorLoop offset fuel) machine) (walk fuel value) := by
  induction fuel generalizing machine value with
  | zero => exact hvalue
  | succ fuel ih =>
    rw [ancestorLoop, List.replicate_succ, List.flatten_cons, execute_append]
    exact ih _ _ (ancestorBlock_represents cache rom offset hrom machine value hvalue)

theorem walk_none {Tool : Type*} {cache : IndexedNodeCache Tool} (fuel : Nat) (state : WalkState cache)
    (hnone : state.current = none) : walk fuel state = state := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [walk, walkStep, hnone] using ih

theorem update_heap_agrees {Tool : Type*} (cache : IndexedNodeCache Tool)
    (heap : Nat → Nat) (capacity : IndexedCapacity cache) (node : cache.NodeId)
    (hagrees : HeapAgrees heap capacity) :
    HeapAgrees (Function.update heap node.val (heap node.val - 1))
      (capacity.set node.val (capacity.get node - 1) node.isLt) := by
  intro target
  rw [vector_set_get]
  by_cases heq : target = node
  · subst target
    rw [Function.update_self, hagrees, ite_eq_left rfl]
  · rw [Function.update_of_ne (fun hh => heq (Fin.ext hh)), ite_eq_right heq]
    exact hagrees target

/-- The full loop's payload is precisely the pre-existing vector operation,
not a fresh definition of extension/capacity semantics. This proof requires
no initial correct-count or correctly-decremented-heap assumption. -/
theorem walk_heap_decrementNodes {Tool : Type*} (cache : IndexedNodeCache Tool) (fuel : Nat)
    (node : cache.NodeId) (heap : Nat → Nat) (capacity : IndexedCapacity cache) (flag : Nat)
    (hagrees : HeapAgrees heap capacity) :
    HeapAgrees (walk fuel (⟨heap, flag, some node⟩ : WalkState cache)).heap
      (IndexedAncestors.decrementNodes cache (IndexedAncestors.parentChain cache fuel node) capacity) := by
  induction fuel generalizing node heap capacity flag with
  | zero => exact hagrees
  | succ fuel ih =>
    have hupdated := update_heap_agrees cache heap capacity node hagrees
    cases hp : cache.parents.get node with
    | none =>
      rw [walk]
      have hn : (walkStep (⟨heap, flag, some node⟩ : WalkState cache)).current = none := hp
      rw [walk_none fuel _ hn]
      simpa only [walkStep, IndexedAncestors.parentChain, hp, IndexedAncestors.decrementNodes] using hupdated
    | some parent =>
      simpa only [walk, walkStep, IndexedAncestors.parentChain, hp,
        IndexedAncestors.decrementNodes] using ih parent _ _ _ hupdated

theorem ancestorLoop_payload_refines {Tool : Type*} (cache : IndexedNodeCache Tool) (rom : ROM)
    (offset : Nat) (hrom : ParentROMFor cache offset rom) (node : cache.NodeId)
    (machine : State) (capacity : IndexedCapacity cache)
    (hheap : HeapAgrees machine.heap capacity) (ha : machine.register .address = node.val + 1)
    (hone : machine.register .total = 1) :
    HeapAgrees (execute rom (ancestorLoop offset cache.nodes.size) machine).heap
      (IndexedAncestors.chainDecrement cache capacity node) := by
  let value : WalkState cache := ⟨machine.heap, machine.register .flag, some node⟩
  have hv : Represents machine value := ⟨rfl, rfl, ha, hone⟩
  have hh := (ancestorLoop_represents cache rom offset cache.nodes.size hrom machine value hv).1
  rw [hh]
  exact walk_heap_decrementNodes cache cache.nodes.size node machine.heap capacity _ hheap

def decrementFlag {Tool : Type*} (cache : IndexedNodeCache Tool) :
    List cache.NodeId → IndexedCapacity cache → Nat → Nat
  | [], _, flag => flag
  | node :: later, capacity, flag =>
      decrementFlag cache later (capacity.set node.val (capacity.get node - 1) node.isLt)
        (if capacity.get node = 0 then 0 else flag)

theorem walk_flag_decrementFlag {Tool : Type*} (cache : IndexedNodeCache Tool) (fuel : Nat)
    (node : cache.NodeId) (heap : Nat → Nat) (capacity : IndexedCapacity cache) (flag : Nat)
    (hagrees : HeapAgrees heap capacity) :
    (walk fuel (⟨heap, flag, some node⟩ : WalkState cache)).flag =
      decrementFlag cache (IndexedAncestors.parentChain cache fuel node) capacity flag := by
  induction fuel generalizing node heap capacity flag with
  | zero => rfl
  | succ fuel ih =>
    have hupdated := update_heap_agrees cache heap capacity node hagrees
    cases hp : cache.parents.get node with
    | none =>
      rw [walk]
      have hn : (walkStep (⟨heap, flag, some node⟩ : WalkState cache)).current = none := hp
      rw [walk_none fuel _ hn]
      simp only [walkStep, IndexedAncestors.parentChain, hp, decrementFlag, hagrees node]
    | some parent =>
      simpa only [walk, walkStep, IndexedAncestors.parentChain, hp, decrementFlag, hagrees node] using
        ih parent _ _ _ hupdated

theorem decrementFlag_nodup {Tool : Type*} (cache : IndexedNodeCache Tool)
    (nodes : List cache.NodeId) (hnodup : nodes.Nodup) (capacity : IndexedCapacity cache) (flag : Nat) :
    decrementFlag cache nodes capacity flag =
      if ∃ node ∈ nodes, capacity.get node = 0 then 0 else flag := by
  induction nodes generalizing capacity flag with
  | nil => simp only [decrementFlag, List.not_mem_nil, false_and, exists_false, ite_false]
  | cons node later ih =>
    rw [decrementFlag, ih (List.nodup_cons.mp hnodup).2]
    have htail :
        (∃ target ∈ later, ((capacity.set node.val (capacity.get node - 1) node.isLt).get target) = 0) ↔
          ∃ target ∈ later, capacity.get target = 0 := by
      apply exists_congr
      intro target
      apply and_congr_right
      intro ht
      have hne : target ≠ node := fun heq => (List.nodup_cons.mp hnodup).1 (heq ▸ ht)
      rw [vector_set_get, ite_eq_right hne]
    have hcons : (∃ target ∈ node :: later, capacity.get target = 0) ↔
        capacity.get node = 0 ∨ ∃ target ∈ later, capacity.get target = 0 := by
      constructor
      · rintro ⟨target, ht, hz⟩
        rcases List.mem_cons.mp ht with heq | hm
        · exact Or.inl (heq ▸ hz)
        · exact Or.inr ⟨target, hm, hz⟩
      · rintro (hz | ⟨target, hm, hz⟩)
        · exact ⟨node, List.mem_cons_self, hz⟩
        · exact ⟨target, List.mem_cons_of_mem _ hm, hz⟩
    simp only [htail, hcons]
    by_cases hz : capacity.get node = 0 <;> simp only [hz, ite_true, ite_false, true_or, false_or]
    · split_ifs <;> rfl

theorem ancestorLoop_flag_refines {Tool : Type*} (cache : IndexedNodeCache Tool) (rom : ROM)
    (offset : Nat) (hrom : ParentROMFor cache offset rom) (node : cache.NodeId)
    (hnodup : (IndexedAncestors.ancestorChain cache node).Nodup)
    (machine : State) (capacity : IndexedCapacity cache)
    (hheap : HeapAgrees machine.heap capacity) (ha : machine.register .address = node.val + 1)
    (hone : machine.register .total = 1) :
    (execute rom (ancestorLoop offset cache.nodes.size) machine).register .flag =
      if IndexedAncestors.chainZero cache capacity node then 0 else machine.register .flag := by
  let value : WalkState cache := ⟨machine.heap, machine.register .flag, some node⟩
  have hv : Represents machine value := ⟨rfl, rfl, ha, hone⟩
  have hf := (ancestorLoop_represents cache rom offset cache.nodes.size hrom machine value hv).2.1
  rw [hf, walk_flag_decrementFlag cache cache.nodes.size node machine.heap capacity _ hheap]
  change decrementFlag cache (IndexedAncestors.ancestorChain cache node) capacity (machine.register .flag) = _
  rw [decrementFlag_nodup cache _ hnodup]
  simp only [IndexedAncestors.chainZero, List.any_eq_true, decide_eq_true_eq]

def parentWords {Tool : Type*} (cache : IndexedNodeCache Tool) : Array Nat :=
  Array.ofFn (fun index : Fin (cache.nodes.size + 1) => parentWord cache index.val)

theorem parentWords_get {Tool : Type*} (cache : IndexedNodeCache Tool) (index : Nat)
    (hi : index < cache.nodes.size + 1) :
    (parentWords cache).getD index 0 = parentWord cache index := by
  simp [parentWords, Array.getD, hi]

def entryWord {Tool : Type*} (cache : IndexedNodeCache Tool)
    (entry : IndexedEntry.FixedEntry cache) (node : Option cache.NodeId) (index : Nat) : Nat :=
  if hi : index < cache.nodes.size then
    match entry with
    | .void => 0
    | .vector capacity => capacity.get ⟨index, hi⟩
  else if index = cache.nodes.size then
    match entry with | .void => 0 | .vector _ => 1
  else if index = cache.nodes.size + 1 then encodedNode cache node else 0

def extensionROM {Tool : Type*} (cache : IndexedNodeCache Tool)
    (entry : IndexedEntry.FixedEntry cache) (node : Option cache.NodeId) : ROM :=
  { read := fun region index => match region with
      | .input => entryWord cache entry node index
      | .internal => 0
      | .children => (parentWords cache).getD index 0 }

theorem extensionROM_parent {Tool : Type*} (cache : IndexedNodeCache Tool)
    (entry : IndexedEntry.FixedEntry cache) (node : Option cache.NodeId) :
    ParentROMFor cache 0 (extensionROM cache entry node) := by
  constructor
  · change (parentWords cache).getD 0 0 = 0
    rw [parentWords_get cache 0 (by omega), parentWord_zero]
  · intro target
    change (parentWords cache).getD (0 + (target.val + 1)) 0 = _
    rw [Nat.zero_add, parentWords_get cache (target.val + 1) (by omega), parentWord_node]

theorem extensionInit_heap (rom : ROM) (size : Nat) (state : State) :
    (execute rom (extensionInit size) state).heap = state.heap := rfl

theorem extensionInit_flag (rom : ROM) (size : Nat) (state : State) :
    (execute rom (extensionInit size) state).register .flag =
      if rom.read .input (size + 1) = 0 then 0 else rom.read .input size := rfl

theorem extensionInit_address (rom : ROM) (size : Nat) (state : State) :
    (execute rom (extensionInit size) state).register .address = rom.read .input (size + 1) := rfl

theorem extensionInit_one (rom : ROM) (size : Nat) (state : State) :
    (execute rom (extensionInit size) state).register .total = 1 := rfl

theorem extensionTail_heap (rom : ROM) (size : Nat) (state : State) :
    (execute rom (extensionTail size) state).heap = Function.update state.heap size (state.register .flag) := rfl

def readCapacity {Tool : Type*} (cache : IndexedNodeCache Tool) (heap : Nat → Nat) : IndexedCapacity cache :=
  Vector.ofFn (fun node => heap node.val)

theorem readCapacity_eq {Tool : Type*} (cache : IndexedNodeCache Tool) (heap : Nat → Nat)
    (capacity : IndexedCapacity cache) (hagrees : HeapAgrees heap capacity) :
    readCapacity cache heap = capacity := by
  apply Vector.ext
  intro index hi
  change (readCapacity cache heap).get ⟨index, hi⟩ = capacity.get ⟨index, hi⟩
  rw [readCapacity, cache_get_ofFn]
  exact hagrees _

def decodeResult {Tool : Type*} (cache : IndexedNodeCache Tool) (heap : Nat → Nat) : IndexedEntry.FixedEntry cache :=
  if heap cache.nodes.size = 0 then .void else .vector (readCapacity cache heap)

def extensionStart {Tool : Type*} (cache : IndexedNodeCache Tool) (entry : IndexedEntry.FixedEntry cache)
    (node : Option cache.NodeId) (initial : State) : State :=
  let rom := extensionROM cache entry node
  execute rom (extensionInit cache.nodes.size) (IndexedRAM.execute rom (copyProgram cache.nodes.size) initial)

def extensionResult {Tool : Type*} (cache : IndexedNodeCache Tool) (entry : IndexedEntry.FixedEntry cache)
    (node : Option cache.NodeId) (initial : State) : IndexedEntry.FixedEntry cache :=
  decodeResult cache (execute (extensionROM cache entry node) (extensionProgram cache.nodes.size 0) initial).heap

theorem entryWord_tag {Tool : Type*} (cache : IndexedNodeCache Tool) (entry : IndexedEntry.FixedEntry cache)
    (node : Option cache.NodeId) : entryWord cache entry node cache.nodes.size =
      match entry with | .void => 0 | .vector _ => 1 := by
  simp only [entryWord, Nat.lt_irrefl, ↓reduceDIte, ite_true]

theorem entryWord_start {Tool : Type*} (cache : IndexedNodeCache Tool) (entry : IndexedEntry.FixedEntry cache)
    (node : Option cache.NodeId) : entryWord cache entry node (cache.nodes.size + 1) = encodedNode cache node := by
  simp [entryWord]

theorem extensionStart_registers {Tool : Type*} (cache : IndexedNodeCache Tool) (entry : IndexedEntry.FixedEntry cache)
    (node : Option cache.NodeId) (initial : State) :
    (extensionStart cache entry node initial).register .address = encodedNode cache node ∧
    (extensionStart cache entry node initial).register .total = 1 ∧
    (extensionStart cache entry node initial).register .flag =
      if encodedNode cache node = 0 then 0 else match entry with | .void => 0 | .vector _ => 1 := by
  simp only [extensionStart, extensionInit_address, extensionInit_one, extensionInit_flag, extensionROM,
    entryWord_start, entryWord_tag, and_self]

theorem extensionStart_payload {Tool : Type*} (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (node : Option cache.NodeId) (initial : State) :
    HeapAgrees (extensionStart cache (.vector capacity) node initial).heap capacity := by
  intro target
  rw [extensionStart, extensionInit_heap, execute_copyProgram_heap, ite_eq_left target.isLt]
  change entryWord cache (.vector capacity) node target.val = capacity.get target
  simp only [entryWord, target.isLt, ↓reduceDIte]

theorem extension_execute_split {Tool : Type*} (cache : IndexedNodeCache Tool) (entry : IndexedEntry.FixedEntry cache)
    (node : Option cache.NodeId) (initial : State) :
    execute (extensionROM cache entry node) (extensionProgram cache.nodes.size 0) initial =
      execute (extensionROM cache entry node) (extensionTail cache.nodes.size)
        (execute (extensionROM cache entry node) (ancestorLoop 0 cache.nodes.size)
          (extensionStart cache entry node initial)) := by
  simp only [extensionProgram, execute_append, execute_base, extensionStart]

theorem walk_zero_flag {Tool : Type*} {cache : IndexedNodeCache Tool} (fuel : Nat) (value : WalkState cache)
    (hz : value.flag = 0) : (walk fuel value).flag = 0 := by
  induction fuel generalizing value with
  | zero => exact hz
  | succ fuel ih =>
    apply ih
    cases hc : value.current <;> simp only [walkStep, hc, hz, ite_self]

theorem extensionResult_void_of_flag {Tool : Type*} (cache : IndexedNodeCache Tool)
    (entry : IndexedEntry.FixedEntry cache) (node : Option cache.NodeId) (initial : State)
    (hz : (extensionStart cache entry node initial).register .flag = 0) :
    extensionResult cache entry node initial = .void := by
  let start := extensionStart cache entry node initial
  let value : WalkState cache := ⟨start.heap, 0, node⟩
  have hs := extensionStart_registers cache entry node initial
  have hv : Represents start value := ⟨rfl, hz, hs.1, hs.2.1⟩
  have hf := (ancestorLoop_represents cache _ 0 cache.nodes.size
    (extensionROM_parent cache entry node) start value hv).2.1
  have hzero : (execute (extensionROM cache entry node) (ancestorLoop 0 cache.nodes.size) start).register .flag = 0 :=
    hf.trans (walk_zero_flag _ value rfl)
  unfold extensionResult
  rw [extension_execute_split, extensionTail_heap]
  unfold decodeResult
  rw [Function.update_self, hzero]
  rfl

theorem extensionResult_void {Tool : Type*} (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (initial : State) : extensionResult cache .void node initial = .void := by
  apply extensionResult_void_of_flag
  rw [(extensionStart_registers cache .void node initial).2.2]
  split_ifs <;> rfl

theorem extensionResult_none {Tool : Type*} (cache : IndexedNodeCache Tool)
    (entry : IndexedEntry.FixedEntry cache) (initial : State) : extensionResult cache entry none initial = .void := by
  apply extensionResult_void_of_flag
  rw [(extensionStart_registers cache entry none initial).2.2]
  rfl

theorem extensionResult_vector {Tool : Type*} (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache)
    (node : cache.NodeId) (hnodup : (IndexedAncestors.ancestorChain cache node).Nodup) (initial : State) :
    extensionResult cache (.vector capacity) (some node) initial =
      if IndexedAncestors.chainZero cache capacity node then .void
        else .vector (IndexedAncestors.chainDecrement cache capacity node) := by
  let rom := extensionROM cache (.vector capacity) (some node)
  let start := extensionStart cache (.vector capacity) (some node) initial
  let result := execute rom (ancestorLoop 0 cache.nodes.size) start
  have hs := extensionStart_registers cache (.vector capacity) (some node) initial
  have ha : start.register .address = node.val + 1 := hs.1
  have hone : start.register .total = 1 := hs.2.1
  have hflag : start.register .flag = 1 := by
    rw [hs.2.2]
    simp only [encodedNode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
  have hh : HeapAgrees result.heap (IndexedAncestors.chainDecrement cache capacity node) :=
    ancestorLoop_payload_refines cache rom 0 (extensionROM_parent cache _ _) node start capacity
      (extensionStart_payload cache capacity (some node) initial) ha hone
  have hf : result.register .flag = if IndexedAncestors.chainZero cache capacity node then 0 else 1 := by
    rw [ancestorLoop_flag_refines cache rom 0 (extensionROM_parent cache _ _) node hnodup start capacity
      (extensionStart_payload cache capacity (some node) initial) ha hone, hflag]
  have hfinal : HeapAgrees (Function.update result.heap cache.nodes.size (result.register .flag))
      (IndexedAncestors.chainDecrement cache capacity node) := by
    intro target
    rw [Function.update_of_ne (Nat.ne_of_lt target.isLt)]
    exact hh target
  unfold extensionResult
  rw [extension_execute_split, extensionTail_heap]
  change decodeResult cache (Function.update result.heap cache.nodes.size (result.register .flag)) = _
  unfold decodeResult
  rw [Function.update_self, readCapacity_eq cache _ _ hfinal, hf]
  by_cases hz : IndexedAncestors.chainZero cache capacity node = true <;> simp [hz]

/-- Actual prepared-cache extension, including VOID, zero capacities and
empty compatibility. Node IDs are supplied by the existing static cache. -/
theorem prepared_extensionResult_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (node : Option (prepareNormalization q full).indexed.NodeId) (initial : State) :
    extensionResult (prepareNormalization q full).indexed entry node initial =
      IndexedStaticMetadata.extendAt (prepareNormalization q full).indexed node entry := by
  cases entry with
  | void => exact extensionResult_void _ node initial
  | vector capacity =>
    cases node with
    | none => exact extensionResult_none _ (.vector capacity) initial
    | some node =>
      exact extensionResult_vector _ capacity node
        (IndexedAncestors.prepared_ancestorChain_nodup q full hq hlaminar node) initial

inductive Runs (rom : ROM) : List Op → State → State → List Event → Prop where
  | nil (state : State) : Runs rom [] state state []
  | step (op : Op) (rest : List Op) (state final : State) (tail : List Event)
      (continuation : Runs rom rest (op.execute rom state) final tail) :
      Runs rom (op :: rest) state final (op.trace ++ tail)

theorem runs_execute (rom : ROM) (program : List Op) (initial : State) :
    Runs rom program initial (execute rom program initial) (trace program) := by
  induction program generalizing initial with
  | nil => exact .nil initial
  | cons op rest ih => exact .step op rest initial _ _ (ih _)

theorem fetchWords_halting_terminal (program : List Op) :
    fetchWords (haltingWords program) (5 * program.length) = haltWords := by
  apply Vector.ext
  intro position hposition
  change (Vector.ofFn _).get ⟨position, hposition⟩ = haltWords.get ⟨position, hposition⟩
  rw [cache_get_ofFn]
  change (programWords program ++ haltWords.toArray.toList).getD (5 * program.length + position) 0 = _
  rw [List.getD_append_right _ _ _ _ (by rw [programWords_length]; omega), programWords_length]
  rw [Nat.add_sub_cancel_left, List.getD_eq_getElem _ 0 (by
    simpa only [Array.length_toList, Vector.size_toArray] using hposition)]
  rfl

def haltTrace : List Event := terminalTrace.map Sum.inl

theorem haltTrace_length : haltTrace.length = 6 := by rw [haltTrace, List.length_map, terminalTrace_length]

inductive HaltingRuns (rom : ROM) (program : List Op) (initial final : State) : List Event → Prop where
  | halt (bodyTrace : List Event) (body : Runs rom program initial final bodyTrace)
      (decodedHalt : Op.decodeWords (fetchWords (haltingWords program) final.pc) = none) :
      HaltingRuns rom program initial final (bodyTrace ++ haltTrace)

theorem execute_halts (rom : ROM) (program : List Op) (initial : State) (hpc : initial.pc = 0) :
    HaltingRuns rom program initial (execute rom program initial) (trace program ++ haltTrace) := by
  apply HaltingRuns.halt _ (runs_execute rom program initial)
  rw [execute_pc, hpc, Nat.zero_add, fetchWords_halting_terminal, Op.decodeWords_halt]

/-- The original prepared-tree extension has an actual coded halting
execution, correct VOID/vector output, and a charged O(t) primitive trace.
This remains a Nat-address RAM theorem: finite-word safety, the intersection
operation and full table/query execution are separate obligations. -/
theorem prepared_extension_halting_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (node : Option (prepareNormalization q full).indexed.NodeId) (initial : State) (hpc : initial.pc = 0) :
    ∃ final operations,
      HaltingRuns (extensionROM (prepareNormalization q full).indexed entry node)
        (extensionProgram (prepareNormalization q full).indexed.nodes.size 0) initial final operations ∧
      decodeResult (prepareNormalization q full).indexed final.heap =
        IndexedStaticMetadata.extendAt (prepareNormalization q full).indexed node entry ∧
      operations.length ≤ 239 * (prepareNormalization q full).indexed.nodes.size := by
  refine ⟨_, _, execute_halts _ _ initial hpc,
    prepared_extensionResult_eq q full hq hlaminar entry node initial, ?_⟩
  rw [List.length_append, haltTrace_length, extensionProgram_trace_length]
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hp : 0 < (prepareNormalization q full).indexed.nodes.size :=
    Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  omega

/-- The actual cached stage-node lookup refines the original full-input
capacity extension, rather than requiring an extra representation premise. -/
theorem prepared_stage_extension_halting_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin full.length)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (initial : State) (hpc : initial.pc = 0) :
    let node := (IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage
    ∃ final operations,
      HaltingRuns (extensionROM (prepareNormalization q full).indexed entry node)
        (extensionProgram (prepareNormalization q full).indexed.nodes.size 0) initial final operations ∧
      decodeResult (prepareNormalization q full).indexed final.heap =
        IndexedEntry.extend (prepareNormalization q full).indexed full[stage.val] entry ∧
      operations.length ≤ 239 * (prepareNormalization q full).indexed.nodes.size := by
  dsimp only
  rw [← IndexedStaticMetadata.buildPositive_extendAt_eq_indexed q full hq hlaminar stage entry]
  exact prepared_extension_halting_run q full hq hlaminar entry _ initial hpc

end PaperProofs.Structure.LaminarTree.IndexedClosureRAM
