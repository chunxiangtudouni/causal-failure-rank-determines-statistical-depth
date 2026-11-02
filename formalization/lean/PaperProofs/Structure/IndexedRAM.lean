module

public import PaperProofs.Structure.IndexedTreeMetadata
public import Mathlib.Data.List.GetD
import Lean.Elab.Tactic.Omega

/-!
Workpad: a word-RAM implementation and pure-evaluator refinement.

The target machine has three readonly ROM regions and a writable heap. A
heap write is an explicit RAM primitive with Function.update semantics. This
is not a complexity claim about Lean's host functions, persistent Vectors or
Array copying. Region base addition, instruction-word fetches, program-counter
advance, register reads/writes, arithmetic and memory accesses are all emitted
in the primitive trace. The static tree program is compiled once; every pass
explicitly copies its input into writable memory before running normalization.
Natural-address encoding bounds and word-value bounds are separate proofs.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedRAM

inductive Region where
  | input | internal | children
  deriving DecidableEq

inductive Register where
  | address | index | value | total | old | fresh | flag
  deriving DecidableEq

structure ROM where
  read : Region → Nat → Nat

structure State where
  register : Register → Nat
  heap : Nat → Nat
  pc : Nat

inductive Instruction where
  | constant (target : Register) (value : Nat)
  | add (target left right : Register)
  | minimum (target left right : Register)
  | select (target condition whenTrue whenFalse : Register)
  | loadROM (region : Region) (target pointer : Register)
  | loadHeap (target pointer : Register)
  | storeHeap (pointer source : Register)

/-- Observable elementary word operations, including dispatch overhead.
Each instruction has a padded five-word encoding; reading each code word,
decoding, and adding five to the program counter are explicitly counted. -/
inductive Primitive where
  | instructionWordRead | decode | pcAdd
  | registerRead | registerWrite | addressAdd
  | readonlyRead | heapRead | heapWrite
  | integerAdd | integerMin | conditionalSelect
  deriving DecidableEq

def Instruction.operations : Instruction → List Primitive
  | .constant _ _ => [.registerWrite]
  | .add _ _ _ => [.registerRead, .registerRead, .integerAdd, .registerWrite]
  | .minimum _ _ _ => [.registerRead, .registerRead, .integerMin, .registerWrite]
  | .select _ _ _ _ => [.registerRead, .registerRead, .registerRead, .conditionalSelect, .registerWrite]
  | .loadROM _ _ _ => [.registerRead, .addressAdd, .readonlyRead, .registerWrite]
  | .loadHeap _ _ => [.registerRead, .addressAdd, .heapRead, .registerWrite]
  | .storeHeap _ _ => [.registerRead, .registerRead, .addressAdd, .heapWrite]

def Instruction.trace (instruction : Instruction) : List Primitive :=
  List.replicate 5 .instructionWordRead ++ [.decode, .pcAdd] ++ instruction.operations

def Instruction.execute (rom : ROM) (instruction : Instruction) (state : State) : State :=
  let registers := state.register
  let after := match instruction with
    | .constant target value => { state with register := Function.update registers target value }
    | .add target left right =>
        { state with register := Function.update registers target (registers left + registers right) }
    | .minimum target left right =>
        { state with register := Function.update registers target (min (registers left) (registers right)) }
    | .select target condition whenTrue whenFalse =>
        { state with register := Function.update registers target (if registers condition = 0 then registers whenFalse else registers whenTrue) }
    | .loadROM region target pointer =>
        { state with register := Function.update registers target (rom.read region (registers pointer)) }
    | .loadHeap target pointer =>
        { state with register := Function.update registers target (state.heap (registers pointer)) }
    | .storeHeap pointer source =>
        { state with heap := Function.update state.heap (registers pointer) (registers source) }
  { after with pc := state.pc + 5 }

def execute (rom : ROM) : List Instruction → State → State
  | [], state => state
  | instruction :: later, state => execute rom later (instruction.execute rom state)

def primitiveTrace (program : List Instruction) : List Primitive := program.flatMap Instruction.trace

theorem execute_append (rom : ROM) (left right : List Instruction) (state : State) :
    execute rom (left ++ right) state = execute rom right (execute rom left state) := by
  induction left generalizing state with
  | nil => rfl
  | cons instruction later ih => exact ih _

theorem execute_pc (rom : ROM) (program : List Instruction) (state : State) :
    (execute rom program state).pc = state.pc + 5 * program.length := by
  induction program generalizing state with
  | nil => simp only [execute, List.length_nil, Nat.mul_zero, Nat.add_zero]
  | cons instruction later ih =>
    rw [execute, ih]
    simp only [Instruction.execute, List.length_cons]
    omega

def copyBlock (index : Nat) : List Instruction :=
  [.constant .index index, .loadROM .input .value .index, .storeHeap .index .value]

def childBlock (offset position : Nat) : List Instruction :=
  [.constant .address offset, .constant .index position, .add .address .address .index,
    .loadROM .children .index .address, .loadHeap .value .index, .add .total .total .value]

def nodeHeader (parent : Nat) : List Instruction :=
  [.constant .index parent, .loadROM .internal .flag .index, .constant .total 0]

def nodeTail (parent : Nat) : List Instruction :=
  [.constant .index parent, .loadHeap .old .index, .minimum .fresh .old .total,
    .select .fresh .flag .fresh .old, .storeHeap .index .fresh]

def copyProgram (size : Nat) : List Instruction := (List.range size).flatMap copyBlock

def nodeProgram (parent offset degree : Nat) : List Instruction :=
  nodeHeader parent ++ (List.range degree).flatMap (childBlock offset) ++ nodeTail parent

def compileNodes {Tool : Type*} (cache : IndexedNodeCache Tool) : List cache.NodeId → Nat → List Instruction
  | [], _ => []
  | parent :: later, offset => nodeProgram parent.val offset (cache.children.get parent).size ++
      compileNodes cache later (offset + (cache.children.get parent).size)

def normalizationProgram {Tool : Type*} (cache : IndexedNodeCache Tool) : List Instruction :=
  copyProgram cache.nodes.size ++ compileNodes cache (List.finRange cache.nodes.size) 0

theorem copyBlock_length (index : Nat) : (copyBlock index).length = 3 := rfl
theorem childBlock_length (offset position : Nat) : (childBlock offset position).length = 6 := rfl
theorem nodeHeader_length (parent : Nat) : (nodeHeader parent).length = 3 := rfl
theorem nodeTail_length (parent : Nat) : (nodeTail parent).length = 5 := rfl

theorem copyBlock_trace_length (index : Nat) : (primitiveTrace (copyBlock index)).length = 30 := rfl
theorem childBlock_trace_length (offset position : Nat) : (primitiveTrace (childBlock offset position)).length = 60 := rfl
theorem nodeHeader_trace_length (parent : Nat) : (primitiveTrace (nodeHeader parent)).length = 27 := rfl
theorem nodeTail_trace_length (parent : Nat) : (primitiveTrace (nodeTail parent)).length = 53 := rfl

theorem nodeProgram_length (parent offset degree : Nat) :
    (nodeProgram parent offset degree).length = 8 + 6 * degree := by
  simp only [nodeProgram, List.length_append, nodeHeader_length, nodeTail_length, List.length_flatMap,
    childBlock_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem primitiveTrace_append (left right : List Instruction) :
    primitiveTrace (left ++ right) = primitiveTrace left ++ primitiveTrace right := List.flatMap_append

theorem primitiveTrace_length_flatMap {α : Type*} (entries : List α) (blocks : α → List Instruction) :
    (primitiveTrace (entries.flatMap blocks)).length =
      (entries.map (fun entry => (primitiveTrace (blocks entry)).length)).sum := by
  simp only [primitiveTrace, List.flatMap_assoc, List.length_flatMap]

theorem nodeProgram_trace_length (parent offset degree : Nat) :
    (primitiveTrace (nodeProgram parent offset degree)).length = 80 + 60 * degree := by
  simp only [nodeProgram, primitiveTrace_append, List.length_append, nodeHeader_trace_length,
    nodeTail_trace_length]
  have hchildren :
      (primitiveTrace ((List.range degree).flatMap (childBlock offset))).length = 60 * degree := by
    rw [primitiveTrace_length_flatMap]
    simp only [childBlock_trace_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
    omega
  rw [hchildren]
  omega

theorem copyProgram_length (size : Nat) : (copyProgram size).length = 3 * size := by
  simp only [copyProgram, List.length_flatMap, copyBlock_length, List.map_const',
    List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem copyProgram_trace_length (size : Nat) : (primitiveTrace (copyProgram size)).length = 30 * size := by
  rw [copyProgram, primitiveTrace_length_flatMap]
  simp only [copyBlock_trace_length, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem compileNodes_length {Tool : Type*} (cache : IndexedNodeCache Tool)
    (parents : List cache.NodeId) (offset : Nat) :
    (compileNodes cache parents offset).length = 8 * parents.length +
      6 * (parents.map (fun parent => (cache.children.get parent).size)).sum := by
  induction parents generalizing offset with
  | nil => rfl
  | cons parent later ih =>
    rw [compileNodes, List.length_append, nodeProgram_length, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem compileNodes_trace_length {Tool : Type*} (cache : IndexedNodeCache Tool)
    (parents : List cache.NodeId) (offset : Nat) :
    (primitiveTrace (compileNodes cache parents offset)).length = 80 * parents.length +
      60 * (parents.map (fun parent => (cache.children.get parent).size)).sum := by
  induction parents generalizing offset with
  | nil => rfl
  | cons parent later ih =>
    rw [compileNodes, primitiveTrace_append, List.length_append, nodeProgram_trace_length, ih]
    simp only [List.length_cons, List.map_cons, List.sum_cons]
    omega

theorem childArray_sum_finRange {Tool : Type*} (cache : IndexedNodeCache Tool) :
    ((List.finRange cache.nodes.size).map (fun parent => (cache.children.get parent).size)).sum =
      ∑ parent : cache.NodeId, (cache.children.get parent).size := by
  rw [← List.sum_toFinset _ (List.nodup_finRange _), List.toFinset_finRange]

theorem normalizationProgram_length {Tool : Type*} (cache : IndexedNodeCache Tool) :
    (normalizationProgram cache).length = 11 * cache.nodes.size +
      6 * (∑ parent : cache.NodeId, (cache.children.get parent).size) := by
  rw [normalizationProgram, List.length_append, copyProgram_length, compileNodes_length,
    childArray_sum_finRange]
  simp only [List.length_finRange]
  omega

theorem normalizationProgram_trace_length {Tool : Type*} (cache : IndexedNodeCache Tool) :
    (primitiveTrace (normalizationProgram cache)).length = 110 * cache.nodes.size +
      60 * (∑ parent : cache.NodeId, (cache.children.get parent).size) := by
  rw [normalizationProgram, primitiveTrace_append, List.length_append, copyProgram_trace_length,
    compileNodes_trace_length, childArray_sum_finRange]
  simp only [List.length_finRange]
  omega

theorem prepared_normalizationProgram_trace_le (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (primitiveTrace (normalizationProgram (prepareNormalization q full).indexed)).length ≤
      170 * (prepareNormalization q full).indexed.nodes.size := by
  rw [normalizationProgram_trace_length, prepared_indexed_edge_count q full hq hlaminar]
  omega

theorem execute_copyBlock_heap (rom : ROM) (index : Nat) (state : State) :
    (execute rom (copyBlock index) state).heap = Function.update state.heap index (rom.read .input index) := rfl

theorem execute_childBlock_heap (rom : ROM) (offset position : Nat) (state : State) :
    (execute rom (childBlock offset position) state).heap = state.heap := rfl

theorem execute_childBlock_total (rom : ROM) (offset position : Nat) (state : State) :
    (execute rom (childBlock offset position) state).register .total =
      state.register .total + state.heap (rom.read .children (offset + position)) := rfl

theorem execute_childBlock_flag (rom : ROM) (offset position : Nat) (state : State) :
    (execute rom (childBlock offset position) state).register .flag = state.register .flag := rfl

theorem execute_nodeHeader_heap (rom : ROM) (parent : Nat) (state : State) :
    (execute rom (nodeHeader parent) state).heap = state.heap := rfl

theorem execute_nodeHeader_total (rom : ROM) (parent : Nat) (state : State) :
    (execute rom (nodeHeader parent) state).register .total = 0 := rfl

theorem execute_nodeHeader_flag (rom : ROM) (parent : Nat) (state : State) :
    (execute rom (nodeHeader parent) state).register .flag = rom.read .internal parent := rfl

theorem execute_nodeTail_heap (rom : ROM) (parent : Nat) (state : State) :
    (execute rom (nodeTail parent) state).heap = Function.update state.heap parent
      (if state.register .flag = 0 then state.heap parent else min (state.heap parent) (state.register .total)) := rfl

theorem execute_copyIndices_heap (rom : ROM) (indices : List Nat) (state : State) (index : Nat) :
    (execute rom (indices.flatMap copyBlock) state).heap index =
      if index ∈ indices then rom.read .input index else state.heap index := by
  induction indices generalizing state with
  | nil => simp only [List.flatMap_nil, execute, List.not_mem_nil, ↓reduceIte]
  | cons head later ih =>
    rw [List.flatMap_cons, execute_append, ih, execute_copyBlock_heap]
    by_cases heq : index = head
    · subst index
      simp only [List.mem_cons_self, ↓reduceIte, Function.update_self, ite_self]
    · simp only [List.mem_cons, heq, false_or, Function.update_of_ne heq]

theorem execute_copyProgram_heap (rom : ROM) (size : Nat) (state : State) (index : Nat) :
    (execute rom (copyProgram size) state).heap index =
      if index < size then rom.read .input index else state.heap index := by
  simpa only [copyProgram, List.mem_range] using execute_copyIndices_heap rom (List.range size) state index

def vectorMemory {size : Nat} (values : Vector Nat size) (index : Nat) : Nat :=
  if hindex : index < size then values.get ⟨index, hindex⟩ else 0

theorem vectorMemory_at {size : Nat} (values : Vector Nat size) (index : Fin size) :
    vectorMemory values index.val = values.get index := by
  simp only [vectorMemory, index.isLt, ↓reduceDIte]

def ROM.withInput {size : Nat} (rom : ROM) (values : Vector Nat size) : ROM :=
  { read := fun region index => if region = .input then vectorMemory values index else rom.read region index }

theorem execute_copyProgram_agrees {size : Nat} (rom : ROM) (values : Vector Nat size)
    (state : State) (index : Fin size) :
    (execute (rom.withInput values) (copyProgram size) state).heap index.val = values.get index := by
  rw [execute_copyProgram_heap]
  simp only [index.isLt, ↓reduceIte, ROM.withInput, vectorMemory_at]

theorem execute_childIndices_heap (rom : ROM) (offset : Nat) (positions : List Nat) (state : State) :
    (execute rom (positions.flatMap (childBlock offset)) state).heap = state.heap := by
  induction positions generalizing state with
  | nil => rfl
  | cons position later ih =>
    rw [List.flatMap_cons, execute_append, ih, execute_childBlock_heap]

theorem execute_childIndices_flag (rom : ROM) (offset : Nat) (positions : List Nat) (state : State) :
    (execute rom (positions.flatMap (childBlock offset)) state).register .flag = state.register .flag := by
  induction positions generalizing state with
  | nil => rfl
  | cons position later ih =>
    rw [List.flatMap_cons, execute_append, ih, execute_childBlock_flag]

theorem execute_childIndices_total (rom : ROM) (offset : Nat) (positions : List Nat) (state : State) :
    (execute rom (positions.flatMap (childBlock offset)) state).register .total = state.register .total +
      (positions.map (fun position => state.heap (rom.read .children (offset + position)))).sum := by
  induction positions generalizing state with
  | nil => simp only [List.flatMap_nil, execute, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons position later ih =>
    rw [List.flatMap_cons, execute_append, ih, execute_childBlock_total, execute_childBlock_heap]
    simp only [List.map_cons, List.sum_cons, Nat.add_assoc]

theorem execute_nodeProgram_heap (rom : ROM) (parent offset degree : Nat) (state : State) :
    (execute rom (nodeProgram parent offset degree) state).heap =
      Function.update state.heap parent (if rom.read .internal parent = 0 then state.heap parent else
        min (state.heap parent)
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
    (List.range degree).flatMap (childBlock offset) ++ nodeTail parent) state).heap = _
  rw [execute_append, execute_append]
  change (execute rom (nodeTail parent) childState).heap = _
  rw [execute_nodeTail_heap, hheap, hflag, htotal]

def HeapAgrees {Tool : Type*} {cache : IndexedNodeCache Tool}
    (heap : Nat → Nat) (capacity : IndexedCapacity cache) : Prop :=
  ∀ node : cache.NodeId, heap node.val = capacity.get node

def InternalROMFor {Tool : Type*} (cache : IndexedNodeCache Tool) (rom : ROM) : Prop :=
  ∀ parent : cache.NodeId, rom.read .internal parent.val ≠ 0 ↔ 1 < (cache.decode parent).card

def ChildrenROMFor {Tool : Type*} (cache : IndexedNodeCache Tool) :
    List cache.NodeId → Nat → ROM → Prop
  | [], _, _ => True
  | parent :: later, offset, rom =>
      (∀ position (hposition : position < (cache.children.get parent).size),
        rom.read .children (offset + position) = ((cache.children.get parent)[position]'hposition).val) ∧
      ChildrenROMFor cache later (offset + (cache.children.get parent).size) rom

theorem child_sum_refines {Tool : Type*} (cache : IndexedNodeCache Tool)
    (rom : ROM) (offset : Nat) (parent : cache.NodeId) (heap : Nat → Nat)
    (capacity : IndexedCapacity cache) (hagrees : HeapAgrees heap capacity)
    (hchildren : ∀ position (hposition : position < (cache.children.get parent).size),
      rom.read .children (offset + position) = ((cache.children.get parent)[position]'hposition).val) :
    ((List.range (cache.children.get parent).size).map
      (fun position => heap (rom.read .children (offset + position)))).sum = cache.childSum capacity parent := by
  apply congrArg List.sum
  apply List.ext_getElem
  · simp only [List.length_map, List.length_range, Array.length_toList]
  · intro position hleft _
    have hposition : position < (cache.children.get parent).size := by
      simpa only [List.length_map, List.length_range] using hleft
    simp only [List.getElem_map, List.getElem_range, Array.getElem_toList]
    rw [hchildren position hposition]
    exact hagrees _

theorem execute_nodeProgram_refines {Tool : Type*} (cache : IndexedNodeCache Tool)
    (rom : ROM) (offset : Nat) (parent : cache.NodeId) (state : State)
    (capacity : IndexedCapacity cache) (hagrees : HeapAgrees state.heap capacity)
    (hflags : InternalROMFor cache rom)
    (hchildren : ∀ position (hposition : position < (cache.children.get parent).size),
      rom.read .children (offset + position) = ((cache.children.get parent)[position]'hposition).val) :
    HeapAgrees (execute rom (nodeProgram parent.val offset (cache.children.get parent).size) state).heap
      (cache.normalizeStep capacity parent) := by
  intro target
  rw [execute_nodeProgram_heap, child_sum_refines cache rom offset parent state.heap capacity hagrees hchildren,
    indexed_normalizeStep_get]
  by_cases hinternal : 1 < (cache.decode parent).card
  · have hflag := (hflags parent).mpr hinternal
    by_cases heq : target = parent
    · subst target
      simp only [Function.update_self, hflag, hinternal, and_self, ↓reduceIte, hagrees parent]
    · have hval : target.val ≠ parent.val := fun h => heq (Fin.ext h)
      simp only [Function.update_of_ne hval, heq, and_false, ↓reduceIte, hagrees target]
  · have hflag : rom.read .internal parent.val = 0 := by
      by_contra hne
      exact hinternal ((hflags parent).mp hne)
    by_cases heq : target = parent
    · subst target
      simp only [Function.update_self, hflag, hinternal, false_and, ↓reduceIte, hagrees parent]
    · have hval : target.val ≠ parent.val := fun h => heq (Fin.ext h)
      simp only [Function.update_of_ne hval, hinternal, false_and, ↓reduceIte, hagrees target]

theorem execute_compileNodes_refines {Tool : Type*} (cache : IndexedNodeCache Tool)
    (parents : List cache.NodeId) (offset : Nat) (rom : ROM) (state : State)
    (capacity : IndexedCapacity cache) (hagrees : HeapAgrees state.heap capacity)
    (hflags : InternalROMFor cache rom) (hchildren : ChildrenROMFor cache parents offset rom) :
    HeapAgrees (execute rom (compileNodes cache parents offset) state).heap
      (cache.normalizeAlong parents capacity) := by
  induction parents generalizing offset state capacity with
  | nil => exact hagrees
  | cons parent later ih =>
    rw [compileNodes, execute_append]
    exact ih _ _ _ (execute_nodeProgram_refines cache rom offset parent state capacity hagrees hflags hchildren.1)
      hchildren.2

def childWords {Tool : Type*} (cache : IndexedNodeCache Tool) (parents : List cache.NodeId) : List Nat :=
  parents.flatMap (fun parent => (cache.children.get parent).toList.map Fin.val)

theorem childrenROMFor_of_slice {Tool : Type*} (cache : IndexedNodeCache Tool)
    (parents : List cache.NodeId) (offset : Nat) (rom : ROM)
    (hlookup : ∀ position, position < (childWords cache parents).length →
      rom.read .children (offset + position) = (childWords cache parents).getD position 0) :
    ChildrenROMFor cache parents offset rom := by
  induction parents generalizing offset with
  | nil => trivial
  | cons parent later ih =>
    constructor
    · intro position hposition
      have hleft : position < ((cache.children.get parent).toList.map Fin.val).length := by
        simpa only [List.length_map, Array.length_toList] using hposition
      have hpositionAll : position < (childWords cache (parent :: later)).length := by
        simp only [childWords, List.flatMap_cons, List.length_append, List.length_map, Array.length_toList]
        omega
      have hread := hlookup position hpositionAll
      rw [childWords, List.flatMap_cons, List.getD_append _ _ _ _ hleft, List.getD_eq_getElem _ 0 hleft] at hread
      simpa only [List.getElem_map, Array.getElem_toList] using hread
    · apply ih
      intro position hposition
      have hpositionAll : (cache.children.get parent).size + position <
          (childWords cache (parent :: later)).length := by
        simp only [childWords, List.flatMap_cons, List.length_append, List.length_map, Array.length_toList] at *
        omega
      have hread := hlookup ((cache.children.get parent).size + position) hpositionAll
      rw [childWords, List.flatMap_cons, List.getD_append_right _ _ _ _ (by
        simp only [List.length_map, Array.length_toList]; omega)] at hread
      simpa only [childWords, List.length_map, Array.length_toList, Nat.add_sub_cancel_left, Nat.add_assoc] using hread

def treeROM {Tool : Type*} [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool) : ROM :=
  let metadata := cache.metadata
  let words := childWords cache (List.finRange cache.nodes.size)
  { read := fun region index => match region with
    | .input => 0
    | .internal => if hindex : index < cache.nodes.size then
        if metadata.isInternal.get ⟨index, hindex⟩ then 1 else 0 else 0
    | .children => words.getD index 0 }

theorem treeROM_flags {Tool : Type*} [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool) :
    InternalROMFor cache (treeROM cache) := by
  intro parent
  have hflag := metadata_isInternal cache parent
  simp only [treeROM, parent.isLt, ↓reduceDIte]
  cases hvalue : cache.metadata.isInternal.get parent
  · simpa only [hvalue, Bool.false_eq_true, ↓reduceIte, ne_eq, not_true_eq_false, false_iff] using hflag
  · have hpos := (metadata_isInternal cache parent).mp hvalue
    simp only [↓reduceIte]
    exact ⟨fun _ => hpos, fun _ => Nat.one_ne_zero⟩

theorem treeROM_children {Tool : Type*} [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool) :
    ChildrenROMFor cache (List.finRange cache.nodes.size) 0 (treeROM cache) := by
  apply childrenROMFor_of_slice
  intro position _
  simp only [treeROM, Nat.zero_add]

theorem ROM.withInput_flags {Tool : Type*} {cache : IndexedNodeCache Tool} (rom : ROM)
    (values : IndexedCapacity cache) (hflags : InternalROMFor cache rom) :
    InternalROMFor cache (rom.withInput values) := by
  intro parent
  exact hflags parent

theorem ROM.withInput_children {Tool : Type*} {cache : IndexedNodeCache Tool} (rom : ROM)
    (values : IndexedCapacity cache) (parents : List cache.NodeId) (offset : Nat)
    (hchildren : ChildrenROMFor cache parents offset rom) :
    ChildrenROMFor cache parents offset (rom.withInput values) := by
  induction parents generalizing offset with
  | nil => trivial
  | cons parent later ih => exact ⟨hchildren.1, ih _ hchildren.2⟩

theorem execute_normalizationProgram_refines {Tool : Type*} [DecidableEq Tool] [Fintype Tool]
    (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache) (state : State) :
    HeapAgrees (execute ((treeROM cache).withInput capacity) (normalizationProgram cache) state).heap
      (cache.normalize capacity) := by
  rw [normalizationProgram, execute_append]
  apply execute_compileNodes_refines
  · exact execute_copyProgram_agrees _ capacity state
  · exact ROM.withInput_flags _ capacity (treeROM_flags cache)
  · exact ROM.withInput_children _ capacity _ _ (treeROM_children cache)

/-- Instrumented RAM operational semantics. Each rule performs the stated
register/heap transition and emits that opcode's explicit primitive trace. -/
inductive Runs (rom : ROM) : List Instruction → State → State → List Primitive → Prop where
  | nil (state : State) : Runs rom [] state state []
  | step (instruction : Instruction) (later : List Instruction) (initial final : State)
      (tailTrace : List Primitive)
      (continuation : Runs rom later (instruction.execute rom initial) final tailTrace) :
      Runs rom (instruction :: later) initial final (instruction.trace ++ tailTrace)

theorem runs_execute (rom : ROM) (program : List Instruction) (state : State) :
    Runs rom program state (execute rom program state) (primitiveTrace program) := by
  induction program generalizing state with
  | nil => exact Runs.nil state
  | cons instruction later ih => exact Runs.step instruction later state _ _ (ih _)

theorem Runs.deterministic {rom : ROM} {program : List Instruction} {initial final : State}
    {trace : List Primitive} (run : Runs rom program initial final trace) :
    final = execute rom program initial ∧ trace = primitiveTrace program := by
  induction run with
  | nil => exact ⟨rfl, rfl⟩
  | step instruction later initial final tailTrace continuation ih =>
    exact ⟨ih.1, congrArg (instruction.trace ++ ·) ih.2⟩

theorem prepared_normalization_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) (initial : State) :
    ∃ final trace,
      Runs (((treeROM (prepareNormalization q full).indexed).withInput capacity))
        (normalizationProgram (prepareNormalization q full).indexed) initial final trace ∧
      HeapAgrees final.heap ((prepareNormalization q full).indexed.normalize capacity) ∧
      trace.length ≤ 170 * (prepareNormalization q full).indexed.nodes.size := by
  exact ⟨_, _, runs_execute _ _ initial, execute_normalizationProgram_refines _ capacity initial,
    prepared_normalizationProgram_trace_le q full hq hlaminar⟩

theorem sum_take_map_le {α : Type*} (entries : List α) (f : α → Nat) (count : Nat) :
    ((entries.take count).map f).sum ≤ (entries.map f).sum := by
  rw [List.map_take]
  have hsum := List.sum_take_add_sum_drop (entries.map f) count
  omega

theorem prepared_indexed_child_card_sum (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (parent : (prepareNormalization q full).indexed.NodeId)
    (hinternal : 1 < ((prepareNormalization q full).indexed.decode parent).card) :
    (∑ child ∈ (prepareNormalization q full).indexed.childIds parent,
      ((prepareNormalization q full).indexed.decode child).card) =
        ((prepareNormalization q full).indexed.decode parent).card := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  have hcount := layout_used_count_eq_sum_children full hlaminar
    (prepared_indexed_node_mem q full parent) hinternal Finset.univ
  change (Finset.univ ∩ (prepareNormalization q full).indexed.decode parent).card =
    ∑ child ∈ children (nodeFamily full) ((prepareNormalization q full).indexed.decode parent),
      (Finset.univ ∩ child).card at hcount
  simp only [Finset.univ_inter] at hcount
  rw [← prepared_indexed_children_decode q full hq hlaminar parent,
    Finset.sum_image (fun left _ right _ heq => prepared_indexed_decode_injective q full heq)] at hcount
  exact hcount.symm

theorem prepared_indexed_childSum_le_card (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hbounded : ∀ node, capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (parent : (prepareNormalization q full).indexed.NodeId) :
    (prepareNormalization q full).indexed.childSum capacity parent ≤
      ((prepareNormalization q full).indexed.decode parent).card := by
  let : Nonempty (Fin q) := ⟨⟨0, hq⟩⟩
  by_cases hinternal : 1 < ((prepareNormalization q full).indexed.decode parent).card
  · rw [childSum_eq_finset _ capacity parent (indexNodes_children_nodup _ _ parent)]
    exact (Finset.sum_le_sum (fun child _ => hbounded child)).trans
      (Nat.le_of_eq (prepared_indexed_child_card_sum q full hq hlaminar parent hinternal))
  · have hempty : ((prepareNormalization q full).indexed.children.get parent).toList = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro child hmem
      have hlt := prepared_indexed_child_card_lt q full hq hlaminar parent child hmem
      have hpositive := Finset.card_pos.mpr
        (nodeFamily_nonempty_nodes full _ (prepared_indexed_node_mem q full child))
      omega
    simp only [IndexedNodeCache.childSum, hempty, List.map_nil, List.sum_nil, Nat.zero_le]

/-- The manuscript's stronger initial coordinate bounds control every
intermediate vector, not only the final normalized output. -/
theorem prepared_intermediate_capacity_le_card (q : Nat) (full : List (Finset (Fin q)))
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hbounded : ∀ node, capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (priorNodes : List (prepareNormalization q full).indexed.NodeId)
    (node : (prepareNormalization q full).indexed.NodeId) :
    ((prepareNormalization q full).indexed.normalizeAlong priorNodes capacity).get node ≤
      ((prepareNormalization q full).indexed.decode node).card :=
  (indexed_normalizeAlong_le _ priorNodes capacity node).trans (hbounded node)

theorem prepared_child_prefix_accumulator_le_q (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hbounded : ∀ node, capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (priorNodes : List (prepareNormalization q full).indexed.NodeId)
    (parent : (prepareNormalization q full).indexed.NodeId) (offset count : Nat) (rom : ROM) (state : State)
    (hagrees : HeapAgrees state.heap ((prepareNormalization q full).indexed.normalizeAlong priorNodes capacity))
    (hzero : state.register .total = 0)
    (hchildren : ∀ position (hposition : position < ((prepareNormalization q full).indexed.children.get parent).size),
      rom.read .children (offset + position) =
        (((prepareNormalization q full).indexed.children.get parent)[position]'hposition).val) :
    (execute rom (((List.range ((prepareNormalization q full).indexed.children.get parent).size).take count).flatMap
      (childBlock offset)) state).register .total ≤ q := by
  rw [execute_childIndices_total, hzero, Nat.zero_add]
  calc
    _ ≤ ((List.range ((prepareNormalization q full).indexed.children.get parent).size).map
        (fun position => state.heap (rom.read .children (offset + position)))).sum := sum_take_map_le _ _ count
    _ = (prepareNormalization q full).indexed.childSum
        ((prepareNormalization q full).indexed.normalizeAlong priorNodes capacity) parent :=
      child_sum_refines _ rom offset parent state.heap _ hagrees hchildren
    _ ≤ ((prepareNormalization q full).indexed.decode parent).card :=
      prepared_indexed_childSum_le_card q full hq hlaminar _
        (prepared_intermediate_capacity_le_card q full capacity hbounded priorNodes) parent
    _ ≤ q := by
      simpa only [Fintype.card_fin] using
        Finset.card_le_univ ((prepareNormalization q full).indexed.decode parent)

def Instruction.addressesBounded (size edges : Nat) (instruction : Instruction) (state : State) : Prop :=
  match instruction with
  | .loadROM .input _ pointer => state.register pointer < size
  | .loadROM .internal _ pointer => state.register pointer < size
  | .loadROM .children _ pointer => state.register pointer < edges
  | .loadHeap _ pointer => state.register pointer < size
  | .storeHeap pointer _ => state.register pointer < size
  | _ => True

/-- All addresses are checked in the actual pre-state of each instruction. -/
def AddressSafe (size edges : Nat) (rom : ROM) : List Instruction → State → Prop
  | [], _ => True
  | instruction :: later, state => instruction.addressesBounded size edges state ∧
      AddressSafe size edges rom later (instruction.execute rom state)

theorem addressSafe_append (size edges : Nat) (rom : ROM) (left right : List Instruction) (state : State) :
    AddressSafe size edges rom (left ++ right) state ↔
      AddressSafe size edges rom left state ∧ AddressSafe size edges rom right (execute rom left state) := by
  induction left generalizing state with
  | nil => simp only [List.nil_append, AddressSafe, execute, true_and]
  | cons instruction later ih => simp only [List.cons_append, AddressSafe, execute, ih, and_assoc]

theorem copyBlock_addressSafe (size edges : Nat) (rom : ROM) (state : State)
    (index : Nat) (hindex : index < size) : AddressSafe size edges rom (copyBlock index) state := by
  simp [copyBlock, AddressSafe, Instruction.addressesBounded, Instruction.execute, hindex]

theorem nodeHeader_addressSafe (size edges : Nat) (rom : ROM) (state : State)
    (parent : Nat) (hparent : parent < size) : AddressSafe size edges rom (nodeHeader parent) state := by
  simp [nodeHeader, AddressSafe, Instruction.addressesBounded, Instruction.execute, hparent]

theorem nodeTail_addressSafe (size edges : Nat) (rom : ROM) (state : State)
    (parent : Nat) (hparent : parent < size) : AddressSafe size edges rom (nodeTail parent) state := by
  simp [nodeTail, AddressSafe, Instruction.addressesBounded, Instruction.execute, hparent]

theorem childBlock_addressSafe (size edges : Nat) (rom : ROM) (state : State)
    (offset position : Nat) (hposition : offset + position < edges)
    (hchild : rom.read .children (offset + position) < size) :
    AddressSafe size edges rom (childBlock offset position) state := by
  simp [childBlock, AddressSafe, Instruction.addressesBounded, Instruction.execute, hposition, hchild]

theorem copyIndices_addressSafe (size edges : Nat) (rom : ROM) (indices : List Nat) (state : State)
    (hindices : ∀ index ∈ indices, index < size) :
    AddressSafe size edges rom (indices.flatMap copyBlock) state := by
  induction indices generalizing state with
  | nil => trivial
  | cons index later ih =>
    rw [List.flatMap_cons, addressSafe_append]
    exact ⟨copyBlock_addressSafe size edges rom state index (hindices index List.mem_cons_self),
      ih _ (fun next hnext => hindices next (List.mem_cons_of_mem _ hnext))⟩

theorem childIndices_addressSafe (size edges : Nat) (rom : ROM) (offset : Nat)
    (positions : List Nat) (state : State)
    (hpositions : ∀ position ∈ positions,
      offset + position < edges ∧ rom.read .children (offset + position) < size) :
    AddressSafe size edges rom (positions.flatMap (childBlock offset)) state := by
  induction positions generalizing state with
  | nil => trivial
  | cons position later ih =>
    rw [List.flatMap_cons, addressSafe_append]
    have hhead := hpositions position List.mem_cons_self
    exact ⟨childBlock_addressSafe size edges rom state offset position hhead.1 hhead.2,
      ih _ (fun next hnext => hpositions next (List.mem_cons_of_mem _ hnext))⟩

theorem nodeProgram_addressSafe (size edges : Nat) (rom : ROM) (parent offset degree : Nat)
    (state : State) (hparent : parent < size) (hspan : offset + degree ≤ edges)
    (hchildren : ∀ position < degree, rom.read .children (offset + position) < size) :
    AddressSafe size edges rom (nodeProgram parent offset degree) state := by
  rw [nodeProgram, addressSafe_append, addressSafe_append]
  refine ⟨⟨nodeHeader_addressSafe size edges rom state parent hparent, ?_⟩,
    nodeTail_addressSafe size edges rom _ parent hparent⟩
  apply childIndices_addressSafe
  intro position hposition
  have hdegree := List.mem_range.mp hposition
  exact ⟨by omega, hchildren position hdegree⟩

theorem compileNodes_addressSafe {Tool : Type*} (cache : IndexedNodeCache Tool)
    (parents : List cache.NodeId) (offset edges : Nat) (rom : ROM) (state : State)
    (hchildren : ChildrenROMFor cache parents offset rom)
    (hspan : offset + (parents.map (fun parent => (cache.children.get parent).size)).sum ≤ edges) :
    AddressSafe cache.nodes.size edges rom (compileNodes cache parents offset) state := by
  induction parents generalizing offset state with
  | nil => trivial
  | cons parent later ih =>
    have hspanHead : offset + (cache.children.get parent).size ≤ edges := by
      simp only [List.map_cons, List.sum_cons] at hspan
      omega
    have hspanTail : offset + (cache.children.get parent).size +
        (later.map (fun next => (cache.children.get next).size)).sum ≤ edges := by
      simpa only [List.map_cons, List.sum_cons, Nat.add_assoc] using hspan
    rw [compileNodes, addressSafe_append]
    refine ⟨nodeProgram_addressSafe _ edges rom parent.val offset _ state parent.isLt hspanHead ?_,
      ih _ _ hchildren.2 hspanTail⟩
    intro position hposition
    rw [hchildren.1 position hposition]
    exact ((cache.children.get parent)[position]'hposition).isLt

theorem normalizationProgram_addressSafe {Tool : Type*} [DecidableEq Tool] [Fintype Tool]
    (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache) (state : State) :
    AddressSafe cache.nodes.size (∑ parent : cache.NodeId, (cache.children.get parent).size)
      ((treeROM cache).withInput capacity) (normalizationProgram cache) state := by
  rw [normalizationProgram, addressSafe_append]
  refine ⟨copyIndices_addressSafe _ _ _ _ state (fun index hindex => List.mem_range.mp hindex), ?_⟩
  apply compileNodes_addressSafe
  · exact ROM.withInput_children _ capacity _ _ (treeROM_children cache)
  · rw [childArray_sum_finRange, Nat.zero_add]

theorem instruction_fetch_bound (rom : ROM) (program : List Instruction) (state : State)
    (beforeCount wordIndex : Nat) (hbefore : beforeCount < program.length) (hword : wordIndex < 5) :
    (execute rom (program.take beforeCount) state).pc + wordIndex < state.pc + 5 * program.length := by
  rw [execute_pc, List.length_take, Nat.min_eq_left (Nat.le_of_lt hbefore)]
  omega

/-- Finite data layout: input, internal flags, serialized children, working
capacity. Region-address additions are the addressAdd operations in the trace. -/
def regionBase (size : Nat) : Region → Nat
  | .input => 0
  | .internal => size
  | .children => 2 * size

def workingBase (size edges : Nat) : Nat := 2 * size + edges
def dataWords (size edges : Nat) : Nat := 3 * size + edges
def physicalWords {Tool : Type*} (cache : IndexedNodeCache Tool) : Nat :=
  dataWords cache.nodes.size (∑ parent : cache.NodeId, (cache.children.get parent).size) +
    5 * (normalizationProgram cache).length

theorem region_address_bound (size edges : Nat) (region : Region) (index : Nat)
    (hindex : index < match region with | .children => edges | _ => size) :
    regionBase size region + index < dataWords size edges := by
  cases region <;> dsimp only at hindex <;> simp only [regionBase, dataWords] <;> omega

theorem working_address_bound (size edges index : Nat) (hindex : index < size) :
    workingBase size edges + index < dataWords size edges := by
  simp only [workingBase, dataWords]
  omega

theorem physicalWords_eq {Tool : Type*} (cache : IndexedNodeCache Tool) :
    physicalWords cache = 58 * cache.nodes.size +
      31 * (∑ parent : cache.NodeId, (cache.children.get parent).size) := by
  rw [physicalWords, dataWords, normalizationProgram_length]
  omega

theorem prepared_physicalWords_le (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    physicalWords (prepareNormalization q full).indexed ≤ 89 * (full.length + q + 1) := by
  rw [physicalWords_eq, prepared_indexed_edge_count q full hq hlaminar]
  have hsize := prepared_indexed_size_le q full
  omega

theorem physical_instruction_fetch_bound {Tool : Type*} (cache : IndexedNodeCache Tool)
    (rom : ROM) (state : State) (hpc : state.pc = 0) (beforeCount wordIndex : Nat)
    (hbefore : beforeCount < (normalizationProgram cache).length) (hword : wordIndex < 5) :
    dataWords cache.nodes.size (∑ parent : cache.NodeId, (cache.children.get parent).size) +
      (execute rom ((normalizationProgram cache).take beforeCount) state).pc + wordIndex <
        physicalWords cache := by
  have hfetch := instruction_fetch_bound rom (normalizationProgram cache) state beforeCount wordIndex hbefore hword
  rw [hpc, Nat.zero_add] at hfetch
  unfold physicalWords
  omega

/-- Stored tree-specific ROM and code, compiled once. No correctness or
performance proposition is a data field. A pass only supplies input cells and
executes these existing fields; primitive traces are ghost cost certificates. -/
structure CompiledNormalizer {Tool : Type*} (cache : IndexedNodeCache Tool) where
  rom : ROM
  program : List Instruction

def compileNormalizer {Tool : Type*} [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool) :
    CompiledNormalizer cache := { rom := treeROM cache, program := normalizationProgram cache }

def CompiledNormalizer.run {Tool : Type*} {cache : IndexedNodeCache Tool}
    (compiled : CompiledNormalizer cache) (capacity : IndexedCapacity cache) (state : State) : State :=
  execute (compiled.rom.withInput capacity) compiled.program state

theorem compiledNormalizer_run_refines {Tool : Type*} [DecidableEq Tool] [Fintype Tool]
    (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache) (state : State) :
    HeapAgrees ((compileNormalizer cache).run capacity state).heap (cache.normalize capacity) :=
  execute_normalizationProgram_refines cache capacity state

theorem prepared_compiledNormalizer_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) (state : State) :
    let compiled := compileNormalizer (prepareNormalization q full).indexed
    HeapAgrees (compiled.run capacity state).heap ((prepareNormalization q full).indexed.normalize capacity) ∧
      AddressSafe (prepareNormalization q full).indexed.nodes.size
        (∑ parent : (prepareNormalization q full).indexed.NodeId,
          ((prepareNormalization q full).indexed.children.get parent).size)
        (compiled.rom.withInput capacity) compiled.program state ∧
      (primitiveTrace compiled.program).length ≤ 170 * (prepareNormalization q full).indexed.nodes.size :=
  ⟨compiledNormalizer_run_refines _ capacity state, normalizationProgram_addressSafe _ capacity state,
    prepared_normalizationProgram_trace_le q full hq hlaminar⟩

def Register.word : Register → Nat
  | .address => 0 | .index => 1 | .value => 2 | .total => 3 | .old => 4 | .fresh => 5 | .flag => 6

def Register.fromWord : Nat → Option Register
  | 0 => some .address | 1 => some .index | 2 => some .value | 3 => some .total
  | 4 => some .old | 5 => some .fresh | 6 => some .flag | _ => none

theorem Register.fromWord_word (reg : Register) : Register.fromWord reg.word = some reg := by
  cases reg <;> rfl

def Region.word : Region → Nat
  | .input => 0 | .internal => 1 | .children => 2

def Region.fromWord : Nat → Option Region
  | 0 => some .input | 1 => some .internal | 2 => some .children | _ => none

theorem Region.fromWord_word (region : Region) : Region.fromWord region.word = some region := by
  cases region <;> rfl

/-- Actual padded five-word instruction encoding used by the fetch count. -/
def Instruction.encodeWords : Instruction → Vector Nat 5
  | .constant target number => ⟨#[0, target.word, number, 0, 0], rfl⟩
  | .add target left right => ⟨#[1, target.word, left.word, right.word, 0], rfl⟩
  | .minimum target left right => ⟨#[2, target.word, left.word, right.word, 0], rfl⟩
  | .select target condition whenTrue whenFalse =>
      ⟨#[3, target.word, condition.word, whenTrue.word, whenFalse.word], rfl⟩
  | .loadROM region target pointer => ⟨#[4, region.word, target.word, pointer.word, 0], rfl⟩
  | .loadHeap target pointer => ⟨#[5, target.word, pointer.word, 0, 0], rfl⟩
  | .storeHeap pointer source => ⟨#[6, pointer.word, source.word, 0, 0], rfl⟩

def Instruction.decodeWords (words : Vector Nat 5) : Option Instruction :=
  match words[0] with
  | 0 => do
      let target ← Register.fromWord words[1]
      return .constant target words[2]
  | 1 => do
      let target ← Register.fromWord words[1]
      let left ← Register.fromWord words[2]
      let right ← Register.fromWord words[3]
      return .add target left right
  | 2 => do
      let target ← Register.fromWord words[1]
      let left ← Register.fromWord words[2]
      let right ← Register.fromWord words[3]
      return .minimum target left right
  | 3 => do
      let target ← Register.fromWord words[1]
      let condition ← Register.fromWord words[2]
      let whenTrue ← Register.fromWord words[3]
      let whenFalse ← Register.fromWord words[4]
      return .select target condition whenTrue whenFalse
  | 4 => do
      let region ← Region.fromWord words[1]
      let target ← Register.fromWord words[2]
      let pointer ← Register.fromWord words[3]
      return .loadROM region target pointer
  | 5 => do
      let target ← Register.fromWord words[1]
      let pointer ← Register.fromWord words[2]
      return .loadHeap target pointer
  | 6 => do
      let pointer ← Register.fromWord words[1]
      let source ← Register.fromWord words[2]
      return .storeHeap pointer source
  | _ => none

theorem Instruction.decodeWords_encodeWords (instruction : Instruction) :
    Instruction.decodeWords instruction.encodeWords = some instruction := by
  cases instruction <;> simp [encodeWords, decodeWords, Register.fromWord_word, Region.fromWord_word]

def programWords (program : List Instruction) : List Nat :=
  program.flatMap (fun instruction => instruction.encodeWords.toArray.toList)

theorem programWords_length (program : List Instruction) :
    (programWords program).length = 5 * program.length := by
  simp only [programWords, List.length_flatMap, Array.length_toList, Vector.size_toArray,
    List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
  omega

theorem physicalWords_eq_serialized {Tool : Type*} (cache : IndexedNodeCache Tool) :
    physicalWords cache = dataWords cache.nodes.size
      (∑ parent : cache.NodeId, (cache.children.get parent).size) +
        (programWords (normalizationProgram cache)).length := by
  rw [programWords_length]
  rfl

theorem programWords_fetch (program : List Instruction) (index position : Nat)
    (hindex : index < program.length) (hposition : position < 5) :
    (programWords program).getD (5 * index + position) 0 =
      ((program[index]'hindex).encodeWords.toArray.toList).getD position 0 := by
  induction program generalizing index with
  | nil => simp only [List.length_nil] at hindex; omega
  | cons instruction later ih =>
    have hhead : instruction.encodeWords.toArray.toList.length = 5 := by
      simp only [Array.length_toList, Vector.size_toArray]
    cases index with
    | zero =>
      simp only [programWords, List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      exact List.getD_append _ _ _ _ (hhead.symm ▸ hposition)
    | succ index =>
      have htail : index < later.length := Nat.lt_of_succ_lt_succ hindex
      have hlarge : instruction.encodeWords.toArray.toList.length ≤ 5 * (index + 1) + position := by omega
      simp only [programWords, List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getD_append_right _ _ _ _ hlarge, hhead]
      have hsub : 5 * (index + 1) + position - 5 = 5 * index + position := by omega
      rw [hsub]
      exact ih index htail

def fetchWords (words : List Nat) (pc : Nat) : Vector Nat 5 :=
  Vector.ofFn (fun position => words.getD (pc + position.val) 0)

theorem fetchWords_programWords (program : List Instruction) (index : Nat) (hindex : index < program.length) :
    fetchWords (programWords program) (5 * index) = (program[index]'hindex).encodeWords := by
  apply Vector.ext
  intro position hposition
  change (Vector.ofFn (fun word : Fin 5 => (programWords program).getD (5 * index + word.val) 0)).get
      ⟨position, hposition⟩ = ((program[index]'hindex).encodeWords).get ⟨position, hposition⟩
  rw [cache_get_ofFn, programWords_fetch program index position hindex hposition,
    List.getD_eq_getElem _ 0 (by simpa only [Array.length_toList, Vector.size_toArray] using hposition)]
  rfl

def haltWords : Vector Nat 5 := ⟨#[7, 0, 0, 0, 0], rfl⟩

def haltingProgramWords (program : List Instruction) : List Nat :=
  programWords program ++ haltWords.toArray.toList

def terminalTrace : List Primitive := List.replicate 5 .instructionWordRead ++ [.decode]

theorem terminalTrace_length : terminalTrace.length = 6 := rfl

theorem decode_haltWords : Instruction.decodeWords haltWords = none := rfl

theorem fetchWords_halting_body (program : List Instruction) (index : Nat) (hindex : index < program.length) :
    fetchWords (haltingProgramWords program) (5 * index) = (program[index]'hindex).encodeWords := by
  have hbody : fetchWords (haltingProgramWords program) (5 * index) =
      fetchWords (programWords program) (5 * index) := by
    apply Vector.ext
    intro position hposition
    change (Vector.ofFn _).get ⟨position, hposition⟩ = (Vector.ofFn _).get ⟨position, hposition⟩
    rw [cache_get_ofFn, cache_get_ofFn]
    exact List.getD_append _ _ _ _ (by rw [programWords_length]; omega)
  exact hbody.trans (fetchWords_programWords program index hindex)

theorem fetchWords_halting_terminal (program : List Instruction) :
    fetchWords (haltingProgramWords program) (5 * program.length) = haltWords := by
  apply Vector.ext
  intro position hposition
  change (Vector.ofFn _).get ⟨position, hposition⟩ = haltWords.get ⟨position, hposition⟩
  rw [cache_get_ofFn]
  change (programWords program ++ haltWords.toArray.toList).getD (5 * program.length + position) 0 = _
  rw [List.getD_append_right _ _ _ _ (by rw [programWords_length]; omega), programWords_length]
  rw [Nat.add_sub_cancel_left, List.getD_eq_getElem _ 0 (by simpa only [Array.length_toList, Vector.size_toArray] using hposition)]
  rfl

theorem haltingProgramWords_length (program : List Instruction) :
    (haltingProgramWords program).length = 5 * program.length + 5 := by
  simp only [haltingProgramWords, List.length_append, programWords_length, Array.length_toList,
    Vector.size_toArray]

/-- Full termination includes fetching and decoding the encoded HALT word.
The earlier Runs relation is the body prefix up to that final halt fetch. -/
inductive HaltingRuns (rom : ROM) (program : List Instruction) (initial final : State) : List Primitive → Prop where
  | halt (bodyTrace : List Primitive) (body : Runs rom program initial final bodyTrace)
      (haltDecoded : Instruction.decodeWords (fetchWords (haltingProgramWords program) final.pc) = none) :
      HaltingRuns rom program initial final (bodyTrace ++ terminalTrace)

theorem execute_halts (rom : ROM) (program : List Instruction) (initial : State) (hpc : initial.pc = 0) :
    HaltingRuns rom program initial (execute rom program initial) (primitiveTrace program ++ terminalTrace) := by
  apply HaltingRuns.halt _ (runs_execute rom program initial)
  rw [execute_pc, hpc, Nat.zero_add, fetchWords_halting_terminal, decode_haltWords]

theorem prepared_haltingNormalization_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed) (initial : State) (hpc : initial.pc = 0) :
    ∃ final trace,
      HaltingRuns (((treeROM (prepareNormalization q full).indexed).withInput capacity))
        (normalizationProgram (prepareNormalization q full).indexed) initial final trace ∧
      HeapAgrees final.heap ((prepareNormalization q full).indexed.normalize capacity) ∧
      trace.length ≤ 176 * (prepareNormalization q full).indexed.nodes.size := by
  refine ⟨_, _, execute_halts _ _ initial hpc, execute_normalizationProgram_refines _ capacity initial, ?_⟩
  rw [List.length_append, terminalTrace_length]
  have hbody := prepared_normalizationProgram_trace_le q full hq hlaminar
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hpositive : 0 < (prepareNormalization q full).indexed.nodes.size :=
    Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  omega

def haltingPhysicalWords {Tool : Type*} (cache : IndexedNodeCache Tool) : Nat := physicalWords cache + 5

theorem haltingPhysicalWords_eq_serialized {Tool : Type*} (cache : IndexedNodeCache Tool) :
    haltingPhysicalWords cache = dataWords cache.nodes.size
      (∑ parent : cache.NodeId, (cache.children.get parent).size) +
        (haltingProgramWords (normalizationProgram cache)).length := by
  rw [haltingPhysicalWords, physicalWords_eq_serialized, haltingProgramWords_length, programWords_length]
  omega

theorem prepared_haltingPhysicalWords_le (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    haltingPhysicalWords (prepareNormalization q full).indexed ≤ 94 * (full.length + q + 1) := by
  have hbody := prepared_physicalWords_le q full hq hlaminar
  unfold haltingPhysicalWords
  omega

theorem halting_body_fetch_bound {Tool : Type*} (cache : IndexedNodeCache Tool)
    (rom : ROM) (state : State) (hpc : state.pc = 0) (beforeCount wordIndex : Nat)
    (hbefore : beforeCount < (normalizationProgram cache).length) (hword : wordIndex < 5) :
    dataWords cache.nodes.size (∑ parent : cache.NodeId, (cache.children.get parent).size) +
      (execute rom ((normalizationProgram cache).take beforeCount) state).pc + wordIndex <
        haltingPhysicalWords cache := by
  have hbody := physical_instruction_fetch_bound cache rom state hpc beforeCount wordIndex hbefore hword
  unfold haltingPhysicalWords
  omega

theorem halting_terminal_fetch_bound {Tool : Type*} (cache : IndexedNodeCache Tool)
    (rom : ROM) (state : State) (hpc : state.pc = 0) (wordIndex : Nat) (hword : wordIndex < 5) :
    dataWords cache.nodes.size (∑ parent : cache.NodeId, (cache.children.get parent).size) +
      (execute rom (normalizationProgram cache) state).pc + wordIndex < haltingPhysicalWords cache := by
  rw [execute_pc, hpc, Nat.zero_add]
  unfold haltingPhysicalWords physicalWords
  omega

theorem childrenROMFor_append {Tool : Type*} (cache : IndexedNodeCache Tool)
    (left right : List cache.NodeId) (offset : Nat) (rom : ROM) :
    ChildrenROMFor cache (left ++ right) offset rom ↔
      ChildrenROMFor cache left offset rom ∧ ChildrenROMFor cache right
        (offset + (left.map (fun parent => (cache.children.get parent).size)).sum) rom := by
  induction left generalizing offset with
  | nil => simp only [List.nil_append, ChildrenROMFor, List.map_nil, List.sum_nil, Nat.add_zero, true_and]
  | cons parent later ih =>
    simp only [List.cons_append, ChildrenROMFor, ih, List.map_cons, List.sum_cons, Nat.add_assoc, and_assoc]

theorem childrenROMFor_take {Tool : Type*} (cache : IndexedNodeCache Tool)
    (parents : List cache.NodeId) (offset : Nat) (rom : ROM)
    (hchildren : ChildrenROMFor cache parents offset rom) (count : Nat) :
    ChildrenROMFor cache (parents.take count) offset rom := by
  have hsplit : ChildrenROMFor cache (parents.take count ++ parents.drop count) offset rom := by
    rw [List.take_append_drop]
    exact hchildren
  exact ((childrenROMFor_append cache _ _ offset rom).mp hsplit).1

theorem childrenROMFor_drop {Tool : Type*} (cache : IndexedNodeCache Tool)
    (parents : List cache.NodeId) (offset : Nat) (rom : ROM)
    (hchildren : ChildrenROMFor cache parents offset rom) (count : Nat) :
    ChildrenROMFor cache (parents.drop count)
      (offset + ((parents.take count).map (fun parent => (cache.children.get parent).size)).sum) rom := by
  have hsplit : ChildrenROMFor cache (parents.take count ++ parents.drop count) offset rom := by
    rw [List.take_append_drop]
    exact hchildren
  exact ((childrenROMFor_append cache _ _ offset rom).mp hsplit).2

theorem compileNodes_append {Tool : Type*} (cache : IndexedNodeCache Tool)
    (left right : List cache.NodeId) (offset : Nat) :
    compileNodes cache (left ++ right) offset = compileNodes cache left offset ++
      compileNodes cache right (offset + (left.map (fun parent => (cache.children.get parent).size)).sum) := by
  induction left generalizing offset with
  | nil => simp only [List.nil_append, compileNodes, List.map_nil, List.sum_nil, Nat.add_zero]
  | cons parent later ih =>
    simp only [List.cons_append, compileNodes, ih, List.map_cons, List.sum_cons, Nat.add_assoc, List.append_assoc]

theorem normalizationProgram_split {Tool : Type*} (cache : IndexedNodeCache Tool) (count : Nat) :
    normalizationProgram cache =
      (copyProgram cache.nodes.size ++ compileNodes cache ((List.finRange cache.nodes.size).take count) 0) ++
        compileNodes cache ((List.finRange cache.nodes.size).drop count)
          (((List.finRange cache.nodes.size).take count).map (fun parent => (cache.children.get parent).size)).sum := by
  have hsplit := compileNodes_append cache ((List.finRange cache.nodes.size).take count)
    ((List.finRange cache.nodes.size).drop count) 0
  rw [List.take_append_drop, Nat.zero_add] at hsplit
  rw [normalizationProgram, hsplit, List.append_assoc]

/-- An observer of a genuine code prefix, not another run implementation. -/
def nodePrefixState {Tool : Type*} [DecidableEq Tool] [Fintype Tool]
    (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache) (initial : State) (count : Nat) : State :=
  execute ((treeROM cache).withInput capacity)
    (copyProgram cache.nodes.size ++ compileNodes cache ((List.finRange cache.nodes.size).take count) 0) initial

theorem nodePrefixState_refines {Tool : Type*} [DecidableEq Tool] [Fintype Tool]
    (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache) (initial : State) (count : Nat) :
    HeapAgrees (nodePrefixState cache capacity initial count).heap
      (cache.normalizeAlong ((List.finRange cache.nodes.size).take count) capacity) := by
  rw [nodePrefixState, execute_append]
  apply execute_compileNodes_refines
  · exact execute_copyProgram_agrees _ capacity initial
  · exact ROM.withInput_flags _ capacity (treeROM_flags cache)
  · exact childrenROMFor_take cache _ 0 _
      (ROM.withInput_children _ capacity _ _ (treeROM_children cache)) count

theorem treeROM_children_at {Tool : Type*} [DecidableEq Tool] [Fintype Tool]
    (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache) (parent : cache.NodeId) :
    ∀ position (hposition : position < (cache.children.get parent).size),
      ((treeROM cache).withInput capacity).read .children
        ((((List.finRange cache.nodes.size).take parent.val).map (fun node => (cache.children.get node).size)).sum +
          position) = ((cache.children.get parent)[position]'hposition).val := by
  have hindex : parent.val < (List.finRange cache.nodes.size).length := by
    simpa only [List.length_finRange] using parent.isLt
  have hget : (List.finRange cache.nodes.size)[parent.val]'hindex = parent := by
    rw [List.getElem_finRange]
    apply Fin.ext
    rfl
  have hdrop := List.drop_eq_getElem_cons hindex
  rw [hget] at hdrop
  have htail := childrenROMFor_drop cache _ 0 _
    (ROM.withInput_children _ capacity _ _ (treeROM_children cache)) parent.val
  rw [hdrop, Nat.zero_add] at htail
  exact htail.1

def nodeChildPrefixState {Tool : Type*} [DecidableEq Tool] [Fintype Tool]
    (cache : IndexedNodeCache Tool) (capacity : IndexedCapacity cache) (initial : State)
    (parent : cache.NodeId) (count : Nat) : State :=
  let rom := (treeROM cache).withInput capacity
  let offset := (((List.finRange cache.nodes.size).take parent.val).map (fun node => (cache.children.get node).size)).sum
  let headerState := execute rom (nodeHeader parent.val) (nodePrefixState cache capacity initial parent.val)
  execute rom (((List.range (cache.children.get parent).size).take count).flatMap (childBlock offset)) headerState

theorem prepared_actual_child_accumulator_le_q (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (hbounded : ∀ node, capacity.get node ≤ ((prepareNormalization q full).indexed.decode node).card)
    (initial : State) (parent : (prepareNormalization q full).indexed.NodeId) (count : Nat) :
    (nodeChildPrefixState (prepareNormalization q full).indexed capacity initial parent count).register .total ≤ q := by
  unfold nodeChildPrefixState
  apply prepared_child_prefix_accumulator_le_q q full hq hlaminar capacity hbounded
  · rw [execute_nodeHeader_heap]
    exact nodePrefixState_refines _ capacity initial parent.val
  · exact execute_nodeHeader_total _ _ _
  · exact treeROM_children_at _ capacity parent

end PaperProofs.Structure.LaminarTree.IndexedRAM
