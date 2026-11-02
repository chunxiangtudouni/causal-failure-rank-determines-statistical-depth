module

public import PaperProofs.Structure.UniformFreeTableSafety

/-! A17 batch 001: the ancestor pass reads parents from the persistent
runtime metadata heap and writes an arbitrary disjoint capacity workspace.
No tree data or stage-node answer occurs in the generated instructions. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17HeapAncestors001

open IndexedRAM IndexedClosureRAM AlgorithmClaims

variable {Tool : Type*}

def heapView (base : Nat) (heap : Nat → Nat) : Nat → Nat := fun index => heap (base + index)

theorem heapView_update (base index value : Nat) (heap : Nat → Nat) :
    heapView base (Function.update heap (base + index) value) =
      Function.update (heapView base heap) index value := by
  funext address
  by_cases heq : address = index
  · subst address
    simp only [heapView, Function.update_self]
  · have hne : base + address ≠ base + index := by omega
    simp only [heapView, Function.update_of_ne heq, Function.update_of_ne hne]

def ParentHeapFor (cache : IndexedNodeCache Tool) (parentBase : Nat) (heap : Nat → Nat) : Prop :=
  heap parentBase = 0 ∧ ∀ node : cache.NodeId,
    heap (parentBase + (node.val + 1)) = encodedNode cache (cache.parents.get node)

def RepresentsAt (cache : IndexedNodeCache Tool) (capacityBase : Nat)
    (machine : State) (value : WalkState cache) : Prop :=
  heapView capacityBase machine.heap = value.heap ∧
    machine.register .flag = value.flag ∧
    machine.register .address = encodedNode cache value.current ∧ machine.register .total = 1

def ancestorBlock (capacityBase parentBase : Nat) : List Op :=
  [.subtract .index .address .total,
   .base (.constant .old capacityBase), .base (.add .index .old .index),
   .base (.loadHeap .value .index), .base (.constant .old 0),
   .base (.select .fresh .value .flag .old),
   .base (.select .flag .address .fresh .flag),
   .subtract .fresh .value .total,
   .base (.select .fresh .address .fresh .value), .base (.storeHeap .index .fresh),
   .base (.constant .index parentBase), .base (.add .index .index .address),
   .base (.loadHeap .address .index)]

theorem ancestorBlock_heap (rom : ROM) (capacityBase parentBase : Nat) (state : State) :
    (execute rom (ancestorBlock capacityBase parentBase) state).heap =
      Function.update state.heap (capacityBase + (state.register .address - state.register .total))
        (if state.register .address = 0 then
          state.heap (capacityBase + (state.register .address - state.register .total))
         else state.heap (capacityBase + (state.register .address - state.register .total)) - state.register .total) := rfl

theorem ancestorBlock_flag (rom : ROM) (capacityBase parentBase : Nat) (state : State) :
    (execute rom (ancestorBlock capacityBase parentBase) state).register .flag =
      if state.register .address = 0 then state.register .flag else
        if state.heap (capacityBase + (state.register .address - state.register .total)) = 0 then 0
        else state.register .flag := rfl

theorem ancestorBlock_parent (rom : ROM) (capacityBase parentBase : Nat) (state : State) :
    (execute rom (ancestorBlock capacityBase parentBase) state).register .address =
      (execute rom (ancestorBlock capacityBase parentBase) state).heap
        (parentBase + state.register .address) := rfl

theorem ancestorBlock_one (rom : ROM) (capacityBase parentBase : Nat) (state : State) :
    (execute rom (ancestorBlock capacityBase parentBase) state).register .total = state.register .total := rfl

theorem ancestorBlock_length (capacityBase parentBase : Nat) :
    (ancestorBlock capacityBase parentBase).length = 13 := rfl

set_option maxRecDepth 4096 in
theorem ancestorBlock_trace_length (capacityBase parentBase : Nat) :
    (trace (ancestorBlock capacityBase parentBase)).length = 137 := rfl

theorem current_index_lt (cache : IndexedNodeCache Tool) (capacityBase : Nat)
    (hsize : 0 < cache.nodes.size) (machine : State) (value : WalkState cache)
    (hvalue : RepresentsAt cache capacityBase machine value) :
    machine.register .address - machine.register .total < cache.nodes.size := by
  rw [hvalue.2.2.1, hvalue.2.2.2]
  cases value.current with
  | none => simpa only [encodedNode, Nat.zero_sub] using hsize
  | some node => simpa only [encodedNode, Nat.add_sub_cancel] using node.isLt

theorem ancestorBlock_frame (rom : ROM) (capacityBase parentBase : Nat) (state : State)
    (address : Nat) (hne : address ≠ capacityBase + (state.register .address - state.register .total)) :
    (execute rom (ancestorBlock capacityBase parentBase) state).heap address = state.heap address := by
  rw [ancestorBlock_heap, Function.update_of_ne hne]

theorem ancestorBlock_parents (cache : IndexedNodeCache Tool) (rom : ROM)
    (capacityBase parentBase : Nat) (hsize : 0 < cache.nodes.size)
    (hdisjoint : ∀ index < cache.nodes.size, ∀ encoded ≤ cache.nodes.size,
      capacityBase + index ≠ parentBase + encoded)
    (machine : State) (value : WalkState cache) (hvalue : RepresentsAt cache capacityBase machine value)
    (hparents : ParentHeapFor cache parentBase machine.heap) :
    ParentHeapFor cache parentBase (execute rom (ancestorBlock capacityBase parentBase) machine).heap := by
  have hi := current_index_lt cache capacityBase hsize machine value hvalue
  constructor
  · rw [ancestorBlock_frame rom capacityBase parentBase machine parentBase (by
      simpa only [Nat.add_zero] using (hdisjoint _ hi 0 (Nat.zero_le _)).symm)]
    exact hparents.1
  · intro node
    rw [ancestorBlock_frame rom capacityBase parentBase machine _
      (hdisjoint _ hi (node.val + 1) node.isLt).symm]
    exact hparents.2 node

theorem ancestorBlock_represents (cache : IndexedNodeCache Tool) (rom : ROM)
    (capacityBase parentBase : Nat) (hsize : 0 < cache.nodes.size)
    (hdisjoint : ∀ index < cache.nodes.size, ∀ encoded ≤ cache.nodes.size,
      capacityBase + index ≠ parentBase + encoded)
    (machine : State) (value : WalkState cache) (hvalue : RepresentsAt cache capacityBase machine value)
    (hparents : ParentHeapFor cache parentBase machine.heap) :
    RepresentsAt cache capacityBase (execute rom (ancestorBlock capacityBase parentBase) machine) (walkStep value) := by
  have hp := ancestorBlock_parents cache rom capacityBase parentBase hsize hdisjoint machine value hvalue hparents
  obtain ⟨hh, hf, ha, hone⟩ := hvalue
  cases hc : value.current with
  | none =>
    have haddr : machine.register .address = 0 := ha.trans (by rw [hc]; rfl)
    have hheap : (execute rom (ancestorBlock capacityBase parentBase) machine).heap = machine.heap := by
      rw [ancestorBlock_heap, haddr]
      simp only [Nat.zero_sub, ite_true]
      exact Function.update_eq_self _ _
    refine ⟨?_, ?_, ?_, ?_⟩
    · simpa only [walkStep, hc, hheap] using hh
    · simpa only [walkStep, hc, ancestorBlock_flag, haddr, ite_true] using hf
    · simpa only [walkStep, hc, ancestorBlock_parent, haddr, Nat.add_zero, encodedNode] using hp.1
    · exact (ancestorBlock_one rom capacityBase parentBase machine).trans hone
  | some node =>
    have haddr : machine.register .address = node.val + 1 := ha.trans (by rw [hc]; rfl)
    have hhnode : machine.heap (capacityBase + node.val) = value.heap node.val := congrFun hh node.val
    refine ⟨?_, ?_, ?_, ?_⟩
    · simp only [walkStep, hc, ancestorBlock_heap, haddr, hone, Nat.add_sub_cancel,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, heapView_update, hhnode, hh]
    · simp only [walkStep, hc, ancestorBlock_flag, haddr, hone, hf, Nat.add_sub_cancel,
        Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false, hhnode]
    · simpa only [walkStep, hc, ancestorBlock_parent, haddr] using hp.2 node
    · exact (ancestorBlock_one rom capacityBase parentBase machine).trans hone

def ancestorLoop (capacityBase parentBase fuel : Nat) : List Op :=
  (List.replicate fuel (ancestorBlock capacityBase parentBase)).flatten

theorem ancestorLoop_correct (cache : IndexedNodeCache Tool) (rom : ROM)
    (capacityBase parentBase fuel : Nat) (hsize : 0 < cache.nodes.size)
    (hdisjoint : ∀ index < cache.nodes.size, ∀ encoded ≤ cache.nodes.size,
      capacityBase + index ≠ parentBase + encoded)
    (machine : State) (value : WalkState cache) (hvalue : RepresentsAt cache capacityBase machine value)
    (hparents : ParentHeapFor cache parentBase machine.heap) :
    RepresentsAt cache capacityBase (execute rom (ancestorLoop capacityBase parentBase fuel) machine) (walk fuel value) ∧
      ParentHeapFor cache parentBase (execute rom (ancestorLoop capacityBase parentBase fuel) machine).heap := by
  induction fuel generalizing machine value with
  | zero => exact ⟨hvalue, hparents⟩
  | succ fuel ih =>
    rw [ancestorLoop, List.replicate_succ, List.flatten_cons, IndexedClosureRAM.execute_append]
    exact ih _ _
      (ancestorBlock_represents cache rom capacityBase parentBase hsize hdisjoint machine value hvalue hparents)
      (ancestorBlock_parents cache rom capacityBase parentBase hsize hdisjoint machine value hvalue hparents)

theorem ancestorLoop_length (capacityBase parentBase fuel : Nat) :
    (ancestorLoop capacityBase parentBase fuel).length = 13 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [ancestorLoop, List.replicate_succ, List.flatten_cons, List.length_append, ancestorBlock_length]
    change 13 + (ancestorLoop capacityBase parentBase fuel).length = _
    rw [ih]
    omega

theorem ancestorLoop_trace_length (capacityBase parentBase fuel : Nat) :
    (trace (ancestorLoop capacityBase parentBase fuel)).length = 137 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [ancestorLoop, List.replicate_succ, List.flatten_cons, IndexedClosureRAM.trace_append,
      List.length_append, ancestorBlock_trace_length]
    change 137 + (trace (ancestorLoop capacityBase parentBase fuel)).length = _
    rw [ih]
    omega

theorem ancestorLoop_frame (cache : IndexedNodeCache Tool) (rom : ROM)
    (capacityBase parentBase fuel : Nat) (hsize : 0 < cache.nodes.size)
    (hdisjoint : ∀ index < cache.nodes.size, ∀ encoded ≤ cache.nodes.size,
      capacityBase + index ≠ parentBase + encoded)
    (machine : State) (value : WalkState cache) (hvalue : RepresentsAt cache capacityBase machine value)
    (hparents : ParentHeapFor cache parentBase machine.heap) (address : Nat)
    (hframe : ∀ index < cache.nodes.size, address ≠ capacityBase + index) :
    (execute rom (ancestorLoop capacityBase parentBase fuel) machine).heap address = machine.heap address := by
  induction fuel generalizing machine value with
  | zero => rfl
  | succ fuel ih =>
    rw [ancestorLoop, List.replicate_succ, List.flatten_cons, IndexedClosureRAM.execute_append]
    change (execute rom (ancestorLoop capacityBase parentBase fuel)
      (execute rom (ancestorBlock capacityBase parentBase) machine)).heap address = _
    rw [ih _ _
      (ancestorBlock_represents cache rom capacityBase parentBase hsize hdisjoint machine value hvalue hparents)
      (ancestorBlock_parents cache rom capacityBase parentBase hsize hdisjoint machine value hvalue hparents)]
    exact ancestorBlock_frame rom capacityBase parentBase machine address
      (hframe _ (current_index_lt cache capacityBase hsize machine value hvalue))

def extensionInit (size capacityBase stageAddress : Nat) : List Op :=
  [.base (.constant .index (capacityBase + size)), .base (.loadHeap .flag .index),
   .base (.constant .index stageAddress), .base (.loadHeap .address .index),
   .base (.constant .old 0), .base (.select .flag .address .flag .old),
   .base (.constant .total 1)]

def extensionTail (size capacityBase : Nat) : List Op :=
  [.base (.constant .index (capacityBase + size)), .base (.storeHeap .index .flag)]

def extensionProgram (size capacityBase parentBase stageAddress : Nat) : List Op :=
  extensionInit size capacityBase stageAddress ++ ancestorLoop capacityBase parentBase size ++
    extensionTail size capacityBase

theorem extensionInit_heap (rom : ROM) (size capacityBase stageAddress : Nat) (state : State) :
    (execute rom (extensionInit size capacityBase stageAddress) state).heap = state.heap := rfl

theorem extensionInit_registers (rom : ROM) (size capacityBase stageAddress : Nat) (state : State) :
    let result := execute rom (extensionInit size capacityBase stageAddress) state
    result.register .address = state.heap stageAddress ∧ result.register .total = 1 ∧
      result.register .flag = if state.heap stageAddress = 0 then 0 else state.heap (capacityBase + size) := by
  exact ⟨rfl, rfl, rfl⟩

theorem extensionTail_heap (rom : ROM) (size capacityBase : Nat) (state : State) :
    (execute rom (extensionTail size capacityBase) state).heap =
      Function.update state.heap (capacityBase + size) (state.register .flag) := rfl

theorem extensionProgram_result (cache : IndexedNodeCache Tool) (rom : ROM)
    (capacityBase parentBase stageAddress : Nat) (hsize : 0 < cache.nodes.size)
    (hdisjoint : ∀ index < cache.nodes.size, ∀ encoded ≤ cache.nodes.size,
      capacityBase + index ≠ parentBase + encoded)
    (node : Option cache.NodeId) (entry : IndexedEntry.FixedEntry cache)
    (machine : State) (hparents : ParentHeapFor cache parentBase machine.heap)
    (hstage : machine.heap stageAddress = encodedNode cache node)
    (hrep : IndexedCellRAM.SlotRep cache machine.heap capacityBase entry)
    (hnodup : ∀ target : cache.NodeId, (IndexedAncestors.ancestorChain cache target).Nodup) :
    IndexedCellRAM.slot cache
      (execute rom (extensionProgram cache.nodes.size capacityBase parentBase stageAddress) machine).heap capacityBase =
      IndexedStaticMetadata.extendAt cache node entry := by
  let start := execute rom (extensionInit cache.nodes.size capacityBase stageAddress) machine
  let value : WalkState cache :=
    ⟨heapView capacityBase machine.heap, start.register .flag, node⟩
  have hs := extensionInit_registers rom cache.nodes.size capacityBase stageAddress machine
  have hv : RepresentsAt cache capacityBase start value :=
    ⟨rfl, rfl, hs.1.trans hstage, hs.2.1⟩
  have hp : ParentHeapFor cache parentBase start.heap := hparents
  have hc := (ancestorLoop_correct cache rom capacityBase parentBase cache.nodes.size hsize hdisjoint
    start value hv hp).1
  let result := execute rom (ancestorLoop capacityBase parentBase cache.nodes.size) start
  have hresult : execute rom (extensionProgram cache.nodes.size capacityBase parentBase stageAddress) machine =
      execute rom (extensionTail cache.nodes.size capacityBase) result := by
    simp only [extensionProgram, IndexedClosureRAM.execute_append]
    rfl
  rw [hresult]
  cases entry with
  | void =>
    have hflag : start.register .flag = 0 := by rw [hs.2.2, hrep]; split_ifs <;> rfl
    have hz : result.register .flag = 0 := hc.2.1.trans (walk_zero_flag _ value hflag)
    apply IndexedCellRAM.slot_eq_of_rep
    change (execute rom (extensionTail cache.nodes.size capacityBase) result).heap
      (capacityBase + cache.nodes.size) = 0
    rw [extensionTail_heap, Function.update_self, hz]
  | vector capacity =>
    cases node with
    | none =>
      have hflag : start.register .flag = 0 := by rw [hs.2.2, hstage]; rfl
      have hz : result.register .flag = 0 := hc.2.1.trans (walk_zero_flag _ value hflag)
      apply IndexedCellRAM.slot_eq_of_rep
      change (execute rom (extensionTail cache.nodes.size capacityBase) result).heap
        (capacityBase + cache.nodes.size) = 0
      rw [extensionTail_heap, Function.update_self, hz]
    | some node =>
      have hheap : HeapAgrees value.heap capacity := by intro target; exact hrep.2 target
      have hflag : value.flag = 1 := by
        change start.register .flag = 1
        rw [hs.2.2, hstage, hrep.1]
        simp only [encodedNode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
      have hout : HeapAgrees (heapView capacityBase result.heap) (IndexedAncestors.chainDecrement cache capacity node) := by
        rw [hc.1]
        exact walk_heap_decrementNodes cache cache.nodes.size node value.heap capacity value.flag hheap
      have hf : result.register .flag = if IndexedAncestors.chainZero cache capacity node then 0 else 1 := by
        rw [hc.2.1, walk_flag_decrementFlag cache cache.nodes.size node value.heap capacity value.flag hheap]
        change decrementFlag cache (IndexedAncestors.ancestorChain cache node) capacity value.flag = _
        rw [decrementFlag_nodup cache _ (hnodup node), hflag]
        simp only [IndexedAncestors.chainZero, List.any_eq_true, decide_eq_true_eq]
      change IndexedCellRAM.slot cache _ capacityBase =
        if IndexedAncestors.chainZero cache capacity node then .void else
          .vector (IndexedAncestors.chainDecrement cache capacity node)
      by_cases hz : IndexedAncestors.chainZero cache capacity node = true
      · rw [ite_eq_left hz]
        apply IndexedCellRAM.slot_eq_of_rep
        change (execute rom (extensionTail cache.nodes.size capacityBase) result).heap
          (capacityBase + cache.nodes.size) = 0
        rw [extensionTail_heap, Function.update_self, hf, ite_eq_left hz]
      · rw [ite_eq_right hz]
        apply IndexedCellRAM.slot_eq_of_rep
        constructor
        · rw [extensionTail_heap, Function.update_self, hf, ite_eq_right hz]
        · intro target
          rw [extensionTail_heap, Function.update_of_ne (by have := target.isLt; omega)]
          exact hout target

theorem extensionProgram_frame (cache : IndexedNodeCache Tool) (rom : ROM)
    (capacityBase parentBase stageAddress : Nat) (hsize : 0 < cache.nodes.size)
    (hdisjoint : ∀ index < cache.nodes.size, ∀ encoded ≤ cache.nodes.size,
      capacityBase + index ≠ parentBase + encoded)
    (node : Option cache.NodeId) (machine : State)
    (hparents : ParentHeapFor cache parentBase machine.heap)
    (hstage : machine.heap stageAddress = encodedNode cache node)
    (address : Nat) (hframe : ∀ index ≤ cache.nodes.size, address ≠ capacityBase + index) :
    (execute rom (extensionProgram cache.nodes.size capacityBase parentBase stageAddress) machine).heap address = machine.heap address := by
  let start := execute rom (extensionInit cache.nodes.size capacityBase stageAddress) machine
  let value : WalkState cache := ⟨heapView capacityBase machine.heap, start.register .flag, node⟩
  have hs := extensionInit_registers rom cache.nodes.size capacityBase stageAddress machine
  rw [extensionProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    extensionTail_heap, Function.update_of_ne (hframe _ le_rfl)]
  exact ancestorLoop_frame cache rom capacityBase parentBase cache.nodes.size hsize hdisjoint start value
    ⟨rfl, rfl, hs.1.trans hstage, hs.2.1⟩ hparents address (fun index hi => hframe index (by omega))

theorem extensionProgram_length (size capacityBase parentBase stageAddress : Nat) :
    (extensionProgram size capacityBase parentBase stageAddress).length = 13 * size + 9 := by
  rw [extensionProgram, List.length_append, List.length_append, ancestorLoop_length]
  have hi : (extensionInit size capacityBase stageAddress).length = 7 := rfl
  have ht : (extensionTail size capacityBase).length = 2 := rfl
  rw [hi, ht]
  omega

set_option maxRecDepth 4096 in
theorem extensionProgram_trace_length (size capacityBase parentBase stageAddress : Nat) :
    (trace (extensionProgram size capacityBase parentBase stageAddress)).length = 137 * size + 85 := by
  have hi : (trace (extensionInit size capacityBase stageAddress)).length = 66 := rfl
  have ht : (trace (extensionTail size capacityBase)).length = 19 := rfl
  rw [extensionProgram, IndexedClosureRAM.trace_append, IndexedClosureRAM.trace_append,
    List.length_append, List.length_append, ancestorLoop_trace_length, hi, ht]
  omega

theorem metadata_parentHeapFor (q : Nat) (full : List (Finset (Fin q))) (base : Nat) (heap : Nat → Nat)
    (hmetadata : UniformTreeMetadataRAM.MetadataCorrect q full base heap) :
    ParentHeapFor (prepareNormalization q full).indexed
      (UniformTreeMetadataRAM.parentAddress (prepareNormalization q full).indexed.nodes.size base 0) heap := by
  constructor
  · exact hmetadata.1
  · intro node
    simpa only [UniformTreeMetadataRAM.parentAddress, Nat.add_zero, Nat.add_assoc]
      using (hmetadata.2 node).2.1

set_option maxRecDepth 10000 in
theorem ancestorBlock_prefix_heap (rom : ROM) (capacityBase parentBase : Nat) (state : State)
    (count : Nat) (hc : count ≤ (ancestorBlock capacityBase parentBase).length) :
    (execute rom ((ancestorBlock capacityBase parentBase).take count) state).heap =
      if count ≤ 9 then state.heap else (execute rom (ancestorBlock capacityBase parentBase) state).heap := by
  change count ≤ 13 at hc
  interval_cases count <;> rfl

theorem ancestorBlock_heap_le (rom : ROM) (capacityBase parentBase : Nat) (state : State) (address : Nat) :
    (execute rom (ancestorBlock capacityBase parentBase) state).heap address ≤ state.heap address := by
  rw [ancestorBlock_heap]
  by_cases heq : address = capacityBase + (state.register .address - state.register .total)
  · rw [heq, Function.update_self]
    split_ifs
    · exact le_rfl
    · exact Nat.sub_le _ _
  · rw [Function.update_of_ne heq]

theorem ancestorBlock_capacityThroughout (q words capacityBase parentBase : Nat) (rom : PhysicalROM)
    (state : State) (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (ancestorBlock capacityBase parentBase) state := by
  intro count hc address ha
  rw [ancestorBlock_prefix_heap rom.semantic capacityBase parentBase state count hc]
  split_ifs
  · exact hcapacity address ha
  · exact (ancestorBlock_heap_le rom.semantic capacityBase parentBase state address).trans (hcapacity address ha)

theorem ancestorLoop_capacityThroughout (q words capacityBase parentBase fuel : Nat) (rom : PhysicalROM)
    (state : State) (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (ancestorLoop capacityBase parentBase fuel) state := by
  induction fuel generalizing state with
  | zero => intro count _; simpa only [ancestorLoop, List.replicate_zero, List.flatten_nil,
      List.take_nil, IndexedClosureRAM.execute] using hcapacity
  | succ fuel ih =>
    rw [ancestorLoop, List.replicate_succ, List.flatten_cons]
    apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state
      (ancestorBlock_capacityThroughout q words capacityBase parentBase rom state hcapacity)
    apply ih
    intro address ha
    exact (ancestorBlock_heap_le rom.semantic capacityBase parentBase state address).trans (hcapacity address ha)

theorem extensionProgram_outputTag_le_one (cache : IndexedNodeCache Tool) (rom : ROM)
    (capacityBase parentBase stageAddress : Nat) (hsize : 0 < cache.nodes.size)
    (hdisjoint : ∀ index < cache.nodes.size, ∀ encoded ≤ cache.nodes.size,
      capacityBase + index ≠ parentBase + encoded)
    (node : Option cache.NodeId) (machine : State)
    (hparents : ParentHeapFor cache parentBase machine.heap)
    (hstage : machine.heap stageAddress = encodedNode cache node)
    (htag : machine.heap (capacityBase + cache.nodes.size) ≤ 1) :
    (execute rom (extensionProgram cache.nodes.size capacityBase parentBase stageAddress) machine).heap
      (capacityBase + cache.nodes.size) ≤ 1 := by
  let start := execute rom (extensionInit cache.nodes.size capacityBase stageAddress) machine
  let value : WalkState cache := ⟨heapView capacityBase machine.heap, start.register .flag, node⟩
  have hs := extensionInit_registers rom cache.nodes.size capacityBase stageAddress machine
  have hc := (ancestorLoop_correct cache rom capacityBase parentBase cache.nodes.size hsize hdisjoint
    start value ⟨rfl, rfl, hs.1.trans hstage, hs.2.1⟩ hparents).1
  rw [extensionProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    extensionTail_heap, Function.update_self, hc.2.1]
  apply (IndexedCellRAM.walk_flag_le _ _ value).trans
  change start.register .flag ≤ 1
  rw [hs.2.2]
  split_ifs
  · exact Nat.zero_le _
  · exact htag

theorem extensionProgram_capacityThroughout (q words : Nat) (rom : PhysicalROM)
    (cache : IndexedNodeCache Tool) (capacityBase parentBase stageAddress : Nat)
    (hsize : 0 < cache.nodes.size) (hq : 0 < q)
    (hdisjoint : ∀ index < cache.nodes.size, ∀ encoded ≤ cache.nodes.size,
      capacityBase + index ≠ parentBase + encoded)
    (node : Option cache.NodeId) (machine : State)
    (hparents : ParentHeapFor cache parentBase machine.heap)
    (hstage : machine.heap stageAddress = encodedNode cache node)
    (htag : machine.heap (capacityBase + cache.nodes.size) ≤ 1)
    (hcapacity : CapacityPrefixBounded q words machine.heap) :
    CapacityThroughout q words rom
      (extensionProgram cache.nodes.size capacityBase parentBase stageAddress) machine := by
  let init := extensionInit cache.nodes.size capacityBase stageAddress
  let loop := ancestorLoop capacityBase parentBase cache.nodes.size
  let start := execute rom.semantic init machine
  let after := execute rom.semantic loop start
  have hi : CapacityThroughout q words rom init machine := by
    intro count hc
    change count ≤ 7 at hc
    interval_cases count <;> exact hcapacity
  have hl := ancestorLoop_capacityThroughout q words capacityBase parentBase cache.nodes.size rom start hcapacity
  have ha : CapacityPrefixBounded q words after.heap := by
    have hh := hl (ancestorLoop capacityBase parentBase cache.nodes.size).length le_rfl
    rw [List.take_length] at hh
    exact hh
  have hf : after.register .flag ≤ 1 := by
    have ht := extensionProgram_outputTag_le_one cache rom.semantic capacityBase parentBase stageAddress
      hsize hdisjoint node machine hparents hstage htag
    simpa only [extensionProgram, IndexedClosureRAM.execute_append, extensionTail_heap,
      Function.update_self] using ht
  rw [extensionProgram]
  apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ machine
    (UniformFreeTableSafety.capacityThroughout_append q words rom _ _ machine hi hl)
  intro count hc address haddress
  change count ≤ 2 at hc
  have ht : Function.update after.heap (capacityBase + cache.nodes.size) (after.register .flag) address ≤ q := by
    by_cases heq : address = capacityBase + cache.nodes.size
    · rw [heq, Function.update_self]; exact hf.trans hq
    · rw [Function.update_of_ne heq]; exact ha address haddress
  interval_cases count <;> first | exact ha address haddress | exact ht

theorem extensionProgram_halting (rom : ROM) (size capacityBase parentBase stageAddress : Nat)
    (hsize : 0 < size) (machine : State) (hpc : machine.pc = 0) :
    HaltingRuns rom (extensionProgram size capacityBase parentBase stageAddress) machine
      (execute rom (extensionProgram size capacityBase parentBase stageAddress) machine)
      (trace (extensionProgram size capacityBase parentBase stageAddress) ++ haltTrace) ∧
      (trace (extensionProgram size capacityBase parentBase stageAddress) ++ haltTrace).length ≤ 228 * size := by
  refine ⟨IndexedClosureRAM.execute_halts _ _ _ hpc, ?_⟩
  rw [List.length_append, extensionProgram_trace_length, haltTrace_length]
  omega

theorem extensionProgram_codeWords_length (size capacityBase parentBase stageAddress : Nat) :
    (haltingWords (extensionProgram size capacityBase parentBase stageAddress)).length = 65 * size + 50 := by
  rw [haltingWords_length, extensionProgram_length]
  omega

theorem prepared_extensionProgram_result (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (capacityBase metadataBase stageAddress : Nat)
    (hdisjoint : ∀ index < (prepareNormalization q full).indexed.nodes.size,
      ∀ encoded ≤ (prepareNormalization q full).indexed.nodes.size,
      capacityBase + index ≠ metadataBase + (prepareNormalization q full).indexed.nodes.size + encoded)
    (stage : Fin full.length) (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (machine : State) (hmetadata : UniformTreeMetadataRAM.MetadataCorrect q full metadataBase machine.heap)
    (hstage : machine.heap stageAddress = encodedNode (prepareNormalization q full).indexed
      (IndexedQuery.storedStageNode q full hq stage))
    (hrep : IndexedCellRAM.SlotRep (prepareNormalization q full).indexed machine.heap capacityBase entry) :
    let cache := (prepareNormalization q full).indexed
    IndexedCellRAM.slot cache (execute (givenTreeROM q full).semantic
      (extensionProgram cache.nodes.size capacityBase (metadataBase + cache.nodes.size) stageAddress) machine).heap capacityBase =
      IndexedEntry.extend cache full[stage.val] entry := by
  intro cache
  have hsize : 0 < cache.nodes.size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  rw [extensionProgram_result cache (givenTreeROM q full).semantic capacityBase _ stageAddress hsize
    hdisjoint _ entry machine (metadata_parentHeapFor q full metadataBase machine.heap hmetadata) hstage hrep
    (fun node => IndexedAncestors.prepared_ancestorChain_nodup q full hq hlaminar node)]
  exact IndexedStaticMetadata.buildPositive_extendAt_eq_indexed q full hq hlaminar stage entry

end PaperProofs.Structure.LaminarTree.PA17HeapAncestors001
