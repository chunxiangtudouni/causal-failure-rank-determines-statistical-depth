module

public import PaperProofs.Structure.RawClosureRAM
public import PaperProofs.Structure.IndexedTable

/-!
An actual fixed-slot heap cell. Input good/bad slots stay in heap; the ROM
contains only the prepared tree and a cached optional NodeId. The computed
extension is consumed from writable memory, never converted into an input
ROM or supplied as an oracle. The work prefix and output copy are explicit
word instructions. Full table scheduling and finite-word packing remain
separate obligations.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedCellRAM

open IndexedRAM IndexedClosureRAM

variable {Tool : Type*}

def copyBlock (source target index : Nat) : List Instruction :=
  [.constant .address (source + index), .loadHeap .value .address,
   .constant .index (target + index), .storeHeap .index .value]

def copyIndices (source target : Nat) (indices : List Nat) : List Instruction :=
  indices.flatMap (copyBlock source target)

def copyWords (source target count : Nat) : List Instruction :=
  copyIndices source target (List.range count)

theorem execute_copyBlock_heap (rom : ROM) (source target index : Nat) (state : State) :
    (IndexedRAM.execute rom (copyBlock source target index) state).heap =
      Function.update state.heap (target + index) (state.heap (source + index)) := rfl

theorem copyIndices_frame (rom : ROM) (source target : Nat) (indices : List Nat)
    (state : State) (address : Nat) (hframe : ∀ index ∈ indices, address ≠ target + index) :
    (IndexedRAM.execute rom (copyIndices source target indices) state).heap address = state.heap address := by
  induction indices generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [copyIndices, List.flatMap_cons, IndexedRAM.execute_append]
    change (IndexedRAM.execute rom (copyIndices source target later)
      (IndexedRAM.execute rom (copyBlock source target head) state)).heap address = _
    rw [ih _ (fun index hi => hframe index (List.mem_cons_of_mem _ hi)), execute_copyBlock_heap,
      Function.update_of_ne (hframe head List.mem_cons_self)]

theorem copyIndices_value (rom : ROM) (source target count : Nat) (indices : List Nat)
    (hindices : ∀ index ∈ indices, index < count)
    (hdisjoint : ∀ left < count, ∀ right < count, source + left ≠ target + right)
    (state : State) (index : Nat) (hindex : index ∈ indices) :
    (IndexedRAM.execute rom (copyIndices source target indices) state).heap (target + index) =
      state.heap (source + index) := by
  induction indices generalizing state with
  | nil => cases hindex
  | cons head later ih =>
    rw [copyIndices, List.flatMap_cons, IndexedRAM.execute_append]
    change (IndexedRAM.execute rom (copyIndices source target later)
      (IndexedRAM.execute rom (copyBlock source target head) state)).heap (target + index) = _
    by_cases hi : index ∈ later
    · rw [ih (fun j hj => hindices j (List.mem_cons_of_mem _ hj)) _ hi, execute_copyBlock_heap]
      exact Function.update_of_ne (hdisjoint index (hindices index hindex) head (hindices head List.mem_cons_self)) _ _
    · have heq : index = head := (List.mem_cons.mp hindex).resolve_right hi
      subst index
      rw [copyIndices_frame rom source target later _ _ (by
        intro j hj heq
        have hh : head = j := Nat.add_left_cancel heq
        exact hi (hh ▸ hj)), execute_copyBlock_heap, Function.update_self]

theorem copyWords_value (rom : ROM) (source target count : Nat)
    (hdisjoint : ∀ left < count, ∀ right < count, source + left ≠ target + right)
    (state : State) (index : Nat) (hi : index < count) :
    (IndexedRAM.execute rom (copyWords source target count) state).heap (target + index) =
      state.heap (source + index) :=
  copyIndices_value rom source target count (List.range count)
    (fun _ h => List.mem_range.mp h) hdisjoint state index (List.mem_range.mpr hi)

theorem copyWords_frame (rom : ROM) (source target count : Nat) (state : State)
    (address : Nat) (hframe : ∀ index < count, address ≠ target + index) :
    (IndexedRAM.execute rom (copyWords source target count) state).heap address = state.heap address :=
  copyIndices_frame rom source target (List.range count) state address (fun i hi => hframe i (List.mem_range.mp hi))

theorem copyWords_length (source target count : Nat) : (copyWords source target count).length = 4 * count := by
  simp only [copyWords, copyIndices, List.length_flatMap, copyBlock, List.length_cons, List.length_nil,
    List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem copyWords_trace_length (source target count : Nat) :
    (primitiveTrace (copyWords source target count)).length = 38 * count := by
  rw [copyWords, copyIndices, primitiveTrace_length_flatMap]
  have hblock : ∀ index, (primitiveTrace (copyBlock source target index)).length = 38 := fun _ => rfl
  simp only [hblock, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

def slot (cache : IndexedNodeCache Tool) (heap : Nat → Nat) (base : Nat) : IndexedEntry.FixedEntry cache :=
  decodeResult cache (fun index => heap (base + index))

def SlotRep (cache : IndexedNodeCache Tool) (heap : Nat → Nat) (base : Nat) : IndexedEntry.FixedEntry cache → Prop
  | .void => heap (base + cache.nodes.size) = 0
  | .vector capacity => heap (base + cache.nodes.size) = 1 ∧
      ∀ node : cache.NodeId, heap (base + node.val) = capacity.get node

theorem slot_eq_of_rep (cache : IndexedNodeCache Tool) (heap : Nat → Nat) (base : Nat)
    (entry : IndexedEntry.FixedEntry cache) (hrep : SlotRep cache heap base entry) : slot cache heap base = entry := by
  cases entry with
  | void =>
    unfold slot decodeResult
    dsimp only
    have hz : heap (base + cache.nodes.size) = 0 := hrep
    rw [ite_eq_left hz]
  | vector capacity =>
    unfold slot decodeResult
    dsimp only
    have hne : heap (base + cache.nodes.size) ≠ 0 := by rw [hrep.1]; exact Nat.one_ne_zero
    rw [ite_eq_right hne]
    exact congrArg _ (readCapacity_eq cache _ capacity hrep.2)

theorem slotRep_of_decode (cache : IndexedNodeCache Tool) (heap : Nat → Nat) (base : Nat)
    (entry : IndexedEntry.FixedEntry cache) (htag : heap (base + cache.nodes.size) ≤ 1)
    (heq : slot cache heap base = entry) : SlotRep cache heap base entry := by
  cases entry with
  | void =>
    by_cases hz : heap (base + cache.nodes.size) = 0
    · exact hz
    · simp only [slot, decodeResult, hz, ↓reduceIte] at heq
      cases heq
  | vector capacity =>
    have hz : heap (base + cache.nodes.size) ≠ 0 := by
      intro hzero
      simp only [slot, decodeResult, hzero, ↓reduceIte] at heq
      cases heq
    refine ⟨by omega, ?_⟩
    have hc : readCapacity cache (fun i => heap (base + i)) = capacity := by
      have hh : CapacityBits.Entry.vector (readCapacity cache (fun i => heap (base + i))) = .vector capacity := by
        simpa only [slot, decodeResult, hz, ↓reduceIte] using heq
      exact CapacityBits.Entry.vector.inj hh
    intro node
    have hh := congrArg (fun value : IndexedCapacity cache => value.get node) hc
    simpa only [readCapacity, cache_get_ofFn] using hh

def cellROM [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) : ROM :=
  { read := fun region index => match region with
    | .input => if index = 0 then encodedNode cache node else 0
    | .internal => (treeROM cache).read .internal index
    | .children => if index < cache.nodes.size + 1 then (parentWords cache).getD index 0
        else (childWords cache (List.finRange cache.nodes.size)).getD (index - (cache.nodes.size + 1)) 0 }

theorem cellROM_parent [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) : ParentROMFor cache 0 (cellROM cache node) := by
  constructor
  · simp only [cellROM, Nat.zero_lt_succ, ↓reduceIte]
    rw [parentWords_get cache 0 (by omega), parentWord_zero]
  · intro target
    have hi : target.val + 1 < cache.nodes.size + 1 := by omega
    simp only [cellROM, Nat.zero_add, hi, ↓reduceIte]
    rw [parentWords_get cache _ hi, parentWord_node]

theorem cellROM_flags [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) : InternalROMFor cache (cellROM cache node) := treeROM_flags cache

theorem cellROM_children [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) :
    ChildrenROMFor cache (List.finRange cache.nodes.size) (cache.nodes.size + 1) (cellROM cache node) := by
  apply childrenROMFor_of_slice
  intro position _
  have hi : ¬ cache.nodes.size + 1 + position < cache.nodes.size + 1 := by omega
  simp only [cellROM, hi, ↓reduceIte, Nat.add_sub_cancel_left]

def extensionInit (size badBase : Nat) : List Op :=
  [.base (.constant .index (badBase + size)), .base (.loadHeap .flag .index),
   .base (.constant .index 0), .base (.loadROM .input .address .index),
   .base (.constant .old 0), .base (.select .flag .address .flag .old), .base (.constant .total 1)]

def extensionStart [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (initial : State) : State :=
  execute (cellROM cache node) (extensionInit cache.nodes.size badBase)
    (IndexedRAM.execute (cellROM cache node) (copyWords badBase 0 cache.nodes.size) initial)

def extensionProgram (size badBase : Nat) : List Op :=
  (copyWords badBase 0 size).map Op.base ++ extensionInit size badBase ++
    ancestorLoop 0 size ++ extensionTail size

theorem extensionStart_heap [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (initial : State) :
    (extensionStart cache node badBase initial).heap =
      (IndexedRAM.execute (cellROM cache node) (copyWords badBase 0 cache.nodes.size) initial).heap := rfl

theorem extensionStart_registers [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (_hbad : cache.nodes.size < badBase) (initial : State) :
    (extensionStart cache node badBase initial).register .address = encodedNode cache node ∧
    (extensionStart cache node badBase initial).register .total = 1 ∧
    (extensionStart cache node badBase initial).register .flag =
      if encodedNode cache node = 0 then 0 else initial.heap (badBase + cache.nodes.size) := by
  have htag := copyWords_frame (cellROM cache node) badBase 0 cache.nodes.size initial
    (badBase + cache.nodes.size) (by intro i hi; omega)
  refine ⟨rfl, rfl, ?_⟩
  change (if encodedNode cache node = 0 then 0 else
    (IndexedRAM.execute (cellROM cache node) (copyWords badBase 0 cache.nodes.size) initial).heap
      (badBase + cache.nodes.size)) = _
  rw [htag]

theorem extensionStart_payload [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (hbad : cache.nodes.size < badBase)
    (capacity : IndexedCapacity cache) (initial : State) (hrep : SlotRep cache initial.heap badBase (.vector capacity)) :
    HeapAgrees (extensionStart cache node badBase initial).heap capacity := by
  intro target
  rw [extensionStart_heap]
  have hh := copyWords_value (cellROM cache node) badBase 0 cache.nodes.size
    (by intro i hi j hj; omega) initial target.val target.isLt
  simpa only [Nat.zero_add, hrep.2 target] using hh

def extensionResult [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (initial : State) : IndexedEntry.FixedEntry cache :=
  decodeResult cache (execute (cellROM cache node) (extensionProgram cache.nodes.size badBase) initial).heap

theorem extension_execute_split [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (initial : State) :
    execute (cellROM cache node) (extensionProgram cache.nodes.size badBase) initial =
      execute (cellROM cache node) (extensionTail cache.nodes.size)
        (execute (cellROM cache node) (ancestorLoop 0 cache.nodes.size)
          (extensionStart cache node badBase initial)) := by
  simp only [extensionProgram, IndexedClosureRAM.execute_append, execute_base, extensionStart]

theorem extensionResult_void_of_flag [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (hbad : cache.nodes.size < badBase) (initial : State)
    (hz : (extensionStart cache node badBase initial).register .flag = 0) :
    extensionResult cache node badBase initial = .void := by
  let start := extensionStart cache node badBase initial
  let value : WalkState cache := ⟨start.heap, 0, node⟩
  have hs := extensionStart_registers cache node badBase hbad initial
  have hv : Represents start value := ⟨rfl, hz, hs.1, hs.2.1⟩
  have hf := (ancestorLoop_represents cache _ 0 cache.nodes.size (cellROM_parent cache node) start value hv).2.1
  have hzero : (execute (cellROM cache node) (ancestorLoop 0 cache.nodes.size) start).register .flag = 0 :=
    hf.trans (walk_zero_flag _ value rfl)
  unfold extensionResult
  rw [extension_execute_split, extensionTail_heap]
  unfold decodeResult
  rw [Function.update_self, hzero]
  rfl

theorem extensionResult_vector [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : cache.NodeId) (badBase : Nat) (hbad : cache.nodes.size < badBase)
    (capacity : IndexedCapacity cache) (initial : State)
    (hrep : SlotRep cache initial.heap badBase (.vector capacity))
    (hnodup : (IndexedAncestors.ancestorChain cache node).Nodup) :
    extensionResult cache (some node) badBase initial =
      if IndexedAncestors.chainZero cache capacity node then .void
        else .vector (IndexedAncestors.chainDecrement cache capacity node) := by
  let rom := cellROM cache (some node)
  let start := extensionStart cache (some node) badBase initial
  let result := execute rom (ancestorLoop 0 cache.nodes.size) start
  have hs := extensionStart_registers cache (some node) badBase hbad initial
  have ha : start.register .address = node.val + 1 := hs.1
  have hone : start.register .total = 1 := hs.2.1
  have hflag : start.register .flag = 1 := by
    rw [hs.2.2, hrep.1]
    simp only [encodedNode, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false, ite_false]
  have hh : HeapAgrees result.heap (IndexedAncestors.chainDecrement cache capacity node) :=
    ancestorLoop_payload_refines cache rom 0 (cellROM_parent cache _) node start capacity
      (extensionStart_payload cache _ badBase hbad capacity initial hrep) ha hone
  have hf : result.register .flag = if IndexedAncestors.chainZero cache capacity node then 0 else 1 := by
    rw [ancestorLoop_flag_refines cache rom 0 (cellROM_parent cache _) node hnodup start capacity
      (extensionStart_payload cache _ badBase hbad capacity initial hrep) ha hone, hflag]
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

theorem extensionResult_eq [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (hbad : cache.nodes.size < badBase)
    (entry : IndexedEntry.FixedEntry cache) (initial : State) (hrep : SlotRep cache initial.heap badBase entry)
    (hnodup : ∀ node : cache.NodeId, (IndexedAncestors.ancestorChain cache node).Nodup) :
    extensionResult cache node badBase initial = IndexedStaticMetadata.extendAt cache node entry := by
  cases entry with
  | void =>
    apply extensionResult_void_of_flag cache node badBase hbad initial
    rw [(extensionStart_registers cache node badBase hbad initial).2.2, hrep]
    split_ifs <;> rfl
  | vector capacity =>
    cases node with
    | none =>
      apply extensionResult_void_of_flag cache none badBase hbad initial
      rw [(extensionStart_registers cache none badBase hbad initial).2.2]
      rfl
    | some node => exact extensionResult_vector cache node badBase hbad capacity initial hrep (hnodup node)

theorem walk_frame (cache : IndexedNodeCache Tool) (fuel : Nat) (value : WalkState cache)
    (address : Nat) (haddress : cache.nodes.size ≤ address) :
    (walk fuel value).heap address = value.heap address := by
  induction fuel generalizing value with
  | zero => rfl
  | succ fuel ih =>
    rw [walk, ih]
    cases hc : value.current with
    | none => simp only [walkStep, hc]
    | some node =>
      simp only [walkStep, hc]
      rw [Function.update_of_ne (by have := node.isLt; omega)]

theorem extensionProgram_frame [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (hbad : cache.nodes.size < badBase)
    (initial : State) (address : Nat) (haddress : cache.nodes.size < address) :
    (execute (cellROM cache node) (extensionProgram cache.nodes.size badBase) initial).heap address = initial.heap address := by
  let start := extensionStart cache node badBase initial
  let value : WalkState cache := ⟨start.heap, start.register .flag, node⟩
  have hs := extensionStart_registers cache node badBase hbad initial
  have hv : Represents start value := ⟨rfl, rfl, hs.1, hs.2.1⟩
  have hh := (ancestorLoop_represents cache _ 0 cache.nodes.size (cellROM_parent cache node) start value hv).1
  rw [extension_execute_split, extensionTail_heap, Function.update_of_ne (by omega)]
  change (execute (cellROM cache node) (ancestorLoop 0 cache.nodes.size) start).heap address = _
  rw [hh, walk_frame cache _ value address (by omega)]
  change start.heap address = _
  rw [extensionStart_heap]
  exact copyWords_frame _ _ _ _ _ _ (by intro i hi; omega)

def minimumBlock (goodBase index : Nat) : List Instruction :=
  [.constant .address (goodBase + index), .loadHeap .old .address,
   .constant .index index, .loadHeap .fresh .index,
   .minimum .value .old .fresh, .storeHeap .index .value]

def minimumIndices (goodBase : Nat) (indices : List Nat) : List Instruction :=
  indices.flatMap (minimumBlock goodBase)

def minimumPass (size goodBase : Nat) : List Instruction := minimumIndices goodBase (List.range size)

theorem execute_minimumBlock_heap (rom : ROM) (goodBase index : Nat) (state : State) :
    (IndexedRAM.execute rom (minimumBlock goodBase index) state).heap =
      Function.update state.heap index (min (state.heap (goodBase + index)) (state.heap index)) := rfl

theorem minimumIndices_frame (rom : ROM) (goodBase : Nat) (indices : List Nat)
    (state : State) (address : Nat) (hframe : address ∉ indices) :
    (IndexedRAM.execute rom (minimumIndices goodBase indices) state).heap address = state.heap address := by
  induction indices generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [minimumIndices, List.flatMap_cons, IndexedRAM.execute_append]
    change (IndexedRAM.execute rom (minimumIndices goodBase later)
      (IndexedRAM.execute rom (minimumBlock goodBase head) state)).heap address = _
    rw [ih _ (fun h => hframe (List.mem_cons_of_mem _ h)), execute_minimumBlock_heap,
      Function.update_of_ne (fun h => hframe (List.mem_cons.mpr (Or.inl h)))]

theorem minimumIndices_value (rom : ROM) (goodBase size : Nat) (hgood : size < goodBase)
    (indices : List Nat) (hindices : ∀ index ∈ indices, index < size) (hnodup : indices.Nodup)
    (state : State) (index : Nat) (hindex : index ∈ indices) :
    (IndexedRAM.execute rom (minimumIndices goodBase indices) state).heap index =
      min (state.heap (goodBase + index)) (state.heap index) := by
  induction indices generalizing state with
  | nil => cases hindex
  | cons head later ih =>
    have hn := List.nodup_cons.mp hnodup
    rw [minimumIndices, List.flatMap_cons, IndexedRAM.execute_append]
    change (IndexedRAM.execute rom (minimumIndices goodBase later)
      (IndexedRAM.execute rom (minimumBlock goodBase head) state)).heap index = _
    rcases List.mem_cons.mp hindex with heq | hi
    · subst index
      rw [minimumIndices_frame _ _ _ _ _ hn.1, execute_minimumBlock_heap, Function.update_self]
    · rw [ih (fun i hh => hindices i (List.mem_cons_of_mem _ hh)) hn.2 _ hi, execute_minimumBlock_heap]
      rw [Function.update_of_ne (by have := hindices head List.mem_cons_self; omega)]
      have hne : index ≠ head := by intro h; exact hn.1 (h ▸ hi)
      rw [Function.update_of_ne hne]

def minimumCapacity (cache : IndexedNodeCache Tool) (heap : Nat → Nat) (goodBase : Nat) : IndexedCapacity cache :=
  Vector.ofFn (fun node => min (heap (goodBase + node.val)) (heap node.val))

theorem minimumPass_refines (cache : IndexedNodeCache Tool) (rom : ROM) (goodBase : Nat)
    (hgood : cache.nodes.size < goodBase) (state : State) :
    HeapAgrees (IndexedRAM.execute rom (minimumPass cache.nodes.size goodBase) state).heap
      (minimumCapacity cache state.heap goodBase) := by
  intro node
  rw [minimumPass, minimumIndices_value rom goodBase cache.nodes.size hgood (List.range cache.nodes.size)
    (fun i hi => List.mem_range.mp hi) List.nodup_range state node.val (List.mem_range.mpr node.isLt)]
  simp only [minimumCapacity, cache_get_ofFn]

theorem minimumPass_frame (rom : ROM) (size goodBase : Nat) (state : State)
    (address : Nat) (ha : size ≤ address) :
    (IndexedRAM.execute rom (minimumPass size goodBase) state).heap address = state.heap address :=
  minimumIndices_frame _ _ _ _ _ (by simpa only [List.mem_range, not_lt] using ha)

theorem compileNodes_frame (cache : IndexedNodeCache Tool) (rom : ROM)
    (parents : List cache.NodeId) (offset : Nat) (state : State)
    (address : Nat) (ha : cache.nodes.size ≤ address) :
    (IndexedRAM.execute rom (compileNodes cache parents offset) state).heap address = state.heap address := by
  induction parents generalizing offset state with
  | nil => rfl
  | cons parent later ih =>
    rw [compileNodes, IndexedRAM.execute_append, ih, execute_nodeProgram_heap,
      Function.update_of_ne (by have := parent.isLt; omega)]

def tagTail (size goodBase : Nat) : List Instruction :=
  [.constant .index (goodBase + size), .loadHeap .old .index,
   .constant .index size, .loadHeap .fresh .index,
   .minimum .value .old .fresh, .storeHeap .index .value]

theorem execute_tagTail_heap (rom : ROM) (size goodBase : Nat) (state : State) :
    (IndexedRAM.execute rom (tagTail size goodBase) state).heap =
      Function.update state.heap size (min (state.heap (goodBase + size)) (state.heap size)) := rfl

def intersectionProgram (cache : IndexedNodeCache Tool) (goodBase : Nat) : List Instruction :=
  minimumPass cache.nodes.size goodBase ++ compileNodes cache (List.finRange cache.nodes.size)
    (cache.nodes.size + 1) ++ tagTail cache.nodes.size goodBase

theorem intersectionProgram_payload [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase : Nat) (hgood : cache.nodes.size < goodBase) (state : State) :
    HeapAgrees (IndexedRAM.execute (cellROM cache node) (intersectionProgram cache goodBase) state).heap
      (cache.normalize (minimumCapacity cache state.heap goodBase)) := by
  intro target
  rw [intersectionProgram, IndexedRAM.execute_append, execute_tagTail_heap,
    Function.update_of_ne (Nat.ne_of_lt target.isLt), IndexedRAM.execute_append]
  exact (execute_compileNodes_refines cache _ _ _ _ _ (minimumPass_refines cache _ goodBase hgood state)
    (cellROM_flags cache node) (cellROM_children cache node)) target

theorem intersectionProgram_tag [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase : Nat) (hgood : cache.nodes.size < goodBase) (state : State) :
    (IndexedRAM.execute (cellROM cache node) (intersectionProgram cache goodBase) state).heap cache.nodes.size =
      min (state.heap (goodBase + cache.nodes.size)) (state.heap cache.nodes.size) := by
  rw [intersectionProgram, IndexedRAM.execute_append, execute_tagTail_heap, Function.update_self,
    IndexedRAM.execute_append, compileNodes_frame cache _ _ _ _ _ (by omega),
    compileNodes_frame cache _ _ _ _ _ (by omega), minimumPass_frame _ _ _ _ _ (by omega),
    minimumPass_frame _ _ _ _ _ (by omega)]

theorem intersectionProgram_frame (cache : IndexedNodeCache Tool) (rom : ROM) (goodBase : Nat)
    (state : State) (address : Nat) (ha : cache.nodes.size < address) :
    (IndexedRAM.execute rom (intersectionProgram cache goodBase) state).heap address = state.heap address := by
  rw [intersectionProgram, IndexedRAM.execute_append, execute_tagTail_heap, Function.update_of_ne (by omega),
    IndexedRAM.execute_append, compileNodes_frame cache rom _ _ _ _ (by omega),
    minimumPass_frame _ _ _ _ _ (by omega)]

def intersectionResult [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase : Nat) (state : State) : IndexedEntry.FixedEntry cache :=
  decodeResult cache (IndexedRAM.execute (cellROM cache node) (intersectionProgram cache goodBase) state).heap

theorem intersectionResult_eq [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase : Nat) (hgood : cache.nodes.size < goodBase)
    (good : IndexedEntry.FixedEntry cache) (state : State) (hrep : SlotRep cache state.heap goodBase good) :
    intersectionResult cache node goodBase state =
      IndexedEntry.intersect cache good (decodeResult cache state.heap) := by
  have ht := intersectionProgram_tag cache node goodBase hgood state
  have hp := intersectionProgram_payload cache node goodBase hgood state
  unfold intersectionResult decodeResult
  rw [ht]
  cases good with
  | void =>
    rw [hrep, Nat.zero_min]
    simp only [↓reduceIte, IndexedEntry.intersect, IndexedEntry.coordinateMin, IndexedEntry.normalize]
  | vector capacity =>
    rw [hrep.1]
    by_cases hz : state.heap cache.nodes.size = 0
    · rw [hz, Nat.min_zero]
      simp only [↓reduceIte, IndexedEntry.intersect, IndexedEntry.coordinateMin, IndexedEntry.normalize]
    · have hmin : min 1 (state.heap cache.nodes.size) ≠ 0 := by omega
      simp only [hmin, hz, ↓reduceIte]
      rw [readCapacity_eq cache _ _ hp]
      have hc : minimumCapacity cache state.heap goodBase =
          Vector.ofFn (fun node => min (capacity.get node) ((readCapacity cache state.heap).get node)) := by
        apply Vector.ext
        intro i hi
        change (Vector.ofFn _).get ⟨i, hi⟩ = (Vector.ofFn _).get ⟨i, hi⟩
        simp only [cache_get_ofFn, hrep.2 ⟨i, hi⟩, readCapacity]
      rw [hc]
      rfl

theorem SlotRep.transfer (cache : IndexedNodeCache Tool) (old fresh : Nat → Nat) (base : Nat)
    (entry : IndexedEntry.FixedEntry cache) (hrep : SlotRep cache old base entry)
    (hframe : ∀ i ≤ cache.nodes.size, fresh (base + i) = old (base + i)) : SlotRep cache fresh base entry := by
  cases entry with
  | void => exact (hframe _ (by omega)).trans hrep
  | vector capacity =>
    exact ⟨(hframe _ (by omega)).trans hrep.1, fun node => (hframe node.val (by omega)).trans (hrep.2 node)⟩

def kernelProgram (cache : IndexedNodeCache Tool) (goodBase badBase : Nat) : List Op :=
  extensionProgram cache.nodes.size badBase ++ (intersectionProgram cache goodBase).map Op.base

def kernelResult [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase : Nat) (initial : State) : IndexedEntry.FixedEntry cache :=
  decodeResult cache (execute (cellROM cache node) (kernelProgram cache goodBase badBase) initial).heap

theorem kernelResult_eq [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase : Nat) (hgood : cache.nodes.size < goodBase) (hbad : cache.nodes.size < badBase)
    (good bad : IndexedEntry.FixedEntry cache) (initial : State)
    (hg : SlotRep cache initial.heap goodBase good) (hb : SlotRep cache initial.heap badBase bad)
    (hnodup : ∀ node : cache.NodeId, (IndexedAncestors.ancestorChain cache node).Nodup) :
    kernelResult cache node goodBase badBase initial = IndexedStaticMetadata.cellAt cache node good bad := by
  let middle := execute (cellROM cache node) (extensionProgram cache.nodes.size badBase) initial
  have hg' : SlotRep cache middle.heap goodBase good :=
    SlotRep.transfer cache initial.heap middle.heap goodBase good hg
      (fun i _ => extensionProgram_frame cache node badBase hbad initial (goodBase + i) (by omega))
  unfold kernelResult kernelProgram
  rw [IndexedClosureRAM.execute_append, execute_base]
  change intersectionResult cache node goodBase middle = _
  rw [intersectionResult_eq cache node goodBase hgood good middle hg']
  change IndexedEntry.intersect cache good (extensionResult cache node badBase initial) = _
  rw [extensionResult_eq cache node badBase hbad bad initial hb hnodup]
  rfl

theorem kernelProgram_frame [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase : Nat) (hbad : cache.nodes.size < badBase)
    (initial : State) (address : Nat) (ha : cache.nodes.size < address) :
    (execute (cellROM cache node) (kernelProgram cache goodBase badBase) initial).heap address = initial.heap address := by
  rw [kernelProgram, IndexedClosureRAM.execute_append, execute_base, intersectionProgram_frame cache _ goodBase _ address ha,
    extensionProgram_frame cache node badBase hbad initial address ha]

theorem decodeResult_congr (cache : IndexedNodeCache Tool) (left right : Nat → Nat)
    (h : ∀ i ≤ cache.nodes.size, left i = right i) : decodeResult cache left = decodeResult cache right := by
  have ht := h cache.nodes.size (by omega)
  have hc : readCapacity cache left = readCapacity cache right := by
    apply Vector.ext
    intro i hi
    change (readCapacity cache left).get ⟨i, hi⟩ = (readCapacity cache right).get ⟨i, hi⟩
    simp only [readCapacity, cache_get_ofFn]
    exact h i (by omega)
  simp only [decodeResult, ht, hc]

theorem copyWords_slot (cache : IndexedNodeCache Tool) (rom : ROM) (output : Nat)
    (hout : cache.nodes.size < output) (state : State) :
    slot cache (IndexedRAM.execute rom (copyWords 0 output (cache.nodes.size + 1)) state).heap output =
      decodeResult cache state.heap := by
  apply decodeResult_congr
  intro i hi
  have hh := copyWords_value rom 0 output (cache.nodes.size + 1)
    (by intro a ha b hb; omega) state i (by omega)
  simpa only [Nat.zero_add] using hh

def cellProgram (cache : IndexedNodeCache Tool) (goodBase badBase output : Nat) : List Op :=
  kernelProgram cache goodBase badBase ++ (copyWords 0 output (cache.nodes.size + 1)).map Op.base

def cellResult [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase output : Nat) (initial : State) : IndexedEntry.FixedEntry cache :=
  slot cache (execute (cellROM cache node) (cellProgram cache goodBase badBase output) initial).heap output

theorem cellResult_eq [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase output : Nat)
    (hgood : cache.nodes.size < goodBase) (hbad : cache.nodes.size < badBase) (hout : cache.nodes.size < output)
    (good bad : IndexedEntry.FixedEntry cache) (initial : State)
    (hg : SlotRep cache initial.heap goodBase good) (hb : SlotRep cache initial.heap badBase bad)
    (hnodup : ∀ node : cache.NodeId, (IndexedAncestors.ancestorChain cache node).Nodup) :
    cellResult cache node goodBase badBase output initial = IndexedStaticMetadata.cellAt cache node good bad := by
  unfold cellResult cellProgram
  rw [IndexedClosureRAM.execute_append, execute_base, copyWords_slot cache _ output hout]
  exact kernelResult_eq cache node goodBase badBase hgood hbad good bad initial hg hb hnodup

theorem cellProgram_frame [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase output : Nat) (hbad : cache.nodes.size < badBase)
    (initial : State) (address : Nat) (ha : cache.nodes.size < address)
    (houtput : ∀ i ≤ cache.nodes.size, address ≠ output + i) :
    (execute (cellROM cache node) (cellProgram cache goodBase badBase output) initial).heap address = initial.heap address := by
  rw [cellProgram, IndexedClosureRAM.execute_append, execute_base,
    copyWords_frame _ _ _ _ _ _ (by intro i hi; exact houtput i (by omega)),
    kernelProgram_frame cache node goodBase badBase hbad initial address ha]

theorem cellProgram_preserves_slot [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase output : Nat) (hbad : cache.nodes.size < badBase)
    (initial : State) (source : Nat) (hsource : cache.nodes.size < source)
    (hdisjoint : ∀ i ≤ cache.nodes.size, ∀ j ≤ cache.nodes.size, source + i ≠ output + j) :
    ∀ i ≤ cache.nodes.size,
      (execute (cellROM cache node) (cellProgram cache goodBase badBase output) initial).heap (source + i) =
        initial.heap (source + i) := by
  intro i hi
  exact cellProgram_frame cache node goodBase badBase output hbad initial _ (by omega) (hdisjoint i hi)

theorem extensionProgram_length (size badBase : Nat) :
    (extensionProgram size badBase).length = 15 * size + 9 := by
  simp only [extensionProgram, List.length_append, List.length_map, copyWords_length, extensionInit,
    extensionTail, List.length_cons, List.length_nil, ancestorLoop_length]
  omega

theorem extensionProgram_trace_length (size badBase : Nat) :
    (trace (extensionProgram size badBase)).length = 156 * size + 85 := by
  have hi : (trace (extensionInit size badBase)).length = 66 := rfl
  have ht : (trace (extensionTail size)).length = 19 := rfl
  simp only [extensionProgram, trace_append, List.length_append, trace_base_length,
    copyWords_trace_length, hi, ancestorLoop_trace_length, ht]
  omega

theorem minimumPass_length (size goodBase : Nat) : (minimumPass size goodBase).length = 6 * size := by
  simp only [minimumPass, minimumIndices, List.length_flatMap, minimumBlock, List.length_cons, List.length_nil,
    List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem minimumPass_trace_length (size goodBase : Nat) :
    (primitiveTrace (minimumPass size goodBase)).length = 60 * size := by
  rw [minimumPass, minimumIndices, primitiveTrace_length_flatMap]
  have hblock : ∀ i, (primitiveTrace (minimumBlock goodBase i)).length = 60 := fun _ => rfl
  simp only [hblock, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul]
  omega

theorem intersectionProgram_length (cache : IndexedNodeCache Tool) (goodBase : Nat) :
    (intersectionProgram cache goodBase).length = 14 * cache.nodes.size +
      6 * (∑ node : cache.NodeId, (cache.children.get node).size) + 6 := by
  have ht : (tagTail cache.nodes.size goodBase).length = 6 := rfl
  simp only [intersectionProgram, List.length_append, minimumPass_length, compileNodes_length,
    List.length_finRange, childArray_sum_finRange, ht]
  omega

theorem intersectionProgram_trace_length (cache : IndexedNodeCache Tool) (goodBase : Nat) :
    (primitiveTrace (intersectionProgram cache goodBase)).length = 140 * cache.nodes.size +
      60 * (∑ node : cache.NodeId, (cache.children.get node).size) + 60 := by
  have ht : (primitiveTrace (tagTail cache.nodes.size goodBase)).length = 60 := rfl
  simp only [intersectionProgram, primitiveTrace_append, List.length_append, minimumPass_trace_length,
    compileNodes_trace_length, List.length_finRange, childArray_sum_finRange, ht]
  omega

theorem cellProgram_length (cache : IndexedNodeCache Tool) (goodBase badBase output : Nat) :
    (cellProgram cache goodBase badBase output).length = 33 * cache.nodes.size +
      6 * (∑ node : cache.NodeId, (cache.children.get node).size) + 19 := by
  simp only [cellProgram, kernelProgram, List.length_append, List.length_map, extensionProgram_length,
    intersectionProgram_length, copyWords_length]
  omega

theorem cellProgram_trace_length (cache : IndexedNodeCache Tool) (goodBase badBase output : Nat) :
    (trace (cellProgram cache goodBase badBase output)).length = 334 * cache.nodes.size +
      60 * (∑ node : cache.NodeId, (cache.children.get node).size) + 183 := by
  simp only [cellProgram, kernelProgram, trace_append, List.length_append, trace_base_length,
    extensionProgram_trace_length, intersectionProgram_trace_length, copyWords_trace_length]
  omega

theorem prepared_cellProgram_trace_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodBase badBase output : Nat) :
    (trace (cellProgram (prepareNormalization q full).indexed goodBase badBase output) ++ haltTrace).length ≤
      523 * (prepareNormalization q full).indexed.nodes.size := by
  rw [List.length_append, haltTrace_length, cellProgram_trace_length, prepared_indexed_edge_count q full hq hlaminar]
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hp : 0 < (prepareNormalization q full).indexed.nodes.size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  omega

theorem prepared_stage_cell_correct_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Fin full.length)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hgood : IndexedEntry.IsNormalized (prepareNormalization q full).indexed good)
    (hbad : IndexedEntry.IsNormalized (prepareNormalization q full).indexed bad)
    (goodBase badBase output : Nat)
    (hgoodBase : (prepareNormalization q full).indexed.nodes.size < goodBase)
    (hbadBase : (prepareNormalization q full).indexed.nodes.size < badBase)
    (hout : (prepareNormalization q full).indexed.nodes.size < output)
    (initial : State) (hpc : initial.pc = 0)
    (hg : SlotRep (prepareNormalization q full).indexed initial.heap goodBase good)
    (hb : SlotRep (prepareNormalization q full).indexed initial.heap badBase bad) :
    let cache := (prepareNormalization q full).indexed
    let node := (IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage
    ∃ final operations,
      IndexedClosureRAM.HaltingRuns (cellROM cache node) (cellProgram cache goodBase badBase output) initial final operations ∧
      slot cache final.heap output = IndexedEntry.cell cache full[stage.val] good bad ∧
      (slot cache final.heap output).denote cache = good.denote cache ∩ usedExtension full[stage.val] (bad.denote cache) ∧
      IndexedEntry.IsNormalized cache (slot cache final.heap output) ∧
      (slot cache final.heap output).Bounded q ∧
      operations.length ≤ 523 * cache.nodes.size := by
  dsimp only
  let cache := (prepareNormalization q full).indexed
  let node := (IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage
  have houtcome := cellResult_eq cache node goodBase badBase output hgoodBase hbadBase hout good bad initial hg hb
    (fun node => IndexedAncestors.prepared_ancestorChain_nodup q full hq hlaminar node)
  rw [IndexedStaticMetadata.buildPositive_cellAt_eq_indexed q full hq hlaminar stage] at houtcome
  unfold cellResult at houtcome
  refine ⟨_, _, execute_halts _ _ initial hpc, houtcome, ?_⟩
  rw [houtcome]
  have heligible : full[stage.val] = ∅ ∨ full[stage.val] ∈ nodeFamily full := by
    by_cases he : full[stage.val] = ∅
    · exact Or.inl he
    · exact Or.inr (nonempty_stage_mem full (List.getElem_mem stage.isLt) (Finset.nonempty_iff_ne_empty.mpr he))
  have hn := IndexedEntry.prepared_cell_normalized_bounded q full hq hlaminar full[stage.val] good bad hgood
  exact ⟨IndexedEntry.prepared_cell_denote q full hq hlaminar full[stage.val] heligible good bad hbad,
    hn.1, hn.2, prepared_cellProgram_trace_le q full hq hlaminar goodBase badBase output⟩

theorem prepared_cellProgram_codeWords_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodBase badBase output : Nat) :
    (haltingWords (cellProgram (prepareNormalization q full).indexed goodBase badBase output)).length ≤
      265 * (prepareNormalization q full).indexed.nodes.size := by
  rw [haltingWords_length, cellProgram_length, prepared_indexed_edge_count q full hq hlaminar]
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hp : 0 < (prepareNormalization q full).indexed.nodes.size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  omega

/-- Static card constants are emitted once from the given tree. Each write
is a real three-instruction block, not a runtime vector constructor. -/
def constantBlock (index value : Nat) : List Instruction :=
  [.constant .index index, .constant .value value, .storeHeap .index .value]

theorem execute_constantBlock_heap (rom : ROM) (index value : Nat) (state : State) :
    (IndexedRAM.execute rom (constantBlock index value) state).heap = Function.update state.heap index value := rfl

def freeIndices (cache : IndexedNodeCache Tool) (nodes : List cache.NodeId) : List Instruction :=
  nodes.flatMap (fun node => constantBlock node.val (cache.decode node).card)

theorem freeIndices_value (cache : IndexedNodeCache Tool) (rom : ROM) (nodes : List cache.NodeId)
    (state : State) (target : cache.NodeId) :
    (IndexedRAM.execute rom (freeIndices cache nodes) state).heap target.val =
      if target ∈ nodes then (cache.decode target).card else state.heap target.val := by
  induction nodes generalizing state with
  | nil => simp only [freeIndices, List.flatMap_nil, IndexedRAM.execute, List.not_mem_nil, ↓reduceIte]
  | cons head later ih =>
    rw [freeIndices, List.flatMap_cons, IndexedRAM.execute_append]
    change (IndexedRAM.execute rom (freeIndices cache later)
      (IndexedRAM.execute rom (constantBlock head.val (cache.decode head).card) state)).heap target.val = _
    rw [ih, execute_constantBlock_heap]
    by_cases heq : target = head
    · subst target
      simp only [List.mem_cons_self, ↓reduceIte, Function.update_self, ite_self]
    · have hne : target.val ≠ head.val := fun h => heq (Fin.ext h)
      simp only [List.mem_cons, heq, false_or, Function.update_of_ne hne]

theorem freeIndices_frame (cache : IndexedNodeCache Tool) (rom : ROM) (nodes : List cache.NodeId)
    (state : State) (address : Nat) (ha : cache.nodes.size ≤ address) :
    (IndexedRAM.execute rom (freeIndices cache nodes) state).heap address = state.heap address := by
  induction nodes generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [freeIndices, List.flatMap_cons, IndexedRAM.execute_append]
    change (IndexedRAM.execute rom (freeIndices cache later)
      (IndexedRAM.execute rom (constantBlock head.val (cache.decode head).card) state)).heap address = _
    rw [ih, execute_constantBlock_heap, Function.update_of_ne (by have := head.isLt; omega)]

def freeKernel (cache : IndexedNodeCache Tool) : List Instruction :=
  freeIndices cache (List.finRange cache.nodes.size) ++ constantBlock cache.nodes.size 1

theorem freeKernel_result (cache : IndexedNodeCache Tool) (rom : ROM) (state : State) :
    decodeResult cache (IndexedRAM.execute rom (freeKernel cache) state).heap = IndexedEntry.free cache := by
  have ht : (IndexedRAM.execute rom (freeKernel cache) state).heap cache.nodes.size = 1 := by
    rw [freeKernel, IndexedRAM.execute_append, execute_constantBlock_heap, Function.update_self]
  have hp : HeapAgrees (IndexedRAM.execute rom (freeKernel cache) state).heap
      (IndexedEntry.reifyCapacity cache Finset.card) := by
    intro node
    rw [freeKernel, IndexedRAM.execute_append, execute_constantBlock_heap,
      Function.update_of_ne (Nat.ne_of_lt node.isLt), freeIndices_value]
    simp only [List.mem_finRange, ↓reduceIte, IndexedEntry.reifyCapacity_get]
  unfold decodeResult
  rw [ht]
  simp only [Nat.one_ne_zero, ↓reduceIte]
  rw [readCapacity_eq cache _ _ hp]
  rfl

def freeProgram (cache : IndexedNodeCache Tool) (output : Nat) : List Op :=
  (freeKernel cache).map Op.base ++ (copyWords 0 output (cache.nodes.size + 1)).map Op.base

theorem freeProgram_result (cache : IndexedNodeCache Tool) (rom : ROM) (output : Nat)
    (hout : cache.nodes.size < output) (initial : State) :
    slot cache (execute rom (freeProgram cache output) initial).heap output = IndexedEntry.free cache := by
  rw [freeProgram, IndexedClosureRAM.execute_append, execute_base, execute_base, copyWords_slot cache rom output hout,
    freeKernel_result]

theorem freeProgram_frame (cache : IndexedNodeCache Tool) (rom : ROM) (output : Nat)
    (state : State) (address : Nat) (ha : cache.nodes.size < address)
    (houtput : ∀ i ≤ cache.nodes.size, address ≠ output + i) :
    (execute rom (freeProgram cache output) state).heap address = state.heap address := by
  rw [freeProgram, IndexedClosureRAM.execute_append, execute_base, execute_base,
    copyWords_frame _ _ _ _ _ _ (by intro i hi; exact houtput i (by omega)), freeKernel,
    IndexedRAM.execute_append, execute_constantBlock_heap, Function.update_of_ne (by omega),
    freeIndices_frame cache rom _ _ address (by omega)]

theorem freeIndices_trace_length (cache : IndexedNodeCache Tool) (nodes : List cache.NodeId) :
    (primitiveTrace (freeIndices cache nodes)).length = 27 * nodes.length := by
  rw [freeIndices, primitiveTrace_length_flatMap]
  have hb : ∀ node : cache.NodeId, (primitiveTrace (constantBlock node.val (cache.decode node).card)).length = 27 := fun _ => rfl
  simp only [hb, List.map_const', List.sum_replicate, Nat.nsmul_eq_mul]
  omega

theorem freeProgram_trace_length (cache : IndexedNodeCache Tool) (output : Nat) :
    (trace (freeProgram cache output) ++ haltTrace).length = 65 * cache.nodes.size + 71 := by
  have ht : (primitiveTrace (constantBlock cache.nodes.size 1)).length = 27 := rfl
  simp only [List.length_append, haltTrace_length, freeProgram, trace_append, trace_base_length, freeKernel,
    primitiveTrace_append, List.length_append, freeIndices_trace_length, List.length_finRange, ht, copyWords_trace_length]
  omega

def budgetProgram (cache : IndexedNodeCache Tool) (goodBase badBase output budget : Nat) : List Op :=
  if budget = 0 then freeProgram cache output else cellProgram cache goodBase badBase output

def budgetResult [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase output budget : Nat) (initial : State) : IndexedEntry.FixedEntry cache :=
  slot cache (execute (cellROM cache node) (budgetProgram cache goodBase badBase output budget) initial).heap output

theorem budgetResult_eq [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase output budget : Nat)
    (hgood : cache.nodes.size < goodBase) (hbad : cache.nodes.size < badBase) (hout : cache.nodes.size < output)
    (good bad : IndexedEntry.FixedEntry cache) (initial : State)
    (hg : SlotRep cache initial.heap goodBase good) (hb : SlotRep cache initial.heap badBase bad)
    (hnodup : ∀ node : cache.NodeId, (IndexedAncestors.ancestorChain cache node).Nodup) :
    budgetResult cache node goodBase badBase output budget initial = IndexedStaticMetadata.budgetCellAt cache node budget good bad := by
  by_cases hz : budget = 0
  · simp only [budgetResult, budgetProgram, hz, ↓reduceIte, IndexedStaticMetadata.budgetCellAt]
    exact freeProgram_result cache _ output hout initial
  · simp only [budgetResult, budgetProgram, hz, ↓reduceIte, IndexedStaticMetadata.budgetCellAt]
    exact cellResult_eq cache node goodBase badBase output hgood hbad hout good bad initial hg hb hnodup

theorem prepared_budgetProgram_trace_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodBase badBase output budget : Nat) :
    (trace (budgetProgram (prepareNormalization q full).indexed goodBase badBase output budget) ++ haltTrace).length ≤
      523 * (prepareNormalization q full).indexed.nodes.size := by
  by_cases hz : budget = 0
  · rw [budgetProgram, ite_eq_left hz, freeProgram_trace_length]
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    have hp : 0 < (prepareNormalization q full).indexed.nodes.size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
    omega
  · rw [budgetProgram, ite_eq_right hz]
    exact prepared_cellProgram_trace_le q full hq hlaminar goodBase badBase output

theorem zeroTool_budgetResult (good bad : IndexedEntry.FixedEntry (IndexedTable.emptyCache (Fin 0)))
    (goodBase badBase output budget : Nat) (hgood : 0 < goodBase) (hbad : 0 < badBase) (hout : 0 < output)
    (initial : State) (hg : SlotRep (IndexedTable.emptyCache (Fin 0)) initial.heap goodBase good)
    (hb : SlotRep (IndexedTable.emptyCache (Fin 0)) initial.heap badBase bad) :
    budgetResult (IndexedTable.emptyCache (Fin 0)) none goodBase badBase output budget initial =
      if budget = 0 then IndexedEntry.free (IndexedTable.emptyCache (Fin 0)) else .void := by
  rw [budgetResult_eq (IndexedTable.emptyCache (Fin 0)) none goodBase badBase output budget hgood hbad hout good bad initial hg hb
    (fun node => Fin.elim0 node)]
  unfold IndexedStaticMetadata.budgetCellAt
  split_ifs
  · rfl
  · cases good <;> cases bad <;> rfl

theorem zeroTool_budgetProgram_trace_le (goodBase badBase output budget : Nat) :
    (trace (budgetProgram (IndexedTable.emptyCache (Fin 0)) goodBase badBase output budget) ++ haltTrace).length ≤ 189 := by
  by_cases hz : budget = 0
  · rw [budgetProgram, ite_eq_left hz, freeProgram_trace_length]
    decide
  · rw [budgetProgram, ite_eq_right hz, List.length_append, haltTrace_length, cellProgram_trace_length]
    simp [IndexedTable.emptyCache]

theorem budgetProgram_frame [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase output budget : Nat) (hbad : cache.nodes.size < badBase)
    (initial : State) (address : Nat) (ha : cache.nodes.size < address)
    (houtput : ∀ i ≤ cache.nodes.size, address ≠ output + i) :
    (execute (cellROM cache node) (budgetProgram cache goodBase badBase output budget) initial).heap address = initial.heap address := by
  by_cases hz : budget = 0
  · rw [budgetProgram, ite_eq_left hz]
    exact freeProgram_frame cache _ output initial address ha houtput
  · rw [budgetProgram, ite_eq_right hz]
    exact cellProgram_frame cache node goodBase badBase output hbad initial address ha houtput

theorem walk_flag_le (cache : IndexedNodeCache Tool) (fuel : Nat) (value : WalkState cache) :
    (walk fuel value).flag ≤ value.flag := by
  induction fuel generalizing value with
  | zero => exact Nat.le_refl _
  | succ fuel ih =>
    rw [walk]
    apply (ih _).trans
    cases hc : value.current with
    | none => simpa only [walkStep, hc] using (Nat.le_refl value.flag)
    | some node =>
      simp only [walkStep, hc]
      split_ifs <;> omega

theorem extensionProgram_tag_le_one [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (badBase : Nat) (hbad : cache.nodes.size < badBase)
    (bad : IndexedEntry.FixedEntry cache) (initial : State) (hb : SlotRep cache initial.heap badBase bad) :
    (execute (cellROM cache node) (extensionProgram cache.nodes.size badBase) initial).heap cache.nodes.size ≤ 1 := by
  let start := extensionStart cache node badBase initial
  let value : WalkState cache := ⟨start.heap, start.register .flag, node⟩
  have hs := extensionStart_registers cache node badBase hbad initial
  have hv : Represents start value := ⟨rfl, rfl, hs.1, hs.2.1⟩
  have hf := (ancestorLoop_represents cache _ 0 cache.nodes.size (cellROM_parent cache node) start value hv).2.1
  have hstart : start.register .flag ≤ 1 := by
    rw [hs.2.2]
    cases bad with
    | void => rw [hb]; split_ifs <;> omega
    | vector capacity => rw [hb.1]; split_ifs <;> omega
  rw [extension_execute_split, extensionTail_heap, Function.update_self]
  exact (hf.le.trans (walk_flag_le cache _ value)).trans hstart

theorem cellProgram_outputTag_le_one [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase output : Nat)
    (hgood : cache.nodes.size < goodBase) (hbad : cache.nodes.size < badBase) (hout : cache.nodes.size < output)
    (bad : IndexedEntry.FixedEntry cache) (initial : State) (hb : SlotRep cache initial.heap badBase bad) :
    (execute (cellROM cache node) (cellProgram cache goodBase badBase output) initial).heap (output + cache.nodes.size) ≤ 1 := by
  rw [cellProgram, IndexedClosureRAM.execute_append, execute_base]
  rw [copyWords_value _ 0 output (cache.nodes.size + 1) (by intro i hi j hj; omega) _ cache.nodes.size (by omega)]
  simp only [Nat.zero_add]
  rw [kernelProgram, IndexedClosureRAM.execute_append, execute_base, intersectionProgram_tag cache node goodBase hgood]
  exact (Nat.min_le_right _ _).trans (extensionProgram_tag_le_one cache node badBase hbad bad initial hb)

theorem budgetProgram_outputTag_le_one [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (goodBase badBase output budget : Nat)
    (hgood : cache.nodes.size < goodBase) (hbad : cache.nodes.size < badBase) (hout : cache.nodes.size < output)
    (bad : IndexedEntry.FixedEntry cache) (initial : State) (hb : SlotRep cache initial.heap badBase bad) :
    (execute (cellROM cache node) (budgetProgram cache goodBase badBase output budget) initial).heap (output + cache.nodes.size) ≤ 1 := by
  by_cases hz : budget = 0
  · rw [budgetProgram, ite_eq_left hz, freeProgram, IndexedClosureRAM.execute_append, execute_base, execute_base,
      copyWords_value _ 0 output (cache.nodes.size + 1) (by intro i hi j hj; omega) _ cache.nodes.size (by omega)]
    simp only [Nat.zero_add]
    rw [freeKernel, IndexedRAM.execute_append, execute_constantBlock_heap, Function.update_self]
  · rw [budgetProgram, ite_eq_right hz]
    exact cellProgram_outputTag_le_one cache node goodBase badBase output hgood hbad hout bad initial hb

theorem freeProgram_length (cache : IndexedNodeCache Tool) (output : Nat) :
    (freeProgram cache output).length = 7 * cache.nodes.size + 7 := by
  have hblock : ∀ node : cache.NodeId, (constantBlock node.val (cache.decode node).card).length = 3 := fun _ => rfl
  have ht : (constantBlock cache.nodes.size 1).length = 3 := rfl
  simp only [freeProgram, List.length_append, List.length_map, freeKernel, freeIndices, List.length_flatMap,
    hblock, List.map_const', List.sum_replicate, List.length_finRange, Nat.nsmul_eq_mul, ht, copyWords_length]
  omega

theorem prepared_budgetProgram_codeWords_le (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (goodBase badBase output budget : Nat) :
    (haltingWords (budgetProgram (prepareNormalization q full).indexed goodBase badBase output budget)).length ≤
      265 * (prepareNormalization q full).indexed.nodes.size := by
  by_cases hz : budget = 0
  · rw [budgetProgram, ite_eq_left hz, haltingWords_length, freeProgram_length]
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    have hp : 0 < (prepareNormalization q full).indexed.nodes.size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
    omega
  · rw [budgetProgram, ite_eq_right hz]
    exact prepared_cellProgram_codeWords_le q full hq hlaminar goodBase badBase output

theorem prepared_stage_budget_correct_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Fin full.length) (budget : Nat)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hgood : IndexedEntry.IsNormalized (prepareNormalization q full).indexed good)
    (goodBase badBase output : Nat)
    (hgoodBase : (prepareNormalization q full).indexed.nodes.size < goodBase)
    (hbadBase : (prepareNormalization q full).indexed.nodes.size < badBase)
    (hout : (prepareNormalization q full).indexed.nodes.size < output)
    (initial : State) (hpc : initial.pc = 0)
    (hg : SlotRep (prepareNormalization q full).indexed initial.heap goodBase good)
    (hb : SlotRep (prepareNormalization q full).indexed initial.heap badBase bad) :
    let cache := (prepareNormalization q full).indexed
    let node := (IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage
    ∃ final operations,
      IndexedClosureRAM.HaltingRuns (cellROM cache node) (budgetProgram cache goodBase badBase output budget) initial final operations ∧
      slot cache final.heap output = IndexedEntry.budgetCell cache full[stage.val] budget good bad ∧
      SlotRep cache final.heap output (IndexedEntry.budgetCell cache full[stage.val] budget good bad) ∧
      IndexedEntry.IsNormalized cache (slot cache final.heap output) ∧
      (slot cache final.heap output).Bounded q ∧
      (∀ address, cache.nodes.size < address → (∀ i ≤ cache.nodes.size, address ≠ output + i) →
        final.heap address = initial.heap address) ∧
      operations.length ≤ 523 * cache.nodes.size := by
  dsimp only
  let cache := (prepareNormalization q full).indexed
  let node := (IndexedStaticMetadata.buildPositive q full hq).stageNodes.get stage
  have heq := budgetResult_eq cache node goodBase badBase output budget hgoodBase hbadBase hout good bad initial hg hb
    (fun node => IndexedAncestors.prepared_ancestorChain_nodup q full hq hlaminar node)
  rw [IndexedStaticMetadata.buildPositive_budgetCellAt_eq_indexed q full hq hlaminar stage budget] at heq
  unfold budgetResult at heq
  refine ⟨_, _, execute_halts _ _ initial hpc, heq,
    slotRep_of_decode cache _ output _
      (budgetProgram_outputTag_le_one cache node goodBase badBase output budget hgoodBase hbadBase hout bad initial hb) heq, ?_⟩
  rw [heq]
  have hn : IndexedEntry.IsNormalized cache (IndexedEntry.budgetCell cache full[stage.val] budget good bad) ∧
      (IndexedEntry.budgetCell cache full[stage.val] budget good bad).Bounded q := by
    by_cases hz : budget = 0
    · rw [IndexedEntry.budgetCell, ite_eq_left hz]
      exact ⟨IndexedTable.prepared_free_normalized q full hq hlaminar, IndexedEntry.free_bounded q cache⟩
    · rw [IndexedEntry.budgetCell, ite_eq_right hz]
      exact IndexedEntry.prepared_cell_normalized_bounded q full hq hlaminar full[stage.val] good bad hgood
  exact ⟨hn.1, hn.2, fun address ha ho => budgetProgram_frame cache node goodBase badBase output budget hbadBase initial address ha ho,
    prepared_budgetProgram_trace_le q full hq hlaminar goodBase badBase output budget⟩

/-- Four genuinely disjoint fixed slots: work, good, bad, output. The final
two preservation conclusions retain the source cells for subsequent DP
budgets. No host vector is read or copied as a single machine operation. -/
theorem fixedSlots_preserved [DecidableEq Tool] [Fintype Tool] (cache : IndexedNodeCache Tool)
    (node : Option cache.NodeId) (budget : Nat) (initial : State) :
    let size := cache.nodes.size
    let final := execute (cellROM cache node) (budgetProgram cache (size + 1) (2 * (size + 1)) (3 * (size + 1)) budget) initial
    (∀ i ≤ size, final.heap (size + 1 + i) = initial.heap (size + 1 + i)) ∧
    (∀ i ≤ size, final.heap (2 * (size + 1) + i) = initial.heap (2 * (size + 1) + i)) := by
  dsimp only
  constructor
  · intro i hi
    apply budgetProgram_frame cache node (cache.nodes.size + 1) (2 * (cache.nodes.size + 1)) (3 * (cache.nodes.size + 1)) budget
      (by omega) initial _ (by omega)
    intro j hj
    omega
  · intro i hi
    apply budgetProgram_frame cache node (cache.nodes.size + 1) (2 * (cache.nodes.size + 1)) (3 * (cache.nodes.size + 1)) budget
      (by omega) initial _ (by omega)
    intro j hj
    omega

theorem zeroTool_budget_correct_run (good bad : IndexedEntry.FixedEntry (IndexedTable.emptyCache (Fin 0)))
    (goodBase badBase output budget : Nat) (hgood : 0 < goodBase) (hbad : 0 < badBase) (hout : 0 < output)
    (initial : State) (hpc : initial.pc = 0)
    (hg : SlotRep (IndexedTable.emptyCache (Fin 0)) initial.heap goodBase good)
    (hb : SlotRep (IndexedTable.emptyCache (Fin 0)) initial.heap badBase bad) :
    let cache := IndexedTable.emptyCache (Fin 0)
    let result : IndexedEntry.FixedEntry cache := if budget = 0 then IndexedEntry.free cache else .void
    ∃ final operations,
      IndexedClosureRAM.HaltingRuns (cellROM cache none) (budgetProgram cache goodBase badBase output budget) initial final operations ∧
      slot cache final.heap output = result ∧ SlotRep cache final.heap output result ∧ operations.length ≤ 189 := by
  dsimp only
  have heq := zeroTool_budgetResult good bad goodBase badBase output budget hgood hbad hout initial hg hb
  unfold budgetResult at heq
  exact ⟨_, _, execute_halts _ _ initial hpc, heq,
    slotRep_of_decode (IndexedTable.emptyCache (Fin 0)) _ output _
      (budgetProgram_outputTag_le_one (IndexedTable.emptyCache (Fin 0)) none goodBase badBase output budget hgood hbad hout bad initial hb) heq,
    zeroTool_budgetProgram_trace_le goodBase badBase output budget⟩

end PaperProofs.Structure.LaminarTree.IndexedCellRAM
