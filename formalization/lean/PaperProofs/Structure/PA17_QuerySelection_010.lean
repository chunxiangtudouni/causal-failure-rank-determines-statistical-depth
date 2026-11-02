module

public import PaperProofs.Structure.PA17_LeafLabels_005

/-! Query selection: exact firstSlackChild pointers are built by scanning
NodeIds in reverse order and pushing every slack child to its actual ROM parent.
The last pushed child is the first in the original ascending child list.
This pass reads capacities/counts only, including arbitrary VOID payloads. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QuerySelection010

open IndexedRAM IndexedClosureRAM AlgorithmClaims

variable {Tool : Type*}

theorem children_eq_filtered [DecidableEq Tool] (nodes : Array (Finset Tool))
    (sourceParent : Finset Tool → Option (Finset Tool)) (parent : (indexNodes nodes sourceParent).NodeId) :
    ((indexNodes nodes sourceParent).children.get parent).toList =
      (List.finRange nodes.size).filter (fun child => decide ((indexNodes nodes sourceParent).parents.get child = some parent)) := by
  change Fin nodes.size at parent
  simp [indexNodes, cache_get_ofFn]

def Inputs (cache : IndexedNodeCache Tool) (counts capacity : IndexedCapacity cache)
    (countBase payloadPointer payloadBase : Nat) (heap : Nat → Nat) : Prop :=
  heap payloadPointer = payloadBase ∧
    ∀ node : cache.NodeId, heap (countBase + node.val) = counts.get node ∧ heap (payloadBase + node.val) = capacity.get node

def SourcesDisjoint (size countBase payloadPointer payloadBase childBase : Nat) : Prop :=
  (∀ encoded ≤ size, payloadPointer ≠ childBase + encoded) ∧
    ∀ node < size, ∀ encoded ≤ size,
      countBase + node ≠ childBase + encoded ∧ payloadBase + node ≠ childBase + encoded

def ParentROMFor (cache : IndexedNodeCache Tool) (rom : ROM) : Prop :=
  ∀ node : cache.NodeId, rom.read .internal node.val = encodedNode cache (cache.parents.get node)

def parentBlock (countBase payloadPointer childBase node : Nat) : List Op :=
  [.base (.constant .index (countBase + node)), .base (.loadHeap .old .index),
   .base (.constant .index payloadPointer), .base (.loadHeap .address .index),
   .base (.constant .fresh node), .base (.add .address .address .fresh), .base (.loadHeap .fresh .address),
   .subtract .flag .fresh .old,
   .base (.constant .index node), .base (.loadROM .internal .total .index),
   .base (.constant .index childBase), .base (.add .index .index .total), .base (.loadHeap .old .index),
   .base (.constant .fresh (node + 1)), .base (.select .value .flag .fresh .old),
   .base (.select .value .total .value .old), .base (.storeHeap .index .value)]

theorem parentBlock_heap (rom : ROM) (countBase payloadPointer childBase node : Nat) (state : State) :
    (execute rom (parentBlock countBase payloadPointer childBase node) state).heap =
      Function.update state.heap (childBase + rom.read .internal node)
        (if rom.read .internal node = 0 then state.heap (childBase + rom.read .internal node) else
          if state.heap (state.heap payloadPointer + node) - state.heap (countBase + node) = 0 then
            state.heap (childBase + rom.read .internal node) else node + 1) := rfl

theorem parentBlock_frame (rom : ROM) (countBase payloadPointer childBase node : Nat) (state : State)
    (address : Nat) (hne : address ≠ childBase + rom.read .internal node) :
    (execute rom (parentBlock countBase payloadPointer childBase node) state).heap address = state.heap address := by
  rw [parentBlock_heap, Function.update_of_ne hne]

theorem parentBlock_sentinel (rom : ROM) (countBase payloadPointer childBase node : Nat) (state : State) :
    (execute rom (parentBlock countBase payloadPointer childBase node) state).heap childBase = state.heap childBase := by
  rw [parentBlock_heap]
  by_cases hz : rom.read .internal node = 0
  · simp only [hz, Nat.add_zero, ite_true, Function.update_self]
  · rw [Function.update_of_ne (by omega)]

theorem parentBlock_inputs (cache : IndexedNodeCache Tool) (rom : ROM) (hrom : ParentROMFor cache rom)
    (counts capacity : IndexedCapacity cache) (countBase payloadPointer payloadBase childBase : Nat)
    (hdisjoint : SourcesDisjoint cache.nodes.size countBase payloadPointer payloadBase childBase)
    (node : cache.NodeId) (state : State) (hinputs : Inputs cache counts capacity countBase payloadPointer payloadBase state.heap) :
    Inputs cache counts capacity countBase payloadPointer payloadBase
      (execute rom (parentBlock countBase payloadPointer childBase node.val) state).heap := by
  have hp : rom.read .internal node.val ≤ cache.nodes.size :=
    (hrom node).trans_le (UniformNormalizationRAM.encodedNode_le cache _)
  constructor
  · rw [parentBlock_frame rom countBase payloadPointer childBase node.val state payloadPointer (hdisjoint.1 _ hp)]
    exact hinputs.1
  · intro other
    rw [parentBlock_frame rom countBase payloadPointer childBase node.val state (countBase + other.val)
      (hdisjoint.2 other.val other.isLt _ hp).1,
      parentBlock_frame rom countBase payloadPointer childBase node.val state (payloadBase + other.val)
        (hdisjoint.2 other.val other.isLt _ hp).2]
    exact hinputs.2 other

theorem parentBlock_candidate (cache : IndexedNodeCache Tool) (rom : ROM) (hrom : ParentROMFor cache rom)
    (counts capacity : IndexedCapacity cache) (countBase payloadPointer payloadBase childBase : Nat)
    (node parent : cache.NodeId) (state : State)
    (hinputs : Inputs cache counts capacity countBase payloadPointer payloadBase state.heap) :
    (execute rom (parentBlock countBase payloadPointer childBase node.val) state).heap (childBase + (parent.val + 1)) =
      if cache.parents.get node = some parent ∧ counts.get node < capacity.get node then node.val + 1
      else state.heap (childBase + (parent.val + 1)) := by
  rw [parentBlock_heap, hinputs.1, (hinputs.2 node).1, (hinputs.2 node).2, hrom node]
  cases hp : cache.parents.get node with
  | none =>
    change Function.update state.heap childBase (state.heap childBase) (childBase + (parent.val + 1)) =
      if (none : Option cache.NodeId) = some parent ∧ counts.get node < capacity.get node then node.val + 1
      else state.heap (childBase + (parent.val + 1))
    rw [Function.update_eq_self]
    exact (ite_eq_right (by rintro ⟨h, _⟩; cases h)).symm
  | some target =>
    by_cases heq : target = parent
    · subst target
      change Function.update state.heap (childBase + (parent.val + 1))
        (if parent.val + 1 = 0 then state.heap (childBase + (parent.val + 1)) else
          if capacity.get node - counts.get node = 0 then state.heap (childBase + (parent.val + 1)) else node.val + 1)
        (childBase + (parent.val + 1)) =
          if (some parent : Option cache.NodeId) = some parent ∧ counts.get node < capacity.get node then node.val + 1
          else state.heap (childBase + (parent.val + 1))
      simp only [Function.update_self, true_and]
      have hn : parent.val + 1 ≠ 0 := by omega
      rw [ite_eq_right hn]
      by_cases hlt : counts.get node < capacity.get node
      · rw [ite_eq_left hlt, ite_eq_right (by omega)]
      · rw [ite_eq_right hlt, ite_eq_left (by omega)]
    · have hnat : target.val ≠ parent.val := by intro he; exact heq (Fin.ext he)
      have haddr : childBase + (parent.val + 1) ≠ childBase + encodedNode cache (some target) := by
        change childBase + (parent.val + 1) ≠ childBase + (target.val + 1)
        omega
      rw [Function.update_of_ne haddr, ite_eq_right (by intro hh; exact heq (Option.some.inj hh.1))]

def pushList (countBase payloadPointer childBase : Nat) (nodes : List Nat) : List Op :=
  nodes.reverse.flatMap (parentBlock countBase payloadPointer childBase)

def program (size countBase payloadPointer childBase : Nat) : List Op :=
  UniformNormalizationRAM.clearWords childBase (size + 1) ++
    pushList countBase payloadPointer childBase (List.range size)

theorem pushList_inputs (cache : IndexedNodeCache Tool) (rom : ROM) (hrom : ParentROMFor cache rom)
    (counts capacity : IndexedCapacity cache) (countBase payloadPointer payloadBase childBase : Nat)
    (hdisjoint : SourcesDisjoint cache.nodes.size countBase payloadPointer payloadBase childBase)
    (nodes : List cache.NodeId) (state : State) (hinputs : Inputs cache counts capacity countBase payloadPointer payloadBase state.heap) :
    Inputs cache counts capacity countBase payloadPointer payloadBase
      (execute rom (pushList countBase payloadPointer childBase (nodes.map Fin.val)) state).heap := by
  induction nodes generalizing state with
  | nil => exact hinputs
  | cons node later ih =>
    rw [pushList, List.map_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, IndexedClosureRAM.execute_append]
    exact parentBlock_inputs cache rom hrom counts capacity countBase payloadPointer payloadBase childBase hdisjoint node _ (ih state hinputs)

theorem pushList_candidate (cache : IndexedNodeCache Tool) (rom : ROM) (hrom : ParentROMFor cache rom)
    (counts capacity : IndexedCapacity cache) (countBase payloadPointer payloadBase childBase : Nat)
    (hdisjoint : SourcesDisjoint cache.nodes.size countBase payloadPointer payloadBase childBase)
    (nodes : List cache.NodeId) (parent : cache.NodeId) (state : State)
    (hinputs : Inputs cache counts capacity countBase payloadPointer payloadBase state.heap) :
    (execute rom (pushList countBase payloadPointer childBase (nodes.map Fin.val)) state).heap (childBase + (parent.val + 1)) =
      match nodes.find? (fun child => decide (cache.parents.get child = some parent ∧ counts.get child < capacity.get child)) with
      | none => state.heap (childBase + (parent.val + 1))
      | some child => child.val + 1 := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    have hi := pushList_inputs cache rom hrom counts capacity countBase payloadPointer payloadBase childBase hdisjoint later state hinputs
    rw [pushList, List.map_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, IndexedClosureRAM.execute_append]
    change (execute rom (parentBlock countBase payloadPointer childBase node.val)
      (execute rom (pushList countBase payloadPointer childBase (later.map Fin.val)) state)).heap _ = _
    rw [parentBlock_candidate cache rom hrom counts capacity countBase payloadPointer payloadBase childBase node parent _ hi]
    change (if _ then _ else (execute rom (pushList countBase payloadPointer childBase (later.map Fin.val)) state).heap _) = _
    rw [ih state hinputs]
    by_cases hh : cache.parents.get node = some parent ∧ counts.get node < capacity.get node <;>
      simp [hh]

theorem finRange_map_val (size : Nat) : (List.finRange size).map Fin.val = List.range size := by
  apply List.ext_getElem
  · simp only [List.length_map, List.length_finRange, List.length_range]
  · intro index hi _
    simp only [List.getElem_map, List.getElem_finRange, List.getElem_range, Fin.val_cast]

theorem clearWords_inputs (cache : IndexedNodeCache Tool) (rom : ROM)
    (counts capacity : IndexedCapacity cache) (countBase payloadPointer payloadBase childBase : Nat)
    (hdisjoint : SourcesDisjoint cache.nodes.size countBase payloadPointer payloadBase childBase)
    (state : State) (hinputs : Inputs cache counts capacity countBase payloadPointer payloadBase state.heap) :
    Inputs cache counts capacity countBase payloadPointer payloadBase
      (execute rom (UniformNormalizationRAM.clearWords childBase (cache.nodes.size + 1)) state).heap := by
  have hf (address : Nat) (ha : ∀ encoded ≤ cache.nodes.size, address ≠ childBase + encoded) :
      (execute rom (UniformNormalizationRAM.clearWords childBase (cache.nodes.size + 1)) state).heap address = state.heap address := by
    apply UniformNormalizationRAM.clearIndices_frame
    intro index hi
    exact ha index (by have := List.mem_range.mp hi; omega)
  constructor
  · rw [hf payloadPointer hdisjoint.1]
    exact hinputs.1
  · intro node
    rw [hf (countBase + node.val) (fun encoded he => (hdisjoint.2 node.val node.isLt encoded he).1),
      hf (payloadBase + node.val) (fun encoded he => (hdisjoint.2 node.val node.isLt encoded he).2)]
    exact hinputs.2 node

theorem pushList_frame (cache : IndexedNodeCache Tool) (rom : ROM) (hrom : ParentROMFor cache rom)
    (countBase payloadPointer childBase : Nat) (nodes : List cache.NodeId) (state : State) (address : Nat)
    (hframe : ∀ encoded ≤ cache.nodes.size, address ≠ childBase + encoded) :
    (execute rom (pushList countBase payloadPointer childBase (nodes.map Fin.val)) state).heap address = state.heap address := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    rw [pushList, List.map_cons, List.reverse_cons, List.flatMap_append, List.flatMap_cons,
      List.flatMap_nil, List.append_nil, IndexedClosureRAM.execute_append,
      parentBlock_frame rom countBase payloadPointer childBase node.val _ address
        (hframe _ ((hrom node).trans_le (UniformNormalizationRAM.encodedNode_le cache _)))]
    exact ih state

theorem pushList_sentinel (rom : ROM) (countBase payloadPointer childBase : Nat) (nodes : List Nat) (state : State) :
    (execute rom (pushList countBase payloadPointer childBase nodes) state).heap childBase = state.heap childBase := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    rw [pushList, List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, IndexedClosureRAM.execute_append, parentBlock_sentinel]
    exact ih state

theorem program_sentinel (rom : ROM) (size countBase payloadPointer childBase : Nat) (state : State) :
    (execute rom (program size countBase payloadPointer childBase) state).heap childBase = 0 := by
  rw [program, IndexedClosureRAM.execute_append, pushList_sentinel]
  have hh := UniformNormalizationRAM.clearIndices_value rom childBase (List.range (size + 1)) state 0
    (List.mem_range.mpr (by omega))
  simpa only [Nat.add_zero, UniformNormalizationRAM.clearWords] using hh

theorem program_candidate {q : Nat} (cache : IndexedNodeCache (Fin q)) (rom : ROM) (hrom : ParentROMFor cache rom)
    (hchildren : ∀ parent : cache.NodeId, (cache.children.get parent).toList =
      (List.finRange cache.nodes.size).filter (fun child => decide (cache.parents.get child = some parent)))
    (counts capacity : IndexedCapacity cache) (countBase payloadPointer payloadBase childBase : Nat)
    (hdisjoint : SourcesDisjoint cache.nodes.size countBase payloadPointer payloadBase childBase)
    (state : State) (hinputs : Inputs cache counts capacity countBase payloadPointer payloadBase state.heap)
    (parent : cache.NodeId) :
    (execute rom (program cache.nodes.size countBase payloadPointer childBase) state).heap (childBase + (parent.val + 1)) =
      encodedNode cache (IndexedDescent.firstSlackChild cache counts capacity parent) := by
  let cleared := execute rom (UniformNormalizationRAM.clearWords childBase (cache.nodes.size + 1)) state
  have hi := clearWords_inputs cache rom counts capacity countBase payloadPointer payloadBase childBase hdisjoint state hinputs
  have hp := pushList_candidate cache rom hrom counts capacity countBase payloadPointer payloadBase childBase hdisjoint
    (List.finRange cache.nodes.size) parent cleared hi
  rw [finRange_map_val] at hp
  have hz : cleared.heap (childBase + (parent.val + 1)) = 0 :=
    UniformNormalizationRAM.clearIndices_value rom childBase (List.range (cache.nodes.size + 1)) state (parent.val + 1)
      (List.mem_range.mpr (by have := parent.isLt; omega))
  rw [hz] at hp
  rw [program, IndexedClosureRAM.execute_append]
  rw [IndexedDescent.firstSlackChild, hchildren parent, List.find?_filter]
  convert hp using 1
  simp only [decide_eq_true_eq, encodedNode]
  congr 2

theorem prepared_program_candidate (q : Nat) (full : List (Finset (Fin q))) (queryStage : Nat) (used : Finset (Fin q))
    (counts capacity : IndexedCapacity (prepareNormalization q full).indexed)
    (countBase payloadPointer payloadBase childBase : Nat)
    (hdisjoint : SourcesDisjoint (prepareNormalization q full).indexed.nodes.size countBase payloadPointer payloadBase childBase)
    (state : State) (hinputs : Inputs (prepareNormalization q full).indexed counts capacity countBase payloadPointer payloadBase state.heap)
    (parent : (prepareNormalization q full).indexed.NodeId) :
    let cache := (prepareNormalization q full).indexed
    (execute (queryROM q full queryStage used).semantic (program cache.nodes.size countBase payloadPointer childBase) state).heap
      (childBase + (parent.val + 1)) = encodedNode cache (IndexedDescent.firstSlackChild cache counts capacity parent) := by
  apply program_candidate _ _ _ _ counts capacity countBase payloadPointer payloadBase childBase hdisjoint state hinputs parent
  · intro node
    exact UniformNormalizationRAM.givenTreeROM_parent q full node
  · intro node
    exact children_eq_filtered (prepareNormalization q full).order.toArray (prepareNormalization q full).parentSupport node

theorem program_inputs (cache : IndexedNodeCache Tool) (rom : ROM) (hrom : ParentROMFor cache rom)
    (counts capacity : IndexedCapacity cache) (countBase payloadPointer payloadBase childBase : Nat)
    (hdisjoint : SourcesDisjoint cache.nodes.size countBase payloadPointer payloadBase childBase)
    (state : State) (hinputs : Inputs cache counts capacity countBase payloadPointer payloadBase state.heap) :
    Inputs cache counts capacity countBase payloadPointer payloadBase
      (execute rom (program cache.nodes.size countBase payloadPointer childBase) state).heap := by
  have hp := pushList_inputs cache rom hrom counts capacity countBase payloadPointer payloadBase childBase hdisjoint
    (List.finRange cache.nodes.size) _
    (clearWords_inputs cache rom counts capacity countBase payloadPointer payloadBase childBase hdisjoint state hinputs)
  rw [finRange_map_val] at hp
  rw [program, IndexedClosureRAM.execute_append]
  exact hp

theorem program_frame (cache : IndexedNodeCache Tool) (rom : ROM) (hrom : ParentROMFor cache rom)
    (countBase payloadPointer childBase : Nat) (state : State) (address : Nat)
    (hframe : ∀ encoded ≤ cache.nodes.size, address ≠ childBase + encoded) :
    (execute rom (program cache.nodes.size countBase payloadPointer childBase) state).heap address = state.heap address := by
  have hp := pushList_frame cache rom hrom countBase payloadPointer childBase (List.finRange cache.nodes.size)
    (execute rom (UniformNormalizationRAM.clearWords childBase (cache.nodes.size + 1)) state) address hframe
  rw [finRange_map_val] at hp
  rw [program, IndexedClosureRAM.execute_append, hp]
  apply UniformNormalizationRAM.clearIndices_frame
  intro index hi
  exact hframe index (by have := List.mem_range.mp hi; omega)

theorem parentBlock_length (countBase payloadPointer childBase node : Nat) :
    (parentBlock countBase payloadPointer childBase node).length = 17 := rfl

set_option maxRecDepth 10000 in
theorem parentBlock_trace_length (countBase payloadPointer childBase node : Nat) :
    (trace (parentBlock countBase payloadPointer childBase node)).length = 171 := rfl

theorem program_trace_length (size countBase payloadPointer childBase : Nat) :
    (trace (program size countBase payloadPointer childBase)).length = 198 * size + 27 := by
  have hc (address : Nat) : (trace (UniformNormalizationRAM.clearBlock address)).length = 27 := rfl
  rw [program, trace_append, List.length_append, UniformNormalizationRAM.clearWords,
    UniformNormalizationRAM.trace_flatMap_length, pushList, UniformNormalizationRAM.trace_flatMap_length]
  simp only [hc, parentBlock_trace_length, List.map_const', List.sum_replicate,
    List.length_range, List.length_reverse, Nat.nsmul_eq_mul]
  omega

end PaperProofs.Structure.LaminarTree.PA17QuerySelection010
