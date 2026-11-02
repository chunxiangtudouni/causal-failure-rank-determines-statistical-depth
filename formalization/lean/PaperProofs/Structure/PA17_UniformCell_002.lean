module

public import PaperProofs.Structure.PA17_HeapAncestors_001
public import PaperProofs.Structure.PA17_TagBridge_001

/-! Dimension-only intersection after the heap-parent extension. The good
input stays tag-first in the persistent table; the work slot is tag-last.
The same given-tree ROM is used throughout. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17UniformCell002

open IndexedRAM IndexedClosureRAM AlgorithmClaims
open PA17TagBridge001

variable {Tool : Type*}

def minimumBlock (workBase goodBase node : Nat) : List Op :=
  [.base (.constant .index (workBase + node)), .base (.loadHeap .old .index),
   .base (.constant .address (goodBase + 1 + node)), .base (.loadHeap .fresh .address),
   .base (.minimum .value .old .fresh), .base (.storeHeap .index .value)]

def minimumPass (size workBase goodBase : Nat) : List Op :=
  (List.range size).flatMap (minimumBlock workBase goodBase)

theorem minimumBlock_heap (rom : ROM) (workBase goodBase node : Nat) (state : State) :
    (execute rom (minimumBlock workBase goodBase node) state).heap =
      Function.update state.heap (workBase + node)
        (min (state.heap (workBase + node)) (state.heap (goodBase + 1 + node))) := rfl

theorem minimumBlocks_frame (rom : ROM) (workBase goodBase : Nat) (nodes : List Nat)
    (state : State) (address : Nat) (hframe : ∀ node ∈ nodes, address ≠ workBase + node) :
    (execute rom (nodes.flatMap (minimumBlock workBase goodBase)) state).heap address = state.heap address := by
  induction nodes generalizing state with
  | nil => rfl
  | cons node later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append,
      ih _ (fun other ho => hframe other (List.mem_cons_of_mem _ ho)), minimumBlock_heap,
      Function.update_of_ne (hframe node List.mem_cons_self)]

theorem minimumBlocks_value (rom : ROM) (size workBase goodBase : Nat)
    (hdisjoint : DisjointSlots size workBase goodBase) (nodes : List Nat)
    (hbound : ∀ node ∈ nodes, node < size) (hnodup : nodes.Nodup)
    (state : State) (node : Nat) (hnode : node ∈ nodes) :
    (execute rom (nodes.flatMap (minimumBlock workBase goodBase)) state).heap (workBase + node) =
      min (state.heap (workBase + node)) (state.heap (goodBase + 1 + node)) := by
  induction nodes generalizing state with
  | nil => cases hnode
  | cons head later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    rcases List.mem_cons.mp hnode with heq | htail
    · subst node
      rw [minimumBlocks_frame rom workBase goodBase later _ _ (by
        intro other ho hh
        exact (List.nodup_cons.mp hnodup).1 ((Nat.add_left_cancel hh) ▸ ho)),
        minimumBlock_heap, Function.update_self]
    · rw [ih (fun other ho => hbound other (List.mem_cons_of_mem _ ho)) (List.nodup_cons.mp hnodup).2 _ htail,
        minimumBlock_heap]
      have hne : workBase + node ≠ workBase + head := by
        intro hh
        exact (List.nodup_cons.mp hnodup).1 ((Nat.add_left_cancel hh) ▸ htail)
      have hg : goodBase + 1 + node ≠ workBase + head := by
        simpa only [Nat.add_assoc] using
          (hdisjoint head (by have := hbound head List.mem_cons_self; omega)
            (1 + node) (by have := hbound node (List.mem_cons_of_mem _ htail); omega)).symm
      rw [Function.update_of_ne hne, Function.update_of_ne hg]

theorem minimumPass_frame (rom : ROM) (size workBase goodBase : Nat) (state : State)
    (address : Nat) (hframe : ∀ node < size, address ≠ workBase + node) :
    (execute rom (minimumPass size workBase goodBase) state).heap address = state.heap address :=
  minimumBlocks_frame rom workBase goodBase (List.range size) state address
    (fun node hn => hframe node (List.mem_range.mp hn))

def minimumCapacity (cache : IndexedNodeCache Tool) (workBase goodBase : Nat) (heap : Nat → Nat) :
    IndexedCapacity cache :=
  Vector.ofFn (fun node => min (heap (workBase + node.val)) (heap (goodBase + 1 + node.val)))

theorem minimumPass_payload (cache : IndexedNodeCache Tool) (rom : ROM) (workBase goodBase : Nat)
    (hdisjoint : DisjointSlots cache.nodes.size workBase goodBase) (state : State) (node : cache.NodeId) :
    (execute rom (minimumPass cache.nodes.size workBase goodBase) state).heap (workBase + node.val) =
      (minimumCapacity cache workBase goodBase state.heap).get node := by
  rw [minimumCapacity, cache_get_ofFn]
  exact minimumBlocks_value rom cache.nodes.size workBase goodBase hdisjoint (List.range cache.nodes.size)
    (fun _ hn => List.mem_range.mp hn) List.nodup_range state node.val (List.mem_range.mpr node.isLt)

def tagTail (size workBase goodBase : Nat) : List Op :=
  [.base (.constant .index goodBase), .base (.loadHeap .old .index),
   .base (.constant .index (workBase + size)), .base (.loadHeap .fresh .index),
   .base (.minimum .value .old .fresh), .base (.storeHeap .index .value)]

theorem tagTail_heap (rom : ROM) (size workBase goodBase : Nat) (state : State) :
    (execute rom (tagTail size workBase goodBase) state).heap =
      Function.update state.heap (workBase + size)
        (min (state.heap goodBase) (state.heap (workBase + size))) := rfl

def intersectionProgram (size workBase goodBase accumulatorBase : Nat) : List Op :=
  minimumPass size workBase goodBase ++
    UniformNormalizationRAM.program size workBase accumulatorBase ++ tagTail size workBase goodBase

theorem prepared_intersectionProgram_tag (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (workBase goodBase accumulatorBase : Nat)
    (hgood : DisjointSlots (prepareNormalization q full).indexed.nodes.size workBase goodBase)
    (hwork : DisjointSlots (prepareNormalization q full).indexed.nodes.size workBase accumulatorBase)
    (hacc : DisjointSlots (prepareNormalization q full).indexed.nodes.size goodBase accumulatorBase)
    (state : State) :
    let size := (prepareNormalization q full).indexed.nodes.size
    (execute (givenTreeROM q full).semantic
      (intersectionProgram size workBase goodBase accumulatorBase) state).heap (workBase + size) =
      min (state.heap goodBase) (state.heap (workBase + size)) := by
  intro size
  rw [intersectionProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    tagTail_heap, Function.update_self]
  rw [UniformNormalizationRAM.program_frame _ _ (UniformNormalizationRAM.givenTreeROM_tree q full hq hlaminar)
    workBase accumulatorBase _ goodBase
    (by intro node hn; exact (hgood node (by omega) 0 (Nat.zero_le _)).symm)
    (by intro slot hs; exact hacc 0 (Nat.zero_le _) slot hs),
    UniformNormalizationRAM.program_frame _ _ (UniformNormalizationRAM.givenTreeROM_tree q full hq hlaminar)
      workBase accumulatorBase _ (workBase + size)
      (by intro node hn; omega) (by intro slot hs; exact hwork size le_rfl slot hs),
    minimumPass_frame _ _ _ _ state goodBase
      (by intro node hn; exact (hgood node (by omega) 0 (Nat.zero_le _)).symm),
    minimumPass_frame _ _ _ _ state (workBase + size) (by intro node hn; omega)]

theorem prepared_intersectionProgram_payload (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (workBase goodBase accumulatorBase : Nat)
    (hgood : DisjointSlots (prepareNormalization q full).indexed.nodes.size workBase goodBase)
    (hwork : DisjointSlots (prepareNormalization q full).indexed.nodes.size workBase accumulatorBase)
    (state : State) :
    let cache := (prepareNormalization q full).indexed
    ∀ node : cache.NodeId,
    (execute (givenTreeROM q full).semantic
      (intersectionProgram cache.nodes.size workBase goodBase accumulatorBase) state).heap (workBase + node.val) =
      (cache.normalize (minimumCapacity cache workBase goodBase state.heap)).get node := by
  intro cache node
  rw [intersectionProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    tagTail_heap, Function.update_of_ne (by have := node.isLt; omega)]
  exact (UniformNormalizationRAM.prepared_program_represents q full hq hlaminar workBase accumulatorBase
    (fun index hi slot hs => hwork index (by omega) slot hs) _ _
    (minimumPass_payload cache _ workBase goodBase hgood state)).1 node

theorem prepared_intersectionProgram_result (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (workBase goodBase accumulatorBase : Nat)
    (hgood : DisjointSlots (prepareNormalization q full).indexed.nodes.size workBase goodBase)
    (hwork : DisjointSlots (prepareNormalization q full).indexed.nodes.size workBase accumulatorBase)
    (hacc : DisjointSlots (prepareNormalization q full).indexed.nodes.size goodBase accumulatorBase)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (state : State)
    (hg : TagFirstRep (prepareNormalization q full).indexed state.heap goodBase good)
    (hb : IndexedCellRAM.SlotRep (prepareNormalization q full).indexed state.heap workBase bad) :
    let cache := (prepareNormalization q full).indexed
    IndexedCellRAM.SlotRep cache (execute (givenTreeROM q full).semantic
      (intersectionProgram cache.nodes.size workBase goodBase accumulatorBase) state).heap workBase
      (IndexedEntry.intersect cache good bad) := by
  intro cache
  have ht := prepared_intersectionProgram_tag q full hq hlaminar workBase goodBase accumulatorBase hgood hwork hacc state
  have hp := prepared_intersectionProgram_payload q full hq hlaminar workBase goodBase accumulatorBase hgood hwork state
  cases good with
  | void =>
    change _ = 0
    rw [ht, hg, Nat.zero_min]
  | vector left =>
    cases bad with
    | void =>
      change _ = 0
      rw [ht, hb, Nat.min_zero]
    | vector right =>
      constructor
      · rw [ht, hg.1, hb.1, Nat.min_self]
      · intro node
        rw [hp node]
        have heq : minimumCapacity cache workBase goodBase state.heap =
            Vector.ofFn (fun target => min (left.get target) (right.get target)) := by
          apply Vector.ext
          intro index hi
          change (Vector.ofFn _).get ⟨index, hi⟩ = (Vector.ofFn _).get ⟨index, hi⟩
          rw [cache_get_ofFn, cache_get_ofFn, hg.2 ⟨index, hi⟩, hb.2 ⟨index, hi⟩, Nat.min_comm]
        rw [heq]

theorem prepared_intersectionProgram_frame (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (workBase goodBase accumulatorBase : Nat)
    (state : State) (address : Nat)
    (hwork : ∀ index ≤ (prepareNormalization q full).indexed.nodes.size, address ≠ workBase + index)
    (hacc : ∀ index ≤ (prepareNormalization q full).indexed.nodes.size, address ≠ accumulatorBase + index) :
    (execute (givenTreeROM q full).semantic
      (intersectionProgram (prepareNormalization q full).indexed.nodes.size workBase goodBase accumulatorBase) state).heap address =
      state.heap address := by
  rw [intersectionProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
    tagTail_heap, Function.update_of_ne (hwork _ le_rfl),
    UniformNormalizationRAM.program_frame _ _ (UniformNormalizationRAM.givenTreeROM_tree q full hq hlaminar)
      workBase accumulatorBase _ address (by intro node hn; exact hwork node (by omega)) hacc,
    minimumPass_frame _ _ _ _ state address (by intro node hn; exact hwork node (by omega))]

theorem minimumPass_length (size workBase goodBase : Nat) :
    (minimumPass size workBase goodBase).length = 6 * size := by
  have hl (node : Nat) : (minimumBlock workBase goodBase node).length = 6 := rfl
  simp only [minimumPass, List.length_flatMap, hl, List.map_const', List.sum_replicate,
    List.length_range, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem minimumPass_trace_length (size workBase goodBase : Nat) :
    (trace (minimumPass size workBase goodBase)).length = 60 * size := by
  have hl (node : Nat) : (trace (minimumBlock workBase goodBase node)).length = 60 := rfl
  rw [minimumPass, UniformNormalizationRAM.trace_flatMap_length]
  simp only [hl, List.map_const', List.sum_replicate, List.length_range, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem intersectionProgram_length (size workBase goodBase accumulatorBase : Nat) :
    (intersectionProgram size workBase goodBase accumulatorBase).length = 25 * size + 9 := by
  rw [intersectionProgram, List.length_append, List.length_append, minimumPass_length,
    UniformNormalizationRAM.program_length]
  have ht : (tagTail size workBase goodBase).length = 6 := rfl
  rw [ht]
  omega

theorem intersectionProgram_trace_length (size workBase goodBase accumulatorBase : Nat) :
    (trace (intersectionProgram size workBase goodBase accumulatorBase)).length = 249 * size + 87 := by
  rw [intersectionProgram, IndexedClosureRAM.trace_append, IndexedClosureRAM.trace_append,
    List.length_append, List.length_append, minimumPass_trace_length, UniformNormalizationRAM.program_trace_length]
  have ht : (trace (tagTail size workBase goodBase)).length = 60 := rfl
  rw [ht]
  omega

def kernelProgram (size workBase goodBase accumulatorBase parentBase stageAddress : Nat) : List Op :=
  PA17HeapAncestors001.extensionProgram size workBase parentBase stageAddress ++
    intersectionProgram size workBase goodBase accumulatorBase

theorem prepared_kernelProgram_result (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (workBase goodBase accumulatorBase metadataBase stageAddress : Nat)
    (hgood : DisjointSlots (prepareNormalization q full).indexed.nodes.size workBase goodBase)
    (hwork : DisjointSlots (prepareNormalization q full).indexed.nodes.size workBase accumulatorBase)
    (hacc : DisjointSlots (prepareNormalization q full).indexed.nodes.size goodBase accumulatorBase)
    (hparent : ∀ index < (prepareNormalization q full).indexed.nodes.size,
      ∀ encoded ≤ (prepareNormalization q full).indexed.nodes.size,
      workBase + index ≠ metadataBase + (prepareNormalization q full).indexed.nodes.size + encoded)
    (stage : Fin full.length) (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (state : State) (hmetadata : UniformTreeMetadataRAM.MetadataCorrect q full metadataBase state.heap)
    (hstage : state.heap stageAddress = encodedNode (prepareNormalization q full).indexed
      (IndexedQuery.storedStageNode q full hq stage))
    (hg : TagFirstRep (prepareNormalization q full).indexed state.heap goodBase good)
    (hb : IndexedCellRAM.SlotRep (prepareNormalization q full).indexed state.heap workBase bad) :
    let cache := (prepareNormalization q full).indexed
    IndexedCellRAM.SlotRep cache (execute (givenTreeROM q full).semantic
      (kernelProgram cache.nodes.size workBase goodBase accumulatorBase (metadataBase + cache.nodes.size) stageAddress) state).heap
      workBase (IndexedEntry.cell cache full[stage.val] good bad) := by
  intro cache
  let rom := (givenTreeROM q full).semantic
  let extension := PA17HeapAncestors001.extensionProgram cache.nodes.size workBase
    (metadataBase + cache.nodes.size) stageAddress
  let middle := execute rom extension state
  have hsize : 0 < cache.nodes.size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have he := PA17HeapAncestors001.prepared_extensionProgram_result q full hq hlaminar
    workBase metadataBase stageAddress hparent stage bad state hmetadata hstage hb
  have htag : state.heap (workBase + cache.nodes.size) ≤ 1 := by
    cases bad with
    | void => rw [hb]; exact Nat.zero_le _
    | vector capacity => rw [hb.1]
  have ht := PA17HeapAncestors001.extensionProgram_outputTag_le_one cache rom workBase
    (metadataBase + cache.nodes.size) stageAddress hsize hparent _ state
    (PA17HeapAncestors001.metadata_parentHeapFor q full metadataBase state.heap hmetadata) hstage htag
  have hb' : IndexedCellRAM.SlotRep cache middle.heap workBase (IndexedEntry.extend cache full[stage.val] bad) :=
    IndexedCellRAM.slotRep_of_decode cache middle.heap workBase _ ht he
  have hframe (address : Nat) (ha : ∀ index ≤ cache.nodes.size, address ≠ workBase + index) :
      middle.heap address = state.heap address :=
    PA17HeapAncestors001.extensionProgram_frame cache rom workBase (metadataBase + cache.nodes.size)
      stageAddress hsize hparent _ state
      (PA17HeapAncestors001.metadata_parentHeapFor q full metadataBase state.heap hmetadata) hstage address ha
  have hg' : TagFirstRep cache middle.heap goodBase good := by
    cases good with
    | void =>
      change middle.heap goodBase = 0
      rw [hframe goodBase (by intro index hi; exact (hgood index hi 0 (Nat.zero_le _)).symm)]
      exact hg
    | vector capacity =>
      constructor
      · rw [hframe goodBase (by intro index hi; exact (hgood index hi 0 (Nat.zero_le _)).symm)]
        exact hg.1
      · intro node
        rw [hframe (goodBase + 1 + node.val) (by
          intro index hi
          simpa only [Nat.add_assoc] using (hgood index hi (1 + node.val)
            (by change 1 + node.val ≤ cache.nodes.size; have := node.isLt; omega)).symm)]
        exact hg.2 node
  rw [kernelProgram, IndexedClosureRAM.execute_append]
  exact prepared_intersectionProgram_result q full hq hlaminar workBase goodBase accumulatorBase
    hgood hwork hacc good _ middle hg' hb'

theorem prepared_kernelProgram_frame (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (workBase goodBase accumulatorBase metadataBase stageAddress : Nat)
    (hparent : ∀ index < (prepareNormalization q full).indexed.nodes.size,
      ∀ encoded ≤ (prepareNormalization q full).indexed.nodes.size,
      workBase + index ≠ metadataBase + (prepareNormalization q full).indexed.nodes.size + encoded)
    (stage : Fin full.length) (state : State)
    (hmetadata : UniformTreeMetadataRAM.MetadataCorrect q full metadataBase state.heap)
    (hstage : state.heap stageAddress = encodedNode (prepareNormalization q full).indexed
      (IndexedQuery.storedStageNode q full hq stage))
    (address : Nat)
    (hwork : ∀ index ≤ (prepareNormalization q full).indexed.nodes.size, address ≠ workBase + index)
    (hacc : ∀ index ≤ (prepareNormalization q full).indexed.nodes.size, address ≠ accumulatorBase + index) :
    (execute (givenTreeROM q full).semantic
      (kernelProgram (prepareNormalization q full).indexed.nodes.size workBase goodBase accumulatorBase
        (metadataBase + (prepareNormalization q full).indexed.nodes.size) stageAddress) state).heap address = state.heap address := by
  let cache := (prepareNormalization q full).indexed
  have hsize : 0 < cache.nodes.size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  rw [kernelProgram, IndexedClosureRAM.execute_append,
    prepared_intersectionProgram_frame q full hq hlaminar workBase goodBase accumulatorBase _ address hwork hacc]
  exact PA17HeapAncestors001.extensionProgram_frame cache _ workBase (metadataBase + cache.nodes.size)
    stageAddress hsize hparent _ state
    (PA17HeapAncestors001.metadata_parentHeapFor q full metadataBase state.heap hmetadata) hstage address hwork

theorem kernelProgram_length (size workBase goodBase accumulatorBase parentBase stageAddress : Nat) :
    (kernelProgram size workBase goodBase accumulatorBase parentBase stageAddress).length = 38 * size + 18 := by
  rw [kernelProgram, List.length_append, PA17HeapAncestors001.extensionProgram_length, intersectionProgram_length]
  omega

theorem kernelProgram_trace_length (size workBase goodBase accumulatorBase parentBase stageAddress : Nat) :
    (trace (kernelProgram size workBase goodBase accumulatorBase parentBase stageAddress)).length = 386 * size + 172 := by
  rw [kernelProgram, IndexedClosureRAM.trace_append, List.length_append,
    PA17HeapAncestors001.extensionProgram_trace_length, intersectionProgram_trace_length]
  omega

theorem kernelProgram_halting (rom : ROM) (size workBase goodBase accumulatorBase parentBase stageAddress : Nat)
    (hsize : 0 < size) (state : State) (hpc : state.pc = 0) :
    HaltingRuns rom (kernelProgram size workBase goodBase accumulatorBase parentBase stageAddress) state
      (execute rom (kernelProgram size workBase goodBase accumulatorBase parentBase stageAddress) state)
      (trace (kernelProgram size workBase goodBase accumulatorBase parentBase stageAddress) ++ haltTrace) ∧
    (trace (kernelProgram size workBase goodBase accumulatorBase parentBase stageAddress) ++ haltTrace).length ≤ 564 * size := by
  refine ⟨IndexedClosureRAM.execute_halts _ _ _ hpc, ?_⟩
  rw [List.length_append, kernelProgram_trace_length, haltTrace_length]
  omega

theorem kernelProgram_codeWords_length (size workBase goodBase accumulatorBase parentBase stageAddress : Nat) :
    (haltingWords (kernelProgram size workBase goodBase accumulatorBase parentBase stageAddress)).length = 190 * size + 95 := by
  rw [haltingWords_length, kernelProgram_length]
  omega

end PaperProofs.Structure.LaminarTree.PA17UniformCell002
