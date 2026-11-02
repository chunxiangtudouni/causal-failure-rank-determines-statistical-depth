module

public import PaperProofs.Structure.PA17_TableCell_004
public import PaperProofs.Structure.PA17_NormalizationSafety_004
import Mathlib.Tactic.IntervalCases

/-! The actual complete persistent-table cell preserves the leading
capacity bound at every Op prefix, and bounds every output payload by its
node cardinality even when the output is VOID. Physical good-slot payload
bounds are independent premises: a VOID tag does not bound its payload. -/

@[expose] public section

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17CellSafety006

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001
  PA17UniformCell002

theorem minimumBlock_heap_le (rom : ROM) (work good node : Nat) (state : State) (address : Nat) :
    (execute rom (minimumBlock work good node) state).heap address ≤ state.heap address := by
  rw [minimumBlock_heap]
  by_cases he : address = work + node
  · rw [he, Function.update_self]
    exact Nat.min_le_left _ _
  · rw [Function.update_of_ne he]

theorem minimumBlock_capacityThroughout (q words work good node : Nat) (rom : PhysicalROM)
    (state : State) (hbound : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (minimumBlock work good node) state := by
  intro count hc
  change count ≤ 6 at hc
  have hfull : CapacityPrefixBounded q words (execute rom.semantic (minimumBlock work good node) state).heap :=
    fun address ha => (minimumBlock_heap_le rom.semantic work good node state address).trans (hbound address ha)
  interval_cases count <;> first | exact hbound | exact hfull

theorem minimumBlocks_capacityThroughout (q words work good : Nat) (rom : PhysicalROM)
    (nodes : List Nat) (state : State) (hbound : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (nodes.flatMap (minimumBlock work good)) state := by
  induction nodes generalizing state with
  | nil => intro count hc; simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hbound
  | cons head later ih =>
    rw [List.flatMap_cons]
    have hh := minimumBlock_capacityThroughout q words work good head rom state hbound
    apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hh
    apply ih
    simpa only [List.take_length] using hh _ le_rfl

theorem tagTail_heap_le (rom : ROM) (size work good : Nat) (state : State) (address : Nat) :
    (execute rom (tagTail size work good) state).heap address ≤ state.heap address := by
  rw [tagTail_heap]
  by_cases he : address = work + size
  · rw [he, Function.update_self]
    exact Nat.min_le_right _ _
  · rw [Function.update_of_ne he]

theorem tagTail_capacityThroughout (q words size work good : Nat) (rom : PhysicalROM)
    (state : State) (hbound : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (tagTail size work good) state := by
  intro count hc
  change count ≤ 6 at hc
  have hfull : CapacityPrefixBounded q words (execute rom.semantic (tagTail size work good) state).heap :=
    fun address ha => (tagTail_heap_le rom.semantic size work good state address).trans (hbound address ha)
  interval_cases count <;> first | exact hbound | exact hfull

theorem minimumCapacity_le_card (q : Nat) (full : List (Finset (Fin q))) (work good : Nat)
    (heap : Nat → Nat)
    (hgood : ∀ node : (prepareNormalization q full).indexed.NodeId,
      heap (good + 1 + node.val) ≤ ((prepareNormalization q full).indexed.decode node).card)
    (node : (prepareNormalization q full).indexed.NodeId) :
    (minimumCapacity (prepareNormalization q full).indexed work good heap).get node ≤
      ((prepareNormalization q full).indexed.decode node).card := by
  rw [minimumCapacity, cache_get_ofFn]
  exact (Nat.min_le_right _ _).trans (hgood node)

theorem prepared_intersection_safe (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (words work good acc : Nat)
    (hgood : DisjointSlots (prepareNormalization q full).indexed.nodes.size work good)
    (hwork : DisjointSlots (prepareNormalization q full).indexed.nodes.size work acc)
    (state : State) (hbound : CapacityPrefixBounded q words state.heap)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      state.heap (good + 1 + node.val) ≤ ((prepareNormalization q full).indexed.decode node).card) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (givenTreeROM q full).semantic
      (intersectionProgram cache.nodes.size work good acc) state
    CapacityThroughout q words (givenTreeROM q full)
      (intersectionProgram cache.nodes.size work good acc) state ∧
      ∀ node : cache.NodeId, result.heap (work + node.val) ≤ (cache.decode node).card := by
  intro cache result
  let rom := givenTreeROM q full
  let capacity := minimumCapacity cache work good state.heap
  let middle := execute rom.semantic (minimumPass cache.nodes.size work good) state
  have hc : ∀ node : cache.NodeId, capacity.get node ≤ (cache.decode node).card :=
    minimumCapacity_le_card q full work good state.heap hcard
  have hm := minimumBlocks_capacityThroughout q words work good rom (List.range cache.nodes.size) state hbound
  have hn := PA17NormalizationSafety004.prepared_program_capacityThroughout q full hq hlaminar
    words work acc (fun node hn slot hs => hwork node (by omega) slot hs) capacity hc middle
    (by simpa only [List.take_length, middle, minimumPass] using hm _ le_rfl)
    (minimumPass_payload cache rom.semantic work good hgood state)
  constructor
  · rw [intersectionProgram]
    apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state
      (UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hm hn)
    apply tagTail_capacityThroughout
    rw [IndexedClosureRAM.execute_append]
    simpa only [List.take_length, middle, minimumPass] using hn _ le_rfl
  · intro node
    rw [prepared_intersectionProgram_payload q full hq hlaminar work good acc hgood hwork state node]
    exact (indexed_normalizeAlong_le cache (List.finRange cache.nodes.size) capacity node).trans (hc node)

theorem prepared_kernel_safe (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (goodSlot : Nat)
    (hgoodSlot : goodSlot < cells full.length q) (stage : Fin full.length)
    (bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (state : State)
    (hp : PA17TableCell004.Persistent q full hq state.heap)
    (hb : IndexedCellRAM.SlotRep (prepareNormalization q full).indexed state.heap
      (PA17CellLayout003.workBase full.length q (prepareNormalization q full).indexed.nodes.size) bad)
    (hbound : CapacityPrefixBounded q
      (PA17CellLayout003.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      state.heap (PA17TableCell004.tableBase (prepareNormalization q full).indexed.nodes.size goodSlot + 1 + node.val) ≤
        ((prepareNormalization q full).indexed.decode node).card) :
    let cache := (prepareNormalization q full).indexed
    let kernel := PA17CellLayout003.kernelProgram full.length q cache.nodes.size goodSlot stage.val
    CapacityThroughout q (PA17CellLayout003.capacityWords full.length q cache.nodes.size)
      (givenTreeROM q full) kernel state ∧
      ∀ node : cache.NodeId,
        (execute (givenTreeROM q full).semantic kernel state).heap
          (PA17CellLayout003.workBase full.length q cache.nodes.size + node.val) ≤ (cache.decode node).card := by
  intro cache kernel
  let rom := givenTreeROM q full
  let work := PA17CellLayout003.workBase full.length q cache.nodes.size
  let good := PA17TableCell004.tableBase cache.nodes.size goodSlot
  let acc := PA17CellLayout003.accumulatorBase full.length q cache.nodes.size
  let metadata := PA17CellLayout003.metadataBase full.length q cache.nodes.size
  let stageAddress := PA17CellLayout003.stageBase full.length q cache.nodes.size + stage.val
  let extension := PA17HeapAncestors001.extensionProgram cache.nodes.size work (metadata + cache.nodes.size) stageAddress
  let middle := execute rom.semantic extension state
  have hsize : 0 < cache.nodes.size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hparent : ∀ index < cache.nodes.size, ∀ encoded ≤ cache.nodes.size,
      work + index ≠ metadata + cache.nodes.size + encoded :=
    PA17CellLayout003.work_parent_disjoint full.length q cache.nodes.size
  have hparents := PA17HeapAncestors001.metadata_parentHeapFor q full metadata state.heap hp.1
  have hstage := hp.2 stage
  have htag : state.heap (work + cache.nodes.size) ≤ 1 := by
    cases bad with
    | void => rw [hb]; exact Nat.zero_le _
    | vector capacity => rw [hb.1]
  have he := PA17HeapAncestors001.extensionProgram_capacityThroughout q
    (PA17CellLayout003.capacityWords full.length q cache.nodes.size) rom cache work
    (metadata + cache.nodes.size) stageAddress hsize hq hparent _ state hparents hstage htag hbound
  have hgood : DisjointSlots cache.nodes.size work good :=
    PA17CellLayout003.work_good_disjoint full.length q cache.nodes.size goodSlot hgoodSlot
  have hmcard (node : cache.NodeId) : middle.heap (good + 1 + node.val) ≤ (cache.decode node).card := by
    rw [PA17HeapAncestors001.extensionProgram_frame cache rom.semantic work (metadata + cache.nodes.size)
      stageAddress hsize hparent _ state hparents hstage (good + 1 + node.val) (by
        intro index hi
        simpa only [Nat.add_assoc] using
          (hgood index hi (1 + node.val) (by have := node.isLt; omega)).symm)]
    exact hcard node
  have hi := prepared_intersection_safe q full hq hlaminar
    (PA17CellLayout003.capacityWords full.length q cache.nodes.size) work good acc hgood
    (PA17CellLayout003.work_accumulator_disjoint full.length q cache.nodes.size) middle
    (by simpa only [List.take_length] using he _ le_rfl) hmcard
  constructor
  · exact UniformFreeTableSafety.capacityThroughout_append q _ rom _ _ state he hi.1
  · intro node
    dsimp only [kernel]
    rw [PA17CellLayout003.kernelProgram, PA17UniformCell002.kernelProgram, IndexedClosureRAM.execute_append]
    exact hi.2 node

/-- All actual prefixes of the full import/kernel/export cell are bounded.
Every output payload is <=card even if its semantic tag is VOID. The sole
physical card premise is on the good table input, independently of its tag. -/
theorem prepared_program_safe (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (goodSlot badSlot outputSlot : Nat)
    (hgoodSlot : goodSlot < cells full.length q) (hbadSlot : badSlot < cells full.length q)
    (houtSlot : outputSlot < cells full.length q) (stage : Fin full.length)
    (good bad : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (state : State)
    (hp : PA17TableCell004.Persistent q full hq state.heap)
    (hg : TagFirstRep (prepareNormalization q full).indexed state.heap
      (PA17TableCell004.tableBase (prepareNormalization q full).indexed.nodes.size goodSlot) good)
    (hb : TagFirstRep (prepareNormalization q full).indexed state.heap
      (PA17TableCell004.tableBase (prepareNormalization q full).indexed.nodes.size badSlot) bad)
    (hbound : CapacityPrefixBounded q
      (PA17CellLayout003.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      state.heap (PA17TableCell004.tableBase (prepareNormalization q full).indexed.nodes.size goodSlot + 1 + node.val) ≤
        ((prepareNormalization q full).indexed.decode node).card) :
    let cache := (prepareNormalization q full).indexed
    let code := PA17TableCell004.program full.length q cache.nodes.size goodSlot badSlot outputSlot stage.val
    let result := execute (givenTreeROM q full).semantic code state
    CapacityThroughout q (PA17CellLayout003.capacityWords full.length q cache.nodes.size)
      (givenTreeROM q full) code state ∧
      (∀ node : cache.NodeId,
        result.heap (PA17TableCell004.tableBase cache.nodes.size outputSlot + 1 + node.val) ≤ (cache.decode node).card) ∧
      TagFirstRep cache result.heap (PA17TableCell004.tableBase cache.nodes.size outputSlot)
        (IndexedEntry.cell cache full[stage.val] good bad) := by
  intro cache code result
  let rom := givenTreeROM q full
  let words := PA17CellLayout003.capacityWords full.length q cache.nodes.size
  let work := PA17CellLayout003.workBase full.length q cache.nodes.size
  let importCode := toTagLast cache.nodes.size (PA17TableCell004.tableBase cache.nodes.size badSlot) work
  let kernel := PA17CellLayout003.kernelProgram full.length q cache.nodes.size goodSlot stage.val
  let exportCode := toTagFirst cache.nodes.size work (PA17TableCell004.tableBase cache.nodes.size outputSlot)
  let copied := execute rom.semantic importCode state
  let computed := execute rom.semantic kernel copied
  have himport : CapacityThroughout q words rom importCode state := by
    apply toTagLast_capacityThroughout q words cache.nodes.size _ work rom _ state hbound
    exact (PA17CellLayout003.table_slot_bound full.length q cache.nodes.size badSlot hbadSlot
      cache.nodes.size le_rfl).trans_le (PA17CellLayout003.table_le_capacityWords full.length q cache.nodes.size)
  have hcopyp := PA17TableCell004.toWork_persistent q full hq badSlot state hp
  have hcopyb : IndexedCellRAM.SlotRep cache copied.heap work bad :=
    toTagLast_rep cache rom.semantic _ work (by
      intro left hl right hr
      exact (PA17CellLayout003.work_good_disjoint full.length q cache.nodes.size badSlot hbadSlot right hr left hl).symm)
      state bad hb
  have hcopycard (node : cache.NodeId) :
      copied.heap (PA17TableCell004.tableBase cache.nodes.size goodSlot + 1 + node.val) ≤ (cache.decode node).card := by
    rw [PA17TableCell004.toWork_frame rom.semantic full.length q cache.nodes.size badSlot state _
      (Or.inl (by
        simpa only [PA17TableCell004.tableBase, Nat.add_assoc] using
          PA17CellLayout003.table_slot_bound full.length q cache.nodes.size goodSlot hgoodSlot
            (1 + node.val) (by have := node.isLt; omega)))]
    exact hcard node
  obtain ⟨hkernel, hkernelcard⟩ := prepared_kernel_safe q full hq hlaminar goodSlot hgoodSlot stage bad copied
    hcopyp hcopyb (by simpa only [List.take_length] using himport _ le_rfl) hcopycard
  have hexport : CapacityThroughout q words rom exportCode computed := by
    have hsource : work + cache.nodes.size < words :=
      (PA17CellLayout003.capacity_slots_before_indices full.length q cache.nodes.size cache.nodes.size le_rfl).1
    apply toTagFirst_capacityThroughout q words cache.nodes.size work _ rom hsource computed
    simpa only [List.take_length] using hkernel _ le_rfl
  refine ⟨?_, ?_, PA17TableCell004.prepared_program_output q full hq hlaminar goodSlot badSlot outputSlot
    hgoodSlot hbadSlot houtSlot stage good bad state hp hg hb⟩
  · apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state
      (UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state himport hkernel)
    rw [IndexedClosureRAM.execute_append]
    exact hexport
  · intro node
    dsimp only [result, code]
    rw [PA17TableCell004.program, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
      toTagFirst_payload rom.semantic cache.nodes.size work (PA17TableCell004.tableBase cache.nodes.size outputSlot)
        (PA17CellLayout003.work_good_disjoint full.length q cache.nodes.size outputSlot houtSlot) _ node.val node.isLt]
    exact hkernelcard node

end PaperProofs.Structure.LaminarTree.PA17CellSafety006

