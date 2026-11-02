module
public import PaperProofs.Structure.PA17_Rolling_018B
public import PaperProofs.Structure.PA17_NormalizationSafety_004
import Mathlib.Tactic.IntervalCases

/-! Real rolling capacity prefixes and every-slot physical payload card bounds,
including payloads hidden by VOID tags. Formal core dependency adaptation. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17Rolling018C
open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001 PA17UniformCell002 PA17Rolling018

theorem copyBlock_prefix_heap (rom : ROM) (source target index count : Nat)
    (hc : count < 4) (state : State) :
    (IndexedRAM.execute rom ((IndexedCellRAM.copyBlock source target index).take count) state).heap = state.heap := by
  interval_cases count <;> rfl

theorem copyBlock_capacity (q words source target index : Nat) (rom : ROM)
    (hsource : source + index < words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityPrefixBounded q words
      (IndexedRAM.execute rom (IndexedCellRAM.copyBlock source target index) state).heap := by
  intro address ha
  rw [IndexedCellRAM.execute_copyBlock_heap]
  by_cases heq : address = target + index
  · rw [heq, Function.update_self]
    exact hcapacity _ hsource
  · rw [Function.update_of_ne heq]
    exact hcapacity address ha

theorem copyIndices_prefix_capacity (q words source target : Nat) (rom : ROM) (indices : List Nat)
    (hsource : ∀ index ∈ indices, source + index < words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) (count : Nat)
    (hc : count ≤ (IndexedCellRAM.copyIndices source target indices).length) :
    CapacityPrefixBounded q words
      (IndexedRAM.execute rom ((IndexedCellRAM.copyIndices source target indices).take count) state).heap := by
  induction indices generalizing state count with
  | nil => simpa only [IndexedCellRAM.copyIndices, List.flatMap_nil, List.take_nil, IndexedRAM.execute] using hcapacity
  | cons index later ih =>
    have hlen : (IndexedCellRAM.copyBlock source target index).length = 4 := rfl
    rw [IndexedCellRAM.copyIndices, List.flatMap_cons] at hc ⊢
    by_cases hsmall : count < 4
    · rw [List.take_append_of_le_length (by rw [hlen]; omega),
        copyBlock_prefix_heap rom source target index count hsmall state]
      exact hcapacity
    · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (show 4 ≤ count by omega)
      rw [heq, List.take_append, List.take_of_length_le (by rw [hlen]; omega), hlen,
        Nat.add_sub_cancel_left, IndexedRAM.execute_append]
      apply ih (fun node hn => hsource node (List.mem_cons_of_mem _ hn)) _
        (copyBlock_capacity q words source target index rom (hsource index List.mem_cons_self) state hcapacity) extra
      rw [List.length_append, hlen] at hc
      simpa only [IndexedCellRAM.copyIndices] using (show extra ≤ (List.flatMap (IndexedCellRAM.copyBlock source target) later).length by omega)

theorem copyWords_capacityThroughout (q words source target size : Nat) (rom : PhysicalROM)
    (hsource : source + size ≤ words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom ((IndexedCellRAM.copyWords source target size).map Op.base) state := by
  intro count hc
  rw [← List.map_take, execute_base]
  exact copyIndices_prefix_capacity q words source target rom.semantic (List.range size)
    (by intro index hi; have := List.mem_range.mp hi; omega) state hcapacity count
    (by simpa only [List.length_map, IndexedCellRAM.copyWords] using hc)

theorem toTagFirst_capacityThroughout (q words size source target : Nat) (rom : PhysicalROM)
    (hsource : source + size < words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (toTagFirst size source target) state := by
  rw [toTagFirst, List.map_append]
  have hl := copyWords_capacityThroughout q words source (target + 1) size rom (by omega) state hcapacity
  apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hl
  apply copyWords_capacityThroughout q words (source + size) target 1 rom (by omega)
  simpa only [List.take_length] using hl _ le_rfl

theorem toTagLast_capacityThroughout (q words size source target : Nat) (rom : PhysicalROM)
    (hsource : source + size < words) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom (toTagLast size source target) state := by
  rw [toTagLast, List.map_append]
  have hl := copyWords_capacityThroughout q words (source + 1) target size rom (by omega) state hcapacity
  apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hl
  apply copyWords_capacityThroughout q words source (target + size) 1 rom (by omega)
  simpa only [List.take_length] using hl _ le_rfl


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


theorem kernel_given_safe (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (goodSlot : Nat)
    (hgoodSlot : goodSlot < 2 * (q + 2)) (stage : Fin full.length) (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hs : StageReady q full hq stage state)
    (htag : state.heap (workBase q (prepareNormalization q full).indexed.nodes.size + (prepareNormalization q full).indexed.nodes.size) ≤ 1)
    (hbound : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      state.heap (base (prepareNormalization q full).indexed.nodes.size goodSlot + 1 + node.val) ≤
        ((prepareNormalization q full).indexed.decode node).card) :
    let cache := (prepareNormalization q full).indexed
    let code := PA17Rolling018.kernelProgram q cache.nodes.size goodSlot
    CapacityThroughout q (capacityWords q cache.nodes.size) (givenTreeROM q full) code state ∧
      ∀ node : cache.NodeId,
        (execute (givenTreeROM q full).semantic code state).heap (workBase q cache.nodes.size + node.val) ≤ (cache.decode node).card := by
  intro cache code
  let rom := givenTreeROM q full
  let work := workBase q cache.nodes.size
  let good := base cache.nodes.size goodSlot
  let acc := accumulatorBase q cache.nodes.size
  let metadata := metadataBase q cache.nodes.size
  let extension := PA17HeapAncestors001.extensionProgram cache.nodes.size work (metadata + cache.nodes.size) (stageWord q cache.nodes.size)
  let middle := execute rom.semantic extension state
  have hsize : 0 < cache.nodes.size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hparents := PA17HeapAncestors001.metadata_parentHeapFor q full metadata state.heap hm
  have he := PA17HeapAncestors001.extensionProgram_capacityThroughout q (capacityWords q cache.nodes.size) rom cache
    work (metadata + cache.nodes.size) (stageWord q cache.nodes.size) hsize hq (work_parent_disjoint q _)
    _ state hparents hs htag hbound
  have hgood : DisjointSlots cache.nodes.size work good := work_slot_disjoint q cache.nodes.size goodSlot hgoodSlot
  have hmcard (node : cache.NodeId) : middle.heap (good + 1 + node.val) ≤ (cache.decode node).card := by
    rw [PA17HeapAncestors001.extensionProgram_frame cache rom.semantic work (metadata + cache.nodes.size)
      (stageWord q cache.nodes.size) hsize (work_parent_disjoint q _) _ state hparents hs
      (good + 1 + node.val) (by
        intro index hi
        simpa only [Nat.add_assoc] using (hgood index hi (1 + node.val) (by have := node.isLt; omega)).symm)]
    exact hcard node
  have hi := prepared_intersection_safe q full hq hlaminar (capacityWords q cache.nodes.size)
    work good acc hgood (work_acc_disjoint q cache.nodes.size) middle
    (by simpa only [List.take_length] using he _ le_rfl) hmcard
  constructor
  · exact UniformFreeTableSafety.capacityThroughout_append q _ rom _ _ state he hi.1
  · intro node
    dsimp only [code]
    rw [PA17Rolling018.kernelProgram, PA17UniformCell002.kernelProgram, IndexedClosureRAM.execute_append]
    exact hi.2 node

theorem kernel_safe (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (goodSlot : Nat)
    (hgoodSlot : goodSlot < 2 * (q + 2)) (stage : Fin full.length) (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hs : StageReady q full hq stage state)
    (htag : state.heap (workBase q (prepareNormalization q full).indexed.nodes.size + (prepareNormalization q full).indexed.nodes.size) ≤ 1)
    (hbound : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcard : ∀ node : (prepareNormalization q full).indexed.NodeId,
      state.heap (base (prepareNormalization q full).indexed.nodes.size goodSlot + 1 + node.val) ≤
        ((prepareNormalization q full).indexed.decode node).card) :
    let cache := (prepareNormalization q full).indexed
    let code := PA17Rolling018.kernelProgram q cache.nodes.size goodSlot
    CapacityThroughout q (capacityWords q cache.nodes.size) (queryROM q full 0 used) code state ∧
      ∀ node : cache.NodeId,
        (execute (queryROM q full 0 used).semantic code state).heap (workBase q cache.nodes.size + node.val) ≤ (cache.decode node).card := by
  intro cache code
  have hg := kernel_given_safe q full hq hlaminar goodSlot hgoodSlot stage state hm hs htag hbound hcard
  constructor
  · intro count hc
    rw [execute_same_internal (queryROM q full 0 used).semantic (givenTreeROM q full).semantic
      (fun _ => rfl) (code.take count) (by intro op ho; exact kernel_internalOnly q cache.nodes.size goodSlot op (List.mem_of_mem_take ho))]
    exact hg.1 count hc
  · rw [kernel_queryROM_eq q full used]
    exact hg.2

def PhysicalCard (q : Nat) (full : List (Finset (Fin q))) (heap : Nat → Nat) : Prop :=
  ∀ slot < 2 * (q + 2), ∀ node : (prepareNormalization q full).indexed.NodeId,
    heap (base (prepareNormalization q full).indexed.nodes.size slot + 1 + node.val) ≤
      ((prepareNormalization q full).indexed.decode node).card

theorem cell_safe (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (budget : Fin (q + 2)) (state : State) (hi : Invariant q full state) (hs : StageReady q full hq stage state)
    (hbound : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcard : PhysicalCard q full state.heap) :
    let cache := (prepareNormalization q full).indexed
    let code := cellProgram q cache.nodes.size stage.val budget.val
    let result := execute (queryROM q full 0 used).semantic code state
    CapacityThroughout q (capacityWords q cache.nodes.size) (queryROM q full 0 used) code state ∧ PhysicalCard q full result.heap := by
  intro cache code result
  let rom := queryROM q full 0 used
  let words := capacityWords q cache.nodes.size
  let work := workBase q cache.nodes.size
  let goodSlot := slot q (stage.val + 1) budget.val
  let badSlot := slot q (stage.val + 1) (budget.val - 1)
  let outSlot := slot q stage.val budget.val
  let importCode := toTagLast cache.nodes.size (base cache.nodes.size badSlot) work
  let kernel := PA17Rolling018.kernelProgram q cache.nodes.size goodSlot
  let exportCode := toTagFirst cache.nodes.size work (base cache.nodes.size outSlot)
  let copied := execute rom.semantic importCode state
  let computed := execute rom.semantic kernel copied
  have hgoodSlot : goodSlot < 2 * (q + 2) := slot_lt q _ budget.val budget.isLt
  have hbadSlot : badSlot < 2 * (q + 2) := slot_lt q _ (budget.val - 1) (by have := budget.isLt; omega)
  have houtSlot : outSlot < 2 * (q + 2) := slot_lt q _ budget.val budget.isLt
  have himport : CapacityThroughout q words rom importCode state := by
    apply toTagLast_capacityThroughout q words cache.nodes.size _ work rom _ state hbound
    have hh := slot_word_lt_work q cache.nodes.size badSlot hbadSlot cache.nodes.size le_rfl
    unfold words capacityWords
    omega
  have hframe (address : Nat) (ha : work + cache.nodes.size < address ∨ address < work) : copied.heap address = state.heap address := by
    apply toTagLast_frame
    intro offset ho
    omega
  have hmeta : UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q cache.nodes.size) copied.heap := by
    apply metadata_transfer q full _ state.heap copied.heap hi.1
    intro address ha _
    apply hframe address
    change metadataBase q cache.nodes.size ≤ address at ha
    unfold metadataBase capacityWords at ha
    exact Or.inl (by dsimp only [work]; omega)
  have hstage : StageReady q full hq stage copied := by
    change copied.heap (stageWord q cache.nodes.size) = _
    rw [hframe _ (Or.inl (by unfold stageWord metadataBase capacityWords; dsimp only [work]; omega))]
    exact hs
  have htag : copied.heap (work + cache.nodes.size) ≤ 1 := by
    rw [toTagLast_tag rom.semantic cache.nodes.size (base cache.nodes.size badSlot) work
      (fun left hl right hr => (work_slot_disjoint q cache.nodes.size badSlot hbadSlot right hr left hl).symm) state]
    exact hi.2.1 badSlot hbadSlot
  have hc (node : cache.NodeId) : copied.heap (base cache.nodes.size goodSlot + 1 + node.val) ≤ (cache.decode node).card := by
    have hn : node.val < cache.nodes.size := node.isLt
    have hh := slot_word_lt_work q cache.nodes.size goodSlot hgoodSlot (1 + node.val) (by omega)
    rw [hframe _ (Or.inr (by simpa only [Nat.add_assoc] using hh))]
    exact hcard goodSlot hgoodSlot node
  have hk := kernel_safe q full hq hlaminar used goodSlot hgoodSlot stage copied hmeta hstage htag
    (by simpa only [List.take_length] using himport _ le_rfl) hc
  have hexport : CapacityThroughout q words rom exportCode computed := by
    have hsource : work + cache.nodes.size < words := by
      dsimp only [work, words, capacityWords]; omega
    apply toTagFirst_capacityThroughout q words cache.nodes.size work _ rom hsource computed
    simpa only [List.take_length] using hk.1 _ le_rfl
  constructor
  · apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state
      (UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state himport hk.1)
    rw [IndexedClosureRAM.execute_append]
    exact hexport
  · intro other ho node
    have hn : node.val < cache.nodes.size := node.isLt
    by_cases heq : other = outSlot
    · subst other
      dsimp only [result, code]
      rw [cellProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append,
        toTagFirst_payload rom.semantic cache.nodes.size work (base cache.nodes.size outSlot)
          (work_slot_disjoint q cache.nodes.size outSlot houtSlot) _ node.val node.isLt]
      exact hk.2 node
    · rw [cell_frame q full hq hlaminar used stage budget.val state hi.1 hs _
        (by intro offset hoff; have hoff' : offset ≤ cache.nodes.size := hoff; simpa only [Nat.add_assoc] using slots_disjoint cache.nodes.size other outSlot heq (1 + node.val) (by omega) offset hoff')
        (Or.inl (by simpa only [Nat.add_assoc] using slot_word_lt_work q cache.nodes.size other ho (1 + node.val) (by omega)))]
      exact hcard other ho node

theorem copyIndices_external_capacity (q words size source target : Nat) (rom : ROM) (indices : List Nat)
    (hindices : ∀ index ∈ indices, index < size)
    (hdisjoint : ∀ left < size, ∀ right < size, source + left ≠ target + right)
    (state : State) (hsource : ∀ index < size, state.heap (source + index) ≤ q)
    (hcapacity : CapacityPrefixBounded q words state.heap) (count : Nat)
    (hc : count ≤ (IndexedCellRAM.copyIndices source target indices).length) :
    CapacityPrefixBounded q words
      (IndexedRAM.execute rom ((IndexedCellRAM.copyIndices source target indices).take count) state).heap := by
  induction indices generalizing state count with
  | nil => simpa only [IndexedCellRAM.copyIndices, List.flatMap_nil, List.take_nil, IndexedRAM.execute] using hcapacity
  | cons index later ih =>
    have hlen : (IndexedCellRAM.copyBlock source target index).length = 4 := rfl
    rw [IndexedCellRAM.copyIndices, List.flatMap_cons] at hc ⊢
    by_cases hsmall : count < 4
    · rw [List.take_append_of_le_length (by rw [hlen]; omega), copyBlock_prefix_heap rom source target index count hsmall state]
      exact hcapacity
    · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (show 4 ≤ count by omega)
      rw [heq, List.take_append, List.take_of_length_le (by rw [hlen]; omega), hlen,
        Nat.add_sub_cancel_left, IndexedRAM.execute_append]
      have hsnext : ∀ node < size,
          (IndexedRAM.execute rom (IndexedCellRAM.copyBlock source target index) state).heap (source + node) ≤ q := by
        intro node hn
        rw [IndexedCellRAM.execute_copyBlock_heap,
          Function.update_of_ne (hdisjoint node hn index (hindices index List.mem_cons_self))]
        exact hsource node hn
      have hcnext : CapacityPrefixBounded q words
          (IndexedRAM.execute rom (IndexedCellRAM.copyBlock source target index) state).heap := by
        intro address ha
        rw [IndexedCellRAM.execute_copyBlock_heap]
        by_cases he : address = target + index
        · rw [he, Function.update_self]; exact hsource index (hindices index List.mem_cons_self)
        · rw [Function.update_of_ne he]; exact hcapacity address ha
      have hcn : extra ≤ (IndexedCellRAM.copyIndices source target later).length := by
        rw [List.length_append, hlen] at hc
        simpa only [IndexedCellRAM.copyIndices] using
          (show extra ≤ (List.flatMap (IndexedCellRAM.copyBlock source target) later).length by omega)
      exact ih (fun node hn => hindices node (List.mem_cons_of_mem _ hn)) _ hsnext hcnext extra hcn

theorem copyWords_external_capacityThroughout (q words size source target : Nat) (rom : PhysicalROM)
    (hdisjoint : ∀ left < size, ∀ right < size, source + left ≠ target + right)
    (state : State) (hsource : ∀ index < size, state.heap (source + index) ≤ q)
    (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom ((IndexedCellRAM.copyWords source target size).map Op.base) state := by
  intro count hc
  rw [← List.map_take, execute_base]
  exact copyIndices_external_capacity q words size source target rom.semantic (List.range size)
    (fun _ hn => List.mem_range.mp hn) hdisjoint state hsource hcapacity count
    (by simpa only [List.length_map, IndexedCellRAM.copyWords] using hc)

theorem constantBlock_capacityThroughout (q words target value : Nat) (rom : PhysicalROM)
    (hv : value ≤ q) (state : State) (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom ((IndexedCellRAM.constantBlock target value).map Op.base) state := by
  intro count hc
  change count ≤ 3 at hc
  interval_cases count <;> first
    | exact hcapacity
    | exact PA17NormalizationSafety004.bounded_update q words state.heap hcapacity target value hv

theorem freeSlot_capacityThroughout (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (slot : Nat) (hs : slot < 2 * (q + 2)) (rom : PhysicalROM) (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcapacity : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    CapacityThroughout q (capacityWords q (prepareNormalization q full).indexed.nodes.size) rom
      (freeSlot q (prepareNormalization q full).indexed.nodes.size slot) state := by
  let size := (prepareNormalization q full).indexed.nodes.size
  have hp := copyWords_external_capacityThroughout q (capacityWords q size) size (metadataBase q size)
    (base size slot + 1) rom (by
      intro left hl right hr
      have hh := slot_word_lt_work q size slot hs (1 + right) (by omega)
      unfold metadataBase capacityWords
      omega) state (by
        intro index hi
        exact UniformTreeMetadataRAM.metadata_card_bound q full (metadataBase q size) state.heap hm ⟨index, hi⟩) hcapacity
  apply UniformFreeTableSafety.capacityThroughout_append q _ rom _ _ state hp
  apply constantBlock_capacityThroughout q _ _ _ rom hq
  simpa only [List.take_length] using hp _ le_rfl

theorem freeSlots_capacityThroughout (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (slots : List Nat) (hs : ∀ slot ∈ slots, slot < 2 * (q + 2)) (rom : PhysicalROM) (state : State)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcapacity : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    CapacityThroughout q (capacityWords q (prepareNormalization q full).indexed.nodes.size) rom
      (slots.flatMap (freeSlot q (prepareNormalization q full).indexed.nodes.size)) state := by
  induction slots generalizing state with
  | nil => intro count _; simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hcapacity
  | cons head later ih =>
    rw [List.flatMap_cons]
    have hh := freeSlot_capacityThroughout q full hq head (hs head List.mem_cons_self) rom state hm hcapacity
    apply UniformFreeTableSafety.capacityThroughout_append q _ rom _ _ state hh
    apply ih (fun slot hslot => hs slot (List.mem_cons_of_mem _ hslot))
    · exact freeSlot_metadata q full head (hs head List.mem_cons_self) rom.semantic state hm
    · simpa only [List.take_length] using hh _ le_rfl

theorem prepareProgram_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (state : State)
    (hcapacity : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := prepareProgram full.length q size
    let result := execute (queryROM q full 0 used).semantic code state
    CapacityThroughout q (capacityWords q size) (queryROM q full 0 used) code state ∧ PhysicalCard q full result.heap := by
  intro size code result
  let rom := queryROM q full 0 used
  have hm := UniformFreeTableSafety.metadataProgram_capacityThroughout q (capacityWords q size) rom full.length q size
    (metadataBase q size) le_rfl state hcapacity
  constructor
  · apply UniformFreeTableSafety.capacityThroughout_append q _ rom _ _ state hm
    apply freeSlots_capacityThroughout q full hq (List.range (2 * (q + 2))) (fun _ hn => List.mem_range.mp hn) rom
    · exact PA17QueryMetadata010.prepared_program_metadata q full hq hlaminar 0 used _ state
    · simpa only [List.take_length] using hm _ le_rfl
  · intro slot hs node
    have hp := (prepared_prepare q full hq hlaminar used state).2 slot hs
    have he := hp.2 node
    rw [IndexedEntry.reifyCapacity_get] at he
    exact he.le

theorem stageProgram_prefixFrame (rom : ROM) (N q size stage address : Nat)
    (hne : address ≠ stageWord q size) :
    UniformFreeTableSafety.PrefixFrame rom (stageProgram N q size stage) address := by
  apply UniformFreeTableSafety.PrefixFrame.append
  · intro state count _
    apply congrFun
    apply PA17StageMap001.execute_noStore_heap
    intro op ho
    have hh := List.mem_of_mem_take ho
    simp only [List.mem_append, List.mem_cons, List.mem_nil_iff, or_false, List.mem_flatMap] at hh
    rcases hh with rfl | ⟨node, _, hn⟩
    · trivial
    · exact PA17StageMap001.nodeBlock_noStore N q stage node op hn
  · intro state count hc
    change count ≤ 2 at hc
    interval_cases count <;> first
      | rfl
      | exact Function.update_of_ne hne _ _

theorem stageProgram_capacityThroughout (q N size stage : Nat) (rom : PhysicalROM) (state : State)
    (hbound : CapacityPrefixBounded q (capacityWords q size) state.heap) :
    CapacityThroughout q (capacityWords q size) rom (stageProgram N q size stage) state := by
  intro count hc address ha
  rw [stageProgram_prefixFrame rom.semantic N q size stage address
    (by unfold stageWord metadataBase; omega) state count hc]
  exact hbound address ha

theorem stageProgram_physicalCard (q : Nat) (full : List (Finset (Fin q))) (stage : Nat)
    (rom : ROM) (state : State) (hcard : PhysicalCard q full state.heap) :
    PhysicalCard q full (execute rom (stageProgram full.length q (prepareNormalization q full).indexed.nodes.size stage) state).heap := by
  intro slot hs node
  rw [stageProgram_frame rom full.length q _ stage state _ (by
    have hh := slot_word_lt_work q (prepareNormalization q full).indexed.nodes.size slot hs
      (1 + node.val) (by have hn := node.isLt; omega)
    unfold stageWord metadataBase capacityWords
    omega)]
  exact hcard slot hs node

theorem budgets_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (budgets : List Nat) (hbudgets : ∀ budget ∈ budgets, 0 < budget ∧ budget < q + 2)
    (state : State) (hi : Invariant q full state) (hs : StageReady q full hq stage state)
    (hnext : RowReady q full ⟨stage.val + 1, by omega⟩ state)
    (hbound : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcard : PhysicalCard q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := budgets.flatMap (cellProgram q size stage.val)
    let result := execute (queryROM q full 0 used).semantic code state
    CapacityThroughout q (capacityWords q size) (queryROM q full 0 used) code state ∧
      PhysicalCard q full result.heap ∧ Invariant q full result ∧ StageReady q full hq stage result ∧
        RowReady q full ⟨stage.val + 1, by omega⟩ result := by
  induction budgets generalizing state with
  | nil =>
    refine ⟨?_, hcard, hi, hs, hnext⟩
    intro count _
    simpa only [List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hbound
  | cons head later ih =>
    have hhead := hbudgets head List.mem_cons_self
    have hc := cell_safe q full hq hlaminar used stage ⟨head, hhead.2⟩ state hi hs hbound hcard
    have hm := cell_preserves_invariant q full hq hlaminar used stage ⟨head, hhead.2⟩ hhead.1 state hi hs hnext
    have hl := ih (fun budget hb => hbudgets budget (List.mem_cons_of_mem _ hb))
      _ hm.1 hm.2.1 hm.2.2.1 (by simpa only [List.take_length] using hc.1 _ le_rfl) hc.2
    dsimp only at hl ⊢
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    refine ⟨?_, hl.2⟩
    exact UniformFreeTableSafety.capacityThroughout_append q _ (queryROM q full 0 used) _ _ state hc.1 hl.1

theorem rowProgram_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (stage : Fin full.length)
    (state : State) (hi : Invariant q full state)
    (hnext : RowReady q full ⟨stage.val + 1, by omega⟩ state)
    (hbound : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcard : PhysicalCard q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := rowProgram full.length q size stage.val
    let result := execute (queryROM q full 0 used).semantic code state
    CapacityThroughout q (capacityWords q size) (queryROM q full 0 used) code state ∧
      PhysicalCard q full result.heap ∧ Invariant q full result ∧ RowReady q full ⟨stage.val, by omega⟩ result := by
  intro size code result
  let afterStage := execute (queryROM q full 0 used).semantic (stageProgram full.length q size stage.val) state
  have hstage := stageProgram_capacityThroughout q full.length size stage.val (queryROM q full 0 used) state hbound
  have hb := budgets_safe q full hq hlaminar used stage (positiveBudgets q)
    (fun budget hm => (positiveBudgets_mem q budget).mp hm) afterStage
    (stageProgram_preserves_invariant q full used stage.val state hi)
    (prepared_stageProgram q full hq used stage state)
    (stageProgram_preserves_row q full used stage.val _ state hnext)
    (by simpa only [List.take_length] using hstage _ le_rfl)
    (stageProgram_physicalCard q full stage.val (queryROM q full 0 used).semantic state hcard)
  have hsemantic := prepared_rowProgram q full hq hlaminar used stage state hi hnext
  refine ⟨?_, ?_, hsemantic⟩
  · exact UniformFreeTableSafety.capacityThroughout_append q _ (queryROM q full 0 used) _ _ state hstage hb.1
  · dsimp only [result, code, rowProgram]
    rw [IndexedClosureRAM.execute_append]
    exact hb.2.1

theorem scheduleProgram_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (count : Nat) (hc : count ≤ full.length)
    (state : State) (hi : Invariant q full state) (hrow : RowReady q full ⟨count, by omega⟩ state)
    (hbound : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hcard : PhysicalCard q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := scheduleProgram full.length q size count
    let result := execute (queryROM q full 0 used).semantic code state
    CapacityThroughout q (capacityWords q size) (queryROM q full 0 used) code state ∧
      PhysicalCard q full result.heap ∧ Invariant q full result ∧ RowReady q full ⟨0, by omega⟩ result := by
  induction count generalizing state with
  | zero =>
    refine ⟨?_, hcard, hi, hrow⟩
    intro count _
    simpa only [scheduleProgram, List.range_zero, List.reverse_nil, List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hbound
  | succ count ih =>
    have hs : count < full.length := by omega
    have hr := rowProgram_safe q full hq hlaminar used ⟨count, hs⟩ state hi hrow hbound hcard
    have ht := ih (by omega) _ hr.2.2.1 hr.2.2.2
      (by simpa only [List.take_length] using hr.1 _ le_rfl) hr.2.1
    dsimp only at ht ⊢
    rw [scheduleProgram_succ, IndexedClosureRAM.execute_append]
    exact ⟨UniformFreeTableSafety.capacityThroughout_append q _ (queryROM q full 0 used) _ _ state hr.1 ht.1, ht.2⟩

theorem prepared_build_safe (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let code := buildProgram full.length q size
    let result := execute (queryROM q full 0 used).semantic code (initial (fun _ => 0))
    CapacityThroughout q (capacityWords q size) (queryROM q full 0 used) code (initial (fun _ => 0)) ∧
      PhysicalCard q full result.heap := by
  intro size code result
  let seed := execute (queryROM q full 0 used).semantic (prepareProgram full.length q size) (initial (fun _ => 0))
  have hp := prepared_prepare q full hq hlaminar used (initial (fun _ => 0))
  have hsafe := prepareProgram_safe q full hq hlaminar used (initial (fun _ => 0)) (fun _ _ => Nat.zero_le q)
  have hi : Invariant q full seed := by
    refine ⟨hp.1, ?_, ?_⟩
    · intro index hs
      exact tag_le_one _ _ _ _ (hp.2 index hs)
    · intro stage
      exact hp.2 _ (slot_lt q stage 0 (by omega))
  have ht : RowReady q full ⟨full.length, by omega⟩ seed := by
    intro budget
    unfold CellReady
    rw [storedRow_terminal]
    exact hp.2 _ (slot_lt q full.length budget.val budget.isLt)
  have hs := scheduleProgram_safe q full hq hlaminar used full.length le_rfl seed hi ht
    (by simpa only [List.take_length] using hsafe.1 _ le_rfl) hsafe.2
  constructor
  · exact UniformFreeTableSafety.capacityThroughout_append q _ (queryROM q full 0 used) _ _ (initial (fun _ => 0)) hsafe.1 hs.1
  · dsimp only [result, code, buildProgram]
    rw [IndexedClosureRAM.execute_append]
    exact hs.2.1

theorem prepared_program_capacityThroughout (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    CapacityThroughout q (capacityWords q size) (queryROM q full 0 used)
      (PA17Rolling018B.program full.length q size) (initial (fun _ => 0)) := by
  intro size
  have hb := prepared_build_safe q full hq hlaminar used
  apply UniformFreeTableSafety.capacityThroughout_append q _ (queryROM q full 0 used) _ _ (initial (fun _ => 0)) hb.1
  apply PA17Rolling018B.finishProgram_capacityThroughout
  simpa only [List.take_length] using hb.1 _ le_rfl

theorem prepared_program_physicalCard (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    PhysicalCard q full
      (execute (queryROM q full 0 used).semantic (PA17Rolling018B.program full.length q size) (initial (fun _ => 0))).heap := by
  intro size other ho node
  have hn : node.val < size := node.isLt
  have hh := slot_word_lt_work q size other ho (1 + node.val) (by omega)
  have hf := PA17Rolling018B.finishProgram_prefixFrame (queryROM q full 0 used).semantic full.length q size
    (base size other + 1 + node.val) (by
      unfold PA17Rolling018B.rowPointer stageWord metadataBase capacityWords
      omega)
    (execute (queryROM q full 0 used).semantic (buildProgram full.length q size) (initial (fun _ => 0)))
    (PA17Rolling018B.finishProgram full.length q size).length le_rfl
  rw [List.take_length] at hf
  rw [PA17Rolling018B.program, IndexedClosureRAM.execute_append, hf]
  exact (prepared_build_safe q full hq hlaminar used).2 other ho node

end PaperProofs.Structure.LaminarTree.PA17Rolling018C
