module

public import PaperProofs.Structure.PA17_TagBridge_001

/-! A17 batch 002: actual runtime metadata followed by explicit tag-first
terminal-row and all-stage budget-zero initialization. The remaining positive
budget cells are left for the later full-table recurrence schedule. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17TerminalRow002

open IndexedRAM IndexedClosureRAM AlgorithmClaims
open PA17TagBridge001

variable {Tool : Type*}

def slotBase (size slot : Nat) : Nat := slot * (size + 1)

def writeFreeSlot (size metadataBase slot : Nat) : List Op :=
  (IndexedCellRAM.copyWords metadataBase (slotBase size slot + 1) size).map Op.base ++
    (IndexedCellRAM.constantBlock (slotBase size slot) 1).map Op.base

def freeSlots (size metadataBase : Nat) (slots : List Nat) : List Op :=
  slots.flatMap (writeFreeSlot size metadataBase)

def seedSlots (N q : Nat) : List Nat :=
  ((List.range (N + 1)).map (fun stage => stage * (q + 2))) ++
    ((List.range (q + 2)).map (fun budget => N * (q + 2) + budget))

def program (N q size : Nat) : List Op :=
  UniformTreeMetadataRAM.program N q size (tableWords N q size) ++
    freeSlots size (tableWords N q size) (seedSlots N q)

theorem slotBase_disjoint (size left right : Nat) (hne : left ≠ right)
    (i j : Nat) (hi : i ≤ size) (hj : j ≤ size) :
    slotBase size left + i ≠ slotBase size right + j := by
  intro heq
  have hpositive : 0 < size + 1 := by omega
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · have hstep := Nat.mul_le_mul_right (size + 1) (show left + 1 ≤ right by omega)
    dsimp [slotBase] at heq
    rw [Nat.add_mul] at hstep
    omega
  · have hstep := Nat.mul_le_mul_right (size + 1) (show right + 1 ≤ left by omega)
    dsimp [slotBase] at heq
    rw [Nat.add_mul] at hstep
    omega

theorem writeFreeSlot_tag (rom : ROM) (size metadataBase slot : Nat) (state : State) :
    (execute rom (writeFreeSlot size metadataBase slot) state).heap (slotBase size slot) = 1 := by
  rw [writeFreeSlot, IndexedClosureRAM.execute_append, execute_base,
    IndexedCellRAM.execute_constantBlock_heap, Function.update_self]

theorem writeFreeSlot_payload (rom : ROM) (size metadataBase slot : Nat)
    (hslot : (slot + 1) * (size + 1) ≤ metadataBase) (state : State) (index : Nat) (hi : index < size) :
    (execute rom (writeFreeSlot size metadataBase slot) state).heap (slotBase size slot + 1 + index) =
      state.heap (metadataBase + index) := by
  rw [writeFreeSlot, IndexedClosureRAM.execute_append, execute_base, execute_base,
    IndexedCellRAM.execute_constantBlock_heap, Function.update_of_ne (by omega)]
  apply IndexedCellRAM.copyWords_value rom metadataBase (slotBase size slot + 1) size _ state index hi
  intro left hl right hr
  dsimp [slotBase]
  rw [Nat.add_mul] at hslot
  omega

theorem writeFreeSlot_frame (rom : ROM) (size metadataBase slot : Nat) (state : State)
    (address : Nat) (hframe : ∀ index ≤ size, address ≠ slotBase size slot + index) :
    (execute rom (writeFreeSlot size metadataBase slot) state).heap address = state.heap address := by
  rw [writeFreeSlot, IndexedClosureRAM.execute_append, execute_base, execute_base,
    IndexedCellRAM.execute_constantBlock_heap, Function.update_of_ne (by simpa only [Nat.add_zero] using hframe 0 (Nat.zero_le size)),
    IndexedCellRAM.copyWords_frame rom metadataBase (slotBase size slot + 1) size state address (by
      intro index hi
      simpa only [Nat.add_assoc] using hframe (1 + index) (by omega))]

theorem writeFreeSlot_rep (cache : IndexedNodeCache Tool) (rom : ROM) (metadataBase slot : Nat)
    (hslot : (slot + 1) * (cache.nodes.size + 1) ≤ metadataBase) (state : State)
    (hcard : ∀ node : cache.NodeId, state.heap (metadataBase + node.val) = (cache.decode node).card) :
    TagFirstRep cache (execute rom (writeFreeSlot cache.nodes.size metadataBase slot) state).heap
      (slotBase cache.nodes.size slot) (IndexedEntry.free cache) := by
  refine ⟨writeFreeSlot_tag rom _ _ _ state, ?_⟩
  intro node
  rw [writeFreeSlot_payload rom _ _ _ hslot state node.val node.isLt,
    IndexedEntry.reifyCapacity_get]
  exact hcard node

theorem freeSlots_frame (rom : ROM) (size metadataBase : Nat) (slots : List Nat) (state : State)
    (address : Nat) (hframe : ∀ slot ∈ slots, ∀ index ≤ size, address ≠ slotBase size slot + index) :
    (execute rom (freeSlots size metadataBase slots) state).heap address = state.heap address := by
  induction slots generalizing state with
  | nil => rfl
  | cons head later ih =>
    rw [freeSlots, List.flatMap_cons, IndexedClosureRAM.execute_append]
    change (execute rom (freeSlots size metadataBase later)
      (execute rom (writeFreeSlot size metadataBase head) state)).heap address = _
    rw [ih _ (fun slot hs => hframe slot (List.mem_cons_of_mem _ hs))]
    exact writeFreeSlot_frame rom size metadataBase head state address (hframe head List.mem_cons_self)

theorem freeSlots_metadata_frame (rom : ROM) (size metadataBase : Nat) (slots : List Nat)
    (hslots : ∀ slot ∈ slots, (slot + 1) * (size + 1) ≤ metadataBase)
    (state : State) (address : Nat) (ha : metadataBase ≤ address) :
    (execute rom (freeSlots size metadataBase slots) state).heap address = state.heap address := by
  apply freeSlots_frame
  intro slot hs index hi
  have hh := hslots slot hs
  dsimp [slotBase]
  rw [Nat.add_mul] at hh
  omega

theorem freeSlots_rep (cache : IndexedNodeCache Tool) (rom : ROM) (metadataBase : Nat) (slots : List Nat)
    (hslots : ∀ slot ∈ slots, (slot + 1) * (cache.nodes.size + 1) ≤ metadataBase)
    (state : State) (hcard : ∀ node : cache.NodeId, state.heap (metadataBase + node.val) = (cache.decode node).card)
    (slot : Nat) (hs : slot ∈ slots) :
    TagFirstRep cache (execute rom (freeSlots cache.nodes.size metadataBase slots) state).heap
      (slotBase cache.nodes.size slot) (IndexedEntry.free cache) := by
  induction slots generalizing state with
  | nil => cases hs
  | cons head later ih =>
    have hhead := hslots head List.mem_cons_self
    have htail : ∀ s ∈ later, (s + 1) * (cache.nodes.size + 1) ≤ metadataBase :=
      fun s hm => hslots s (List.mem_cons_of_mem _ hm)
    rw [freeSlots, List.flatMap_cons, IndexedClosureRAM.execute_append]
    change TagFirstRep cache (execute rom (freeSlots cache.nodes.size metadataBase later)
      (execute rom (writeFreeSlot cache.nodes.size metadataBase head) state)).heap
      (slotBase cache.nodes.size slot) (IndexedEntry.free cache)
    by_cases hmem : slot ∈ later
    · apply ih htail _ _ hmem
      intro node
      rw [writeFreeSlot_frame rom _ metadataBase head state (metadataBase + node.val) (by
        intro index hi
        dsimp [slotBase]
        rw [Nat.add_mul] at hhead
        omega)]
      exact hcard node
    · have heq : slot = head := (List.mem_cons.mp hs).resolve_right hmem
      subst head
      have hrep := writeFreeSlot_rep cache rom metadataBase slot hhead state hcard
      refine ⟨?_, ?_⟩
      · rw [freeSlots_frame rom _ metadataBase later _ (slotBase cache.nodes.size slot) (by
          intro other ho index hi
          have hne : slot ≠ other := by intro he; exact hmem (he.symm ▸ ho)
          simpa only [Nat.add_zero] using slotBase_disjoint cache.nodes.size slot other hne 0 index (Nat.zero_le _) hi)]
        exact hrep.1
      · intro node
        rw [freeSlots_frame rom _ metadataBase later _ (slotBase cache.nodes.size slot + 1 + node.val) (by
          intro other ho index hi
          have hne : slot ≠ other := by intro he; exact hmem (he.symm ▸ ho)
          simpa only [Nat.add_assoc] using slotBase_disjoint cache.nodes.size slot other hne (1 + node.val) index (by omega) hi)]
        exact hrep.2 node

theorem seedSlots_mem_bound (N q slot : Nat) (hs : slot ∈ seedSlots N q) : slot < cells N q := by
  rw [seedSlots, List.mem_append] at hs
  rcases hs with hzero | hterminal
  · obtain ⟨stage, hstage, rfl⟩ := List.mem_map.mp hzero
    have hstage' := List.mem_range.mp hstage
    unfold cells
    have hm := Nat.mul_le_mul_right (q + 2) (show stage + 1 ≤ N + 1 by omega)
    rw [Nat.add_mul] at hm
    omega
  · obtain ⟨budget, hbudget, rfl⟩ := List.mem_map.mp hterminal
    have hbudget' := List.mem_range.mp hbudget
    unfold cells
    rw [Nat.add_mul]
    omega

theorem seedSlots_words_bound (N q size slot : Nat) (hs : slot ∈ seedSlots N q) :
    (slot + 1) * (size + 1) ≤ tableWords N q size := by
  exact Nat.mul_le_mul_right (size + 1) (seedSlots_mem_bound N q slot hs)

theorem prepared_program_rep (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) (slot : Nat) (hs : slot ∈ seedSlots full.length q) :
    let cache := (prepareNormalization q full).indexed
    TagFirstRep cache (execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state).heap
      (slotBase cache.nodes.size slot) (IndexedEntry.free cache) := by
  intro cache
  rw [program, IndexedClosureRAM.execute_append]
  apply freeSlots_rep cache (givenTreeROM q full).semantic (tableWords full.length q cache.nodes.size)
    (seedSlots full.length q) (seedSlots_words_bound full.length q cache.nodes.size) _ _ slot hs
  intro node
  exact ((UniformTreeMetadataRAM.prepared_program_metadata q full hq hlaminar
    (tableWords full.length q cache.nodes.size) state).2 node).1

theorem prepared_program_readEntry (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) (slot : Nat) (hs : slot ∈ seedSlots full.length q) :
    let cache := (prepareNormalization q full).indexed
    readEntry cache.nodes.size slot (execute (givenTreeROM q full).semantic
      (program full.length q cache.nodes.size) state).heap = IndexedEntry.free cache := by
  intro cache
  exact readEntry_eq_of_rep cache slot _ _ (prepared_program_rep q full hq hlaminar state slot hs)

theorem prepared_program_metadata (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) :
    let cache := (prepareNormalization q full).indexed
    UniformTreeMetadataRAM.MetadataCorrect q full (tableWords full.length q cache.nodes.size)
      (execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state).heap := by
  intro cache
  rw [program, IndexedClosureRAM.execute_append]
  have hm := UniformTreeMetadataRAM.prepared_program_metadata q full hq hlaminar
    (tableWords full.length q cache.nodes.size) state
  constructor
  · rw [freeSlots_metadata_frame _ _ _ _ (seedSlots_words_bound full.length q cache.nodes.size) _ _ (by
      dsimp [UniformTreeMetadataRAM.parentAddress]; omega)]
    exact hm.1
  · intro node
    rw [freeSlots_metadata_frame _ _ _ _ (seedSlots_words_bound full.length q cache.nodes.size) _ _ (by
        dsimp [UniformTreeMetadataRAM.cardAddress]; omega),
      freeSlots_metadata_frame _ _ _ _ (seedSlots_words_bound full.length q cache.nodes.size) _ _ (by
        dsimp [UniformTreeMetadataRAM.parentAddress]; omega),
      freeSlots_metadata_frame _ _ _ _ (seedSlots_words_bound full.length q cache.nodes.size) _ _ (by
        dsimp [UniformTreeMetadataRAM.internalAddress]; omega)]
    exact hm.2 node

theorem prepared_program_budgetZero (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) (stage : Fin (full.length + 1)) :
    let cache := (prepareNormalization q full).indexed
    readEntry cache.nodes.size (stage.val * (q + 2))
      (execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state).heap = IndexedEntry.free cache := by
  apply prepared_program_readEntry q full hq hlaminar state
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨stage.val, List.mem_range.mpr stage.isLt, rfl⟩

theorem prepared_program_terminal (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) (budget : Fin (q + 2)) :
    let cache := (prepareNormalization q full).indexed
    readEntry cache.nodes.size (full.length * (q + 2) + budget.val)
      (execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state).heap = IndexedEntry.free cache := by
  apply prepared_program_readEntry q full hq hlaminar state
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨budget.val, List.mem_range.mpr budget.isLt, rfl⟩

theorem writeFreeSlot_trace_length (size metadataBase slot : Nat) :
    (trace (writeFreeSlot size metadataBase slot)).length = 38 * size + 27 := by
  rw [writeFreeSlot, IndexedClosureRAM.trace_append, List.length_append, trace_base_length,
    trace_base_length, IndexedCellRAM.copyWords_trace_length]
  rfl

theorem freeSlots_trace_length (size metadataBase : Nat) (slots : List Nat) :
    (trace (freeSlots size metadataBase slots)).length = slots.length * (38 * size + 27) := by
  induction slots with
  | nil => simp only [freeSlots, trace, List.flatMap_nil, List.length_nil, Nat.zero_mul]
  | cons head later ih =>
    rw [freeSlots, List.flatMap_cons, IndexedClosureRAM.trace_append, List.length_append,
      writeFreeSlot_trace_length]
    change 38 * size + 27 + (trace (freeSlots size metadataBase later)).length = _
    rw [ih, List.length_cons, Nat.add_mul, Nat.one_mul]
    omega

theorem seedSlots_length (N q : Nat) : (seedSlots N q).length = N + q + 3 := by
  simp only [seedSlots, List.length_append, List.length_map, List.length_range]
  omega

theorem program_trace_length (N q size : Nat) :
    (trace (program N q size) ++ haltTrace).length =
      (30 * q + 131) * size + 27 + (N + q + 3) * (38 * size + 27) + 6 := by
  rw [List.length_append, program, IndexedClosureRAM.trace_append, List.length_append,
    UniformTreeMetadataRAM.program_trace_length, freeSlots_trace_length, seedSlots_length, haltTrace_length]

theorem rowsList_terminal [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (maxBudget : Nat) (suffix : List (Finset Tool)) :
    (IndexedTable.rowsList cache maxBudget suffix)[suffix.length]'(by
      rw [IndexedTable.rowsList_length]; omega) = IndexedTable.terminalRow cache maxBudget := by
  induction suffix with
  | nil => rfl
  | cons eligible later ih =>
    simpa only [IndexedTable.rowsList, IndexedTable.rows, List.length_cons,
      List.getElem_cons_succ] using ih

theorem rowsList_budgetZero [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (maxBudget : Nat) (suffix : List (Finset Tool)) (stage : Nat) (hstage : stage ≤ suffix.length) :
    ((IndexedTable.rowsList cache maxBudget suffix)[stage]'(by
      rw [IndexedTable.rowsList_length]; omega)).get ⟨0, by omega⟩ = IndexedEntry.free cache := by
  induction suffix generalizing stage with
  | nil =>
    have hz : stage = 0 := by simpa only [List.length_nil] using Nat.eq_zero_of_le_zero hstage
    subst stage
    exact IndexedTable.terminalRow_get cache maxBudget ⟨0, by omega⟩
  | cons eligible later ih =>
    cases stage with
    | zero =>
      change (IndexedTable.rowStep cache maxBudget eligible (IndexedTable.rows cache maxBudget later).1).get ⟨0, by omega⟩ = _
      rw [IndexedTable.rowStep_get]
      rfl
    | succ stage =>
      simpa only [IndexedTable.rowsList, IndexedTable.rows, List.getElem_cons_succ] using
        ih stage (by simpa only [List.length_cons] using Nat.le_of_succ_le_succ hstage)

theorem storedPositiveRow_terminal (q : Nat) (full : List (Finset (Fin q))) :
    IndexedQuery.storedPositiveRow q full ⟨full.length, by omega⟩ =
      IndexedTable.terminalRow (prepareNormalization q full).indexed (q + 1) := by
  simpa only [IndexedQuery.storedPositiveRow, IndexedTable.buildPositive, List.getElem_toArray] using
    rowsList_terminal (prepareNormalization q full).indexed (q + 1) full

theorem storedPositiveRow_budgetZero (q : Nat) (full : List (Finset (Fin q))) (stage : Fin (full.length + 1)) :
    (IndexedQuery.storedPositiveRow q full stage).get ⟨0, by omega⟩ =
      IndexedEntry.free (prepareNormalization q full).indexed := by
  simpa only [IndexedQuery.storedPositiveRow, IndexedTable.buildPositive, List.getElem_toArray] using
    rowsList_budgetZero (prepareNormalization q full).indexed (q + 1) full stage.val (by omega)

theorem prepared_program_terminal_stored (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) (budget : Fin (q + 2)) :
    let cache := (prepareNormalization q full).indexed
    readEntry cache.nodes.size (full.length * (q + 2) + budget.val)
      (execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state).heap =
        (IndexedQuery.storedPositiveRow q full ⟨full.length, by omega⟩).get budget := by
  rw [storedPositiveRow_terminal, IndexedTable.terminalRow_get]
  exact prepared_program_terminal q full hq hlaminar state budget

theorem prepared_program_budgetZero_stored (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) (stage : Fin (full.length + 1)) :
    let cache := (prepareNormalization q full).indexed
    readEntry cache.nodes.size (stage.val * (q + 2))
      (execute (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state).heap =
        (IndexedQuery.storedPositiveRow q full stage).get ⟨0, by omega⟩ := by
  rw [storedPositiveRow_budgetZero]
  exact prepared_program_budgetZero q full hq hlaminar state stage

theorem program_trace_le (N q size : Nat) (hsize : 0 < size) :
    (trace (program N q size) ++ haltTrace).length ≤ 359 * (N + q + 1) * size := by
  rw [program_trace_length]
  have hN : N ≤ N * size := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left N hsize
  have hq : q ≤ q * size := by simpa only [Nat.mul_one] using Nat.mul_le_mul_left q hsize
  nlinarith

theorem writeFreeSlot_length (size metadataBase slot : Nat) :
    (writeFreeSlot size metadataBase slot).length = 4 * size + 3 := by
  rw [writeFreeSlot, List.length_append, List.length_map, IndexedCellRAM.copyWords_length]
  rfl

theorem freeSlots_length (size metadataBase : Nat) (slots : List Nat) :
    (freeSlots size metadataBase slots).length = slots.length * (4 * size + 3) := by
  simp only [freeSlots, List.length_flatMap, writeFreeSlot_length, List.map_const',
    List.sum_replicate, Nat.nsmul_eq_mul]

theorem program_length (N q size : Nat) :
    (program N q size).length = (3 * q + 14) * size + 3 + (N + q + 3) * (4 * size + 3) := by
  rw [program, List.length_append, UniformTreeMetadataRAM.program_length, freeSlots_length, seedSlots_length]

theorem program_code_length (N q size : Nat) :
    (haltingWords (program N q size)).length =
      5 * ((3 * q + 14) * size + 3 + (N + q + 3) * (4 * size + 3)) + 5 := by
  rw [haltingWords_length, program_length]

theorem copyBlock_capacity_values (q words source target index : Nat) (rom : ROM) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap) (hvalue : state.heap (source + index) ≤ q) :
    CapacityPrefixBounded q words
      (IndexedRAM.execute rom (IndexedCellRAM.copyBlock source target index) state).heap := by
  intro address ha
  rw [IndexedCellRAM.execute_copyBlock_heap]
  by_cases heq : address = target + index
  · rw [heq, Function.update_self]
    exact hvalue
  · rw [Function.update_of_ne heq]
    exact hcapacity address ha

theorem copyIndices_prefix_capacity_values (q words source target size : Nat) (hsource : target + size ≤ source)
    (rom : ROM) (indices : List Nat) (hindices : ∀ index ∈ indices, index < size) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap)
    (hvalues : ∀ node < size, state.heap (source + node) ≤ q) (count : Nat)
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
        PA17TagBridge001.copyBlock_prefix_heap rom source target index count hsmall state]
      exact hcapacity
    · obtain ⟨extra, heq⟩ := Nat.exists_eq_add_of_le (show 4 ≤ count by omega)
      rw [heq, List.take_append, List.take_of_length_le (by rw [hlen]; omega), hlen,
        Nat.add_sub_cancel_left, IndexedRAM.execute_append]
      have hvalues' : ∀ node < size,
          (IndexedRAM.execute rom (IndexedCellRAM.copyBlock source target index) state).heap (source + node) ≤ q := by
        intro node hn
        rw [IndexedCellRAM.execute_copyBlock_heap, Function.update_of_ne (by
          have := hindices index List.mem_cons_self
          omega)]
        exact hvalues node hn
      have hcount' : extra ≤ (IndexedCellRAM.copyIndices source target later).length := by
        rw [List.length_append, hlen] at hc
        simpa only [IndexedCellRAM.copyIndices] using
          (show extra ≤ (List.flatMap (IndexedCellRAM.copyBlock source target) later).length by omega)
      exact ih (fun node hn => hindices node (List.mem_cons_of_mem _ hn)) _
        (copyBlock_capacity_values q words source target index rom state hcapacity
          (hvalues index (hindices index List.mem_cons_self))) hvalues' extra hcount'

theorem copyWords_capacityThroughout_values (q words source target size : Nat) (hsource : target + size ≤ source)
    (rom : PhysicalROM) (state : State) (hcapacity : CapacityPrefixBounded q words state.heap)
    (hvalues : ∀ node < size, state.heap (source + node) ≤ q) :
    CapacityThroughout q words rom ((IndexedCellRAM.copyWords source target size).map Op.base) state := by
  intro count hc
  rw [← List.map_take, execute_base]
  exact copyIndices_prefix_capacity_values q words source target size hsource rom.semantic (List.range size)
    (fun _ hm => List.mem_range.mp hm) state hcapacity hvalues count
      (by simpa only [List.length_map, IndexedCellRAM.copyWords] using hc)

theorem constantTag_capacityThroughout (q words target : Nat) (hq : 0 < q) (rom : PhysicalROM)
    (state : State) (hcapacity : CapacityPrefixBounded q words state.heap) :
    CapacityThroughout q words rom ((IndexedCellRAM.constantBlock target 1).map Op.base) state := by
  intro count hc address ha
  change count ≤ 3 at hc
  have htag : Function.update state.heap target 1 address ≤ q := by
    by_cases heq : address = target
    · rw [heq, Function.update_self]
      exact hq
    · rw [Function.update_of_ne heq]
      exact hcapacity address ha
  interval_cases count <;> first
    | exact hcapacity address ha
    | exact htag

theorem writeFreeSlot_capacityThroughout (q words size metadataBase slot : Nat) (hq : 0 < q)
    (hslot : (slot + 1) * (size + 1) ≤ metadataBase) (rom : PhysicalROM) (state : State)
    (hcapacity : CapacityPrefixBounded q words state.heap)
    (hvalues : ∀ node < size, state.heap (metadataBase + node) ≤ q) :
    CapacityThroughout q words rom (writeFreeSlot size metadataBase slot) state := by
  rw [writeFreeSlot]
  have hh : slotBase size slot + 1 + size ≤ metadataBase := by
    dsimp [slotBase]
    rw [Nat.add_mul] at hslot
    omega
  have hl := copyWords_capacityThroughout_values q words metadataBase (slotBase size slot + 1) size hh
    rom state hcapacity hvalues
  apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hl
  apply constantTag_capacityThroughout q words (slotBase size slot) hq rom
  simpa only [List.take_length] using hl _ le_rfl

theorem freeSlots_capacityThroughout (q words size metadataBase : Nat) (hq : 0 < q)
    (rom : PhysicalROM) (slots : List Nat)
    (hslots : ∀ slot ∈ slots, (slot + 1) * (size + 1) ≤ metadataBase)
    (state : State) (hcapacity : CapacityPrefixBounded q words state.heap)
    (hvalues : ∀ node < size, state.heap (metadataBase + node) ≤ q) :
    CapacityThroughout q words rom (freeSlots size metadataBase slots) state := by
  induction slots generalizing state with
  | nil => intro count _; simpa only [freeSlots, List.flatMap_nil, List.take_nil, IndexedClosureRAM.execute] using hcapacity
  | cons slot later ih =>
    have hslot := hslots slot List.mem_cons_self
    have hl := writeFreeSlot_capacityThroughout q words size metadataBase slot hq hslot rom state hcapacity hvalues
    rw [freeSlots, List.flatMap_cons]
    apply UniformFreeTableSafety.capacityThroughout_append q words rom _ _ state hl
    apply ih (fun s hs => hslots s (List.mem_cons_of_mem _ hs)) _
      (by simpa only [List.take_length] using hl _ le_rfl)
    intro node hn
    rw [writeFreeSlot_frame rom.semantic size metadataBase slot state (metadataBase + node) (by
      intro index hi
      dsimp [slotBase]
      rw [Nat.add_mul] at hslot
      omega)]
    exact hvalues node hn

theorem prepared_program_capacityThroughout (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State)
    (hcapacity : CapacityPrefixBounded q (tableWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    let cache := (prepareNormalization q full).indexed
    CapacityThroughout q (tableWords full.length q cache.nodes.size) (givenTreeROM q full)
      (program full.length q cache.nodes.size) state := by
  intro cache
  rw [program]
  have hl := UniformFreeTableSafety.metadataProgram_capacityThroughout q
    (tableWords full.length q cache.nodes.size) (givenTreeROM q full) full.length q cache.nodes.size
    (tableWords full.length q cache.nodes.size) le_rfl state hcapacity
  apply UniformFreeTableSafety.capacityThroughout_append q _ (givenTreeROM q full) _ _ state hl
  apply freeSlots_capacityThroughout q _ _ _ hq (givenTreeROM q full) (seedSlots full.length q)
    (seedSlots_words_bound full.length q cache.nodes.size) _
    (by simpa only [List.take_length] using hl _ le_rfl)
  intro node hn
  exact UniformTreeMetadataRAM.metadata_card_bound q full _ _
    (UniformTreeMetadataRAM.prepared_program_metadata q full hq hlaminar _ state) ⟨node, hn⟩

theorem program_unseeded_frame (rom : ROM) (N q size : Nat) (state : State) (address : Nat)
    (ha : address < tableWords N q size)
    (hframe : ∀ slot ∈ seedSlots N q, ∀ index ≤ size, address ≠ slotBase size slot + index) :
    (execute rom (program N q size) state).heap address = state.heap address := by
  rw [program, IndexedClosureRAM.execute_append, freeSlots_frame rom size _ _ _ address hframe]
  exact UniformTreeMetadataRAM.program_frame rom N q size _ state address (Or.inl ha)

theorem program_outside_frame (rom : ROM) (N q size : Nat) (state : State) (address : Nat)
    (ha : tableWords N q size + 3 * size < address) :
    (execute rom (program N q size) state).heap address = state.heap address := by
  rw [program, IndexedClosureRAM.execute_append,
    freeSlots_metadata_frame rom size _ _ (seedSlots_words_bound N q size) _ address (by omega)]
  exact UniformTreeMetadataRAM.program_frame rom N q size _ state address (Or.inr ha)

theorem prepared_halting_run (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (state : State) (hpc : state.pc = 0)
    (hcapacity : CapacityPrefixBounded q (tableWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    let cache := (prepareNormalization q full).indexed
    ∃ final operations,
      HaltingRuns (givenTreeROM q full).semantic (program full.length q cache.nodes.size) state final operations ∧
      (∀ stage : Fin (full.length + 1), readEntry cache.nodes.size (stage.val * (q + 2)) final.heap =
        (IndexedQuery.storedPositiveRow q full stage).get ⟨0, by omega⟩) ∧
      (∀ budget : Fin (q + 2), readEntry cache.nodes.size (full.length * (q + 2) + budget.val) final.heap =
        (IndexedQuery.storedPositiveRow q full ⟨full.length, by omega⟩).get budget) ∧
      UniformTreeMetadataRAM.MetadataCorrect q full (tableWords full.length q cache.nodes.size) final.heap ∧
      CapacityThroughout q (tableWords full.length q cache.nodes.size) (givenTreeROM q full)
        (program full.length q cache.nodes.size) state ∧
      operations.length ≤ 359 * (full.length + q + 1) * cache.nodes.size := by
  intro cache
  obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
  have hsize : 0 < cache.nodes.size := Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  exact ⟨_, _, execute_halts _ _ state hpc, prepared_program_budgetZero_stored q full hq hlaminar state,
    prepared_program_terminal_stored q full hq hlaminar state, prepared_program_metadata q full hq hlaminar state,
    prepared_program_capacityThroughout q full hq hlaminar state hcapacity, program_trace_le full.length q cache.nodes.size hsize⟩

end PaperProofs.Structure.LaminarTree.PA17TerminalRow002
