module

public import PaperProofs.Structure.IndexedIntersectionRAM

/-!
Raw eligibility incidence words are read by an actual charged program. A
singleton in the set is selected during the same scan that counts its size;
then parent pointers are followed until that size identifies the tree node.
No set lookup, cardinality scan or ancestor operation is a RAM primitive.
Shared static metadata preparation and finite-word packing remain separate.
-/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.IndexedRawClosureRAM

open IndexedRAM IndexedClosureRAM

abbrev rawROM := IndexedIntersectionRAM.rawExtensionROM

variable {Tool : Type*}

def scanBlock (size tool : Nat) : List Op :=
  [.base (.constant .index (size + 1 + tool)), .base (.loadROM .input .value .index),
    .base (.add .total .total .value), .base (.constant .index (2 * size + tool)),
    .base (.loadROM .internal .fresh .index), .base (.select .address .value .fresh .address)]

def scanInit : List Op := [.base (.constant .address 0), .base (.constant .total 0)]

def scanPass (size q : Nat) : List Op :=
  (List.finRange q).flatMap (fun tool => scanBlock size tool.val)

structure ScanState (q : Nat) where
  count : Nat
  selected : Option (Fin q)

def scanStep {q : Nat} (eligible : Finset (Fin q)) (tool : Fin q) (state : ScanState q) : ScanState q :=
  if tool ∈ eligible then ⟨state.count + 1, some tool⟩ else state

def scanTools {q : Nat} (eligible : Finset (Fin q)) : List (Fin q) → ScanState q → ScanState q
  | [], state => state
  | tool :: later, state => scanTools eligible later (scanStep eligible tool state)

def singletonCode (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) : Option (Fin q) → Nat
  | none => 0
  | some tool => (((IndexedStaticMetadata.buildPositive q full hq).toolNodes).get tool).val + 1

theorem scanBlock_length (size tool : Nat) : (scanBlock size tool).length = 6 := rfl

theorem scanBlock_trace_length (size tool : Nat) : (trace (scanBlock size tool)).length = 61 := rfl

theorem scanInit_trace_length : (trace scanInit).length = 16 := rfl

theorem execute_scanBlock_heap (rom : ROM) (size tool : Nat) (state : State) :
    (execute rom (scanBlock size tool) state).heap = state.heap := rfl

theorem execute_scanBlock_count (rom : ROM) (size tool : Nat) (state : State) :
    (execute rom (scanBlock size tool) state).register .total =
      state.register .total + rom.read .input (size + 1 + tool) := rfl

theorem execute_scanBlock_address (rom : ROM) (size tool : Nat) (state : State) :
    (execute rom (scanBlock size tool) state).register .address =
      if rom.read .input (size + 1 + tool) = 0 then state.register .address
        else rom.read .internal (2 * size + tool) := rfl

theorem execute_scanInit_heap (rom : ROM) (state : State) :
    (execute rom scanInit state).heap = state.heap := rfl

theorem execute_scanInit_count (rom : ROM) (state : State) :
    (execute rom scanInit state).register .total = 0 := rfl

theorem execute_scanInit_address (rom : ROM) (state : State) :
    (execute rom scanInit state).register .address = 0 := rfl

theorem rawROM_bit (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (tool : Fin q) :
    (rawROM q full hq entry eligible).read .input ((prepareNormalization q full).indexed.nodes.size + 1 + tool.val) =
      if tool ∈ eligible then 1 else 0 := by
  have hn : ¬(prepareNormalization q full).indexed.nodes.size + 1 + tool.val <
      (prepareNormalization q full).indexed.nodes.size := by omega
  have he : (prepareNormalization q full).indexed.nodes.size + 1 + tool.val ≠
      (prepareNormalization q full).indexed.nodes.size := by omega
  have hb : (prepareNormalization q full).indexed.nodes.size + 1 ≤
      (prepareNormalization q full).indexed.nodes.size + 1 + tool.val ∧
      (prepareNormalization q full).indexed.nodes.size + 1 + tool.val <
        (prepareNormalization q full).indexed.nodes.size + 1 + q := ⟨by omega, by have := tool.isLt; omega⟩
  simp only [rawROM, IndexedIntersectionRAM.rawExtensionROM, hn, he, ↓reduceIte, hb, Nat.add_sub_cancel_left]
  simp

theorem rawROM_singleton (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (tool : Fin q) :
    (rawROM q full hq entry eligible).read .internal (2 * (prepareNormalization q full).indexed.nodes.size + tool.val) =
      singletonCode q full hq (some tool) := by
  have hn : ¬2 * (prepareNormalization q full).indexed.nodes.size + tool.val <
      (prepareNormalization q full).indexed.nodes.size := by omega
  have hb : 2 * (prepareNormalization q full).indexed.nodes.size ≤
      2 * (prepareNormalization q full).indexed.nodes.size + tool.val ∧
      2 * (prepareNormalization q full).indexed.nodes.size + tool.val <
        2 * (prepareNormalization q full).indexed.nodes.size + q := ⟨by omega, by have := tool.isLt; omega⟩
  simp only [rawROM, IndexedIntersectionRAM.rawExtensionROM, hn, ↓reduceDIte, hb, Nat.add_sub_cancel_left, singletonCode]
  simp

theorem rawROM_cardinality (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (node : (prepareNormalization q full).indexed.NodeId) :
    (rawROM q full hq entry eligible).read .internal node.val =
      ((prepareNormalization q full).indexed.decode node).card := by
  simp only [rawROM, IndexedIntersectionRAM.rawExtensionROM, node.isLt, ↓reduceDIte, metadata_cardinality]

theorem rawROM_parent (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q)) :
    ParentROMFor (prepareNormalization q full).indexed 0 (rawROM q full hq entry eligible) := by
  constructor
  · change (parentWords (prepareNormalization q full).indexed).getD 0 0 = 0
    rw [parentWords_get _ 0 (by omega), parentWord_zero]
  · intro node
    change (parentWords (prepareNormalization q full).indexed).getD (0 + (node.val + 1)) 0 = _
    rw [Nat.zero_add, parentWords_get _ _ (by have := node.isLt; omega), parentWord_node]

theorem scanBlock_represents (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (tool : Fin q) (machine : State) (value : ScanState q)
    (hcount : machine.register .total = value.count)
    (hselected : machine.register .address = singletonCode q full hq value.selected) :
    (execute (rawROM q full hq entry eligible) (scanBlock (prepareNormalization q full).indexed.nodes.size tool.val) machine).register .total =
        (scanStep eligible tool value).count ∧
      (execute (rawROM q full hq entry eligible) (scanBlock (prepareNormalization q full).indexed.nodes.size tool.val) machine).register .address =
        singletonCode q full hq (scanStep eligible tool value).selected := by
  rw [execute_scanBlock_count, execute_scanBlock_address, rawROM_bit, rawROM_singleton, hcount, hselected]
  by_cases hm : tool ∈ eligible <;> simp only [scanStep, hm, ↓reduceIte, Nat.add_zero, Nat.one_ne_zero, and_self]

theorem scanTools_represents (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (tools : List (Fin q)) (machine : State) (value : ScanState q)
    (hcount : machine.register .total = value.count)
    (hselected : machine.register .address = singletonCode q full hq value.selected) :
    (execute (rawROM q full hq entry eligible)
      (tools.flatMap (fun tool => scanBlock (prepareNormalization q full).indexed.nodes.size tool.val)) machine).register .total =
        (scanTools eligible tools value).count ∧
      (execute (rawROM q full hq entry eligible)
        (tools.flatMap (fun tool => scanBlock (prepareNormalization q full).indexed.nodes.size tool.val)) machine).register .address =
        singletonCode q full hq (scanTools eligible tools value).selected := by
  induction tools generalizing machine value with
  | nil => exact ⟨hcount, hselected⟩
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append]
    have hstep := scanBlock_represents q full hq entry eligible tool machine value hcount hselected
    exact ih _ _ hstep.1 hstep.2

theorem scanTools_count {q : Nat} (eligible : Finset (Fin q)) (tools : List (Fin q)) (value : ScanState q) :
    (scanTools eligible tools value).count = value.count + (tools.filter (fun tool => decide (tool ∈ eligible))).length := by
  induction tools generalizing value with
  | nil => simp only [scanTools, List.filter_nil, List.length_nil, Nat.add_zero]
  | cons tool later ih =>
    rw [scanTools, ih]
    by_cases hm : tool ∈ eligible <;> simp [scanStep, hm]
    omega

theorem scanTools_selected_none_iff {q : Nat} (eligible : Finset (Fin q)) (tools : List (Fin q)) (value : ScanState q) :
    (scanTools eligible tools value).selected = none ↔ value.selected = none ∧ ∀ tool ∈ tools, tool ∉ eligible := by
  induction tools generalizing value with
  | nil => simp only [scanTools, List.not_mem_nil, false_implies, implies_true, and_true]
  | cons tool later ih =>
    rw [scanTools, ih]
    by_cases hm : tool ∈ eligible
    · simp only [scanStep, hm, ↓reduceIte, reduceCtorEq, false_and, List.mem_cons]
      constructor
      · intro h; exact False.elim h
      · rintro ⟨_, h⟩; exact h tool (Or.inl rfl) hm
    · simp only [scanStep, hm, ↓reduceIte, List.mem_cons]
      constructor
      · rintro ⟨hv, ht⟩
        exact ⟨hv, fun other ho => (Or.elim ho (fun he => he ▸ hm) (fun hh => ht other hh))⟩
      · rintro ⟨hv, ht⟩
        exact ⟨hv, fun other ho => ht other (Or.inr ho)⟩

theorem scanTools_selected_mem {q : Nat} (eligible : Finset (Fin q)) (tools : List (Fin q)) (value : ScanState q)
    (hvalue : ∀ tool, value.selected = some tool → tool ∈ eligible) :
    ∀ tool, (scanTools eligible tools value).selected = some tool → tool ∈ eligible := by
  induction tools generalizing value with
  | nil => exact hvalue
  | cons tool later ih =>
    apply ih (scanStep eligible tool value)
    intro other ho
    by_cases hm : tool ∈ eligible
    · have he : tool = other := by simpa only [scanStep, hm, ↓reduceIte, Option.some.injEq] using ho
      exact he ▸ hm
    · exact hvalue other (by simpa only [scanStep, hm, ↓reduceIte] using ho)

theorem finRange_filter_length (q : Nat) (eligible : Finset (Fin q)) :
    ((List.finRange q).filter (fun tool => decide (tool ∈ eligible))).length = eligible.card := by
  have hn := (List.nodup_finRange q).filter (fun tool => decide (tool ∈ eligible))
  have hs : ((List.finRange q).filter (fun tool => decide (tool ∈ eligible))).toFinset = eligible := by
    ext tool
    simp only [List.mem_toFinset, List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]
  rw [← List.toFinset_card_of_nodup hn, hs]

def searchBlock : List Op :=
  [.base (.constant .index 1), .subtract .index .address .index,
    .base (.loadROM .internal .old .index), .subtract .value .old .total,
    .subtract .fresh .total .old, .base (.add .value .value .fresh),
    .base (.select .fresh .value .flag .address), .base (.select .flag .address .fresh .flag),
    .base (.loadROM .children .address .address)]

def searchLoop (fuel : Nat) : List Op := (List.replicate fuel searchBlock).flatten

structure SearchState (cache : IndexedNodeCache Tool) where
  current : Option cache.NodeId
  found : Option cache.NodeId

def searchStep [DecidableEq Tool] (cache : IndexedNodeCache Tool) (goal : Nat)
    (value : SearchState cache) : SearchState cache :=
  match value.current with
  | none => value
  | some node => ⟨cache.parents.get node,
      if (cache.decode node).card = goal then some node else value.found⟩

def searchWalk [DecidableEq Tool] (cache : IndexedNodeCache Tool) (goal : Nat) :
    Nat → SearchState cache → SearchState cache
  | 0, value => value
  | fuel + 1, value => searchWalk cache goal fuel (searchStep cache goal value)

def SearchRepresents (cache : IndexedNodeCache Tool) (goal : Nat) (machine : State)
    (value : SearchState cache) : Prop :=
  machine.register .address = encodedNode cache value.current ∧
    machine.register .flag = encodedNode cache value.found ∧ machine.register .total = goal

theorem searchBlock_length : searchBlock.length = 9 := rfl

theorem searchBlock_trace_length : (trace searchBlock).length = 98 := rfl

theorem execute_searchBlock_heap (rom : ROM) (machine : State) :
    (execute rom searchBlock machine).heap = machine.heap := rfl

theorem execute_searchBlock_total (rom : ROM) (machine : State) :
    (execute rom searchBlock machine).register .total = machine.register .total := rfl

theorem execute_searchBlock_address (rom : ROM) (machine : State) :
    (execute rom searchBlock machine).register .address = rom.read .children (machine.register .address) := rfl

theorem execute_searchBlock_flag (rom : ROM) (machine : State) :
    (execute rom searchBlock machine).register .flag =
      if machine.register .address = 0 then machine.register .flag else
        if (rom.read .internal (machine.register .address - 1) - machine.register .total) +
            (machine.register .total - rom.read .internal (machine.register .address - 1)) = 0
        then machine.register .address else machine.register .flag := rfl

theorem searchBlock_represents (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (goal : Nat) (machine : State) (value : SearchState (prepareNormalization q full).indexed)
    (hvalue : SearchRepresents (prepareNormalization q full).indexed goal machine value) :
    SearchRepresents (prepareNormalization q full).indexed goal
      (execute (rawROM q full hq entry eligible) searchBlock machine)
      (searchStep (prepareNormalization q full).indexed goal value) := by
  obtain ⟨ha, hf, ht⟩ := hvalue
  have hp := rawROM_parent q full hq entry eligible
  cases hc : value.current with
  | none =>
    have haz : machine.register .address = 0 := ha.trans (by rw [hc]; rfl)
    refine ⟨?_, ?_, ?_⟩
    · rw [execute_searchBlock_address, haz]
      simpa only [Nat.zero_add, searchStep, hc, encodedNode] using hp.1
    · rw [execute_searchBlock_flag, haz, ite_eq_left rfl]
      simpa only [searchStep, hc] using hf
    · exact (execute_searchBlock_total _ machine).trans ht
  | some node =>
    have han : machine.register .address = node.val + 1 := ha.trans (by rw [hc]; rfl)
    refine ⟨?_, ?_, ?_⟩
    · rw [execute_searchBlock_address, han]
      simpa only [Nat.zero_add, searchStep, hc] using hp.2 node
    · rw [execute_searchBlock_flag, han, hf, ht, Nat.add_sub_cancel, rawROM_cardinality]
      have hnz : node.val + 1 ≠ 0 := by omega
      rw [ite_eq_right hnz]
      by_cases hg : ((prepareNormalization q full).indexed.decode node).card = goal
      · have hz : (((prepareNormalization q full).indexed.decode node).card - goal) +
            (goal - ((prepareNormalization q full).indexed.decode node).card) = 0 := by omega
        rw [ite_eq_left hz]
        simp only [searchStep, hc, hg, ite_true, encodedNode]
      · have hz : (((prepareNormalization q full).indexed.decode node).card - goal) +
            (goal - ((prepareNormalization q full).indexed.decode node).card) ≠ 0 := by omega
        rw [ite_eq_right hz]
        simp only [searchStep, hc, hg, ite_false]
    · exact (execute_searchBlock_total _ machine).trans ht

theorem searchLoop_represents (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (goal fuel : Nat) (machine : State) (value : SearchState (prepareNormalization q full).indexed)
    (hvalue : SearchRepresents (prepareNormalization q full).indexed goal machine value) :
    SearchRepresents (prepareNormalization q full).indexed goal
      (execute (rawROM q full hq entry eligible) (searchLoop fuel) machine)
      (searchWalk (prepareNormalization q full).indexed goal fuel value) := by
  induction fuel generalizing machine value with
  | zero => exact hvalue
  | succ fuel ih =>
    rw [searchLoop, List.replicate_succ, List.flatten_cons, IndexedClosureRAM.execute_append]
    exact ih _ _ (searchBlock_represents q full hq entry eligible goal machine value hvalue)

theorem searchWalk_none [DecidableEq Tool] (cache : IndexedNodeCache Tool) (goal fuel : Nat)
    (value : SearchState cache) (hn : value.current = none) : searchWalk cache goal fuel value = value := by
  induction fuel with
  | zero => rfl
  | succ fuel ih => simpa only [searchWalk, searchStep, hn] using ih

def searchFold [DecidableEq Tool] (cache : IndexedNodeCache Tool) (goal : Nat) :
    List cache.NodeId → Option cache.NodeId → Option cache.NodeId
  | [], found => found
  | node :: later, found => searchFold cache goal later
      (if (cache.decode node).card = goal then some node else found)

theorem searchWalk_found [DecidableEq Tool] (cache : IndexedNodeCache Tool) (goal fuel : Nat)
    (node : cache.NodeId) (found : Option cache.NodeId) :
    (searchWalk cache goal fuel (⟨some node, found⟩ : SearchState cache)).found =
      searchFold cache goal (IndexedAncestors.parentChain cache fuel node) found := by
  induction fuel generalizing node found with
  | zero => rfl
  | succ fuel ih =>
    cases hp : cache.parents.get node with
    | none =>
      rw [searchWalk]
      have hc : (searchStep cache goal (⟨some node, found⟩ : SearchState cache)).current = none := hp
      rw [searchWalk_none cache goal fuel _ hc]
      simp only [searchStep, IndexedAncestors.parentChain, hp, searchFold]
    | some parent =>
      simpa only [searchWalk, searchStep, IndexedAncestors.parentChain, hp, searchFold] using
        ih parent (if (cache.decode node).card = goal then some node else found)

theorem searchFold_no_hit [DecidableEq Tool] (cache : IndexedNodeCache Tool) (goal : Nat)
    (nodes : List cache.NodeId) (found : Option cache.NodeId)
    (hno : ∀ node ∈ nodes, (cache.decode node).card ≠ goal) :
    searchFold cache goal nodes found = found := by
  induction nodes generalizing found with
  | nil => rfl
  | cons node later ih =>
    rw [searchFold, ite_eq_right (hno node List.mem_cons_self)]
    exact ih found (fun other ho => hno other (List.mem_cons_of_mem node ho))

theorem searchFold_unique [DecidableEq Tool] (cache : IndexedNodeCache Tool) (goal : Nat)
    (nodes : List cache.NodeId) (target : cache.NodeId) (found : Option cache.NodeId)
    (hmem : target ∈ nodes) (hgoal : (cache.decode target).card = goal)
    (honly : ∀ node ∈ nodes, (cache.decode node).card = goal → node = target) :
    searchFold cache goal nodes found = some target := by
  induction nodes generalizing found with
  | nil => cases hmem
  | cons node later ih =>
    by_cases ht : target ∈ later
    · rw [searchFold]
      exact ih _ ht (fun other ho => honly other (List.mem_cons_of_mem node ho))
    · have he : target = node := (List.mem_cons.mp hmem).resolve_right ht
      subst node
      rw [searchFold, ite_eq_left hgoal]
      apply searchFold_no_hit
      intro other ho hg
      exact ht ((honly other (List.mem_cons_of_mem target ho) hg) ▸ ho)

theorem prepared_search_target (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible ∈ nodeFamily full) (tool : Fin q) (htool : tool ∈ eligible)
    (target : (prepareNormalization q full).indexed.NodeId)
    (htarget : (prepareNormalization q full).indexed.decode target = eligible) :
    let leaf := ((IndexedStaticMetadata.buildPositive q full hq).toolNodes).get tool
    (searchWalk (prepareNormalization q full).indexed eligible.card
      (prepareNormalization q full).indexed.nodes.size (⟨some leaf, none⟩ : SearchState _)).found = some target := by
  dsimp only
  rw [searchWalk_found]
  apply searchFold_unique
  · apply (IndexedAncestors.prepared_ancestorChain_mem_iff q full hq hlaminar _ target).mpr
    rw [IndexedStaticMetadata.buildPositive_tool_decode, htarget]
    exact Finset.singleton_subset_iff.mpr htool
  · exact congrArg Finset.card htarget
  · intro node hn hcard
    have hsub := (IndexedAncestors.prepared_ancestorChain_mem_iff q full hq hlaminar _ node).mp hn
    rw [IndexedStaticMetadata.buildPositive_tool_decode] at hsub
    have hnTool : tool ∈ (prepareNormalization q full).indexed.decode node :=
      (Finset.singleton_subset_iff.mp hsub)
    apply prepared_indexed_decode_injective q full
    rw [htarget]
    rcases nodeFamily_laminar full hlaminar _ (prepared_indexed_node_mem q full node) eligible heligible with hd | hs | hs
    · exact False.elim ((Finset.disjoint_left.mp hd) hnTool htool)
    · exact Finset.eq_of_subset_of_card_le hs hcard.ge
    · exact (Finset.eq_of_subset_of_card_le hs hcard.le).symm

def fullScan {q : Nat} (eligible : Finset (Fin q)) : ScanState q :=
  scanTools eligible (List.finRange q) ⟨0, none⟩

theorem fullScan_count (q : Nat) (eligible : Finset (Fin q)) : (fullScan eligible).count = eligible.card := by
  rw [fullScan, scanTools_count, finRange_filter_length, Nat.zero_add]

theorem fullScan_selected_none_iff (q : Nat) (eligible : Finset (Fin q)) :
    (fullScan eligible).selected = none ↔ eligible = ∅ := by
  rw [fullScan, scanTools_selected_none_iff]
  simp only [true_and]
  constructor
  · intro h
    exact Finset.eq_empty_of_forall_notMem (fun tool ht => h tool (List.mem_finRange tool) ht)
  · intro he tool _
    rw [he]
    exact Finset.notMem_empty tool

theorem fullScan_selected_mem (q : Nat) (eligible : Finset (Fin q)) (tool : Fin q)
    (h : (fullScan eligible).selected = some tool) : tool ∈ eligible :=
  scanTools_selected_mem eligible (List.finRange q) (⟨0, none⟩ : ScanState q)
    (fun (_other : Fin q) (hh : (none : Option (Fin q)) = some _other) => by cases hh) tool h

theorem execute_scanTools_heap (rom : ROM) (size q : Nat) (tools : List (Fin q)) (machine : State) :
    (execute rom (tools.flatMap (fun tool => scanBlock size tool.val)) machine).heap = machine.heap := by
  induction tools generalizing machine with
  | nil => rfl
  | cons tool later ih =>
    rw [List.flatMap_cons, IndexedClosureRAM.execute_append, ih, execute_scanBlock_heap]

def flagReset : List Op := [.base (.constant .flag 0)]

theorem execute_flagReset_heap (rom : ROM) (machine : State) :
    (execute rom flagReset machine).heap = machine.heap := rfl

theorem execute_flagReset_address (rom : ROM) (machine : State) :
    (execute rom flagReset machine).register .address = machine.register .address := rfl

theorem execute_flagReset_total (rom : ROM) (machine : State) :
    (execute rom flagReset machine).register .total = machine.register .total := rfl

theorem execute_flagReset_flag (rom : ROM) (machine : State) :
    (execute rom flagReset machine).register .flag = 0 := rfl

def locateProgram (size q : Nat) : List Op := scanInit ++ scanPass size q ++ flagReset ++ searchLoop size

def scanSearchStart (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (initial : State) : State :=
  execute (rawROM q full hq entry eligible) flagReset
    (execute (rawROM q full hq entry eligible) (scanPass (prepareNormalization q full).indexed.nodes.size q)
      (execute (rawROM q full hq entry eligible) scanInit initial))

def fullSearchStart (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (eligible : Finset (Fin q)) : SearchState (prepareNormalization q full).indexed :=
  ⟨(fullScan eligible).selected.map (fun tool => ((IndexedStaticMetadata.buildPositive q full hq).toolNodes).get tool), none⟩

theorem scanSearchStart_represents (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (initial : State) :
    SearchRepresents (prepareNormalization q full).indexed eligible.card
      (scanSearchStart q full hq entry eligible initial) (fullSearchStart q full hq eligible) := by
  let rom := rawROM q full hq entry eligible
  have hs := scanTools_represents q full hq entry eligible (List.finRange q)
    (execute rom scanInit initial) (⟨0, none⟩ : ScanState q)
      (execute_scanInit_count rom initial) (execute_scanInit_address rom initial)
  refine ⟨?_, ?_, ?_⟩
  · calc
      _ = (execute rom (scanPass (prepareNormalization q full).indexed.nodes.size q) (execute rom scanInit initial)).register .address :=
        execute_flagReset_address _ _
      _ = singletonCode q full hq (fullScan eligible).selected := hs.2
      _ = _ := by
        change singletonCode q full hq (fullScan eligible).selected =
          encodedNode (prepareNormalization q full).indexed
            ((fullScan eligible).selected.map (fun tool => ((IndexedStaticMetadata.buildPositive q full hq).toolNodes).get tool))
        cases (fullScan eligible).selected <;> rfl
  · exact execute_flagReset_flag _ _
  · exact (execute_flagReset_total _ _).trans (hs.1.trans (fullScan_count q eligible))

/-- Specification only. The program obtains this node from raw incidence
bits; this search function is not evaluated in its input ROM or code. -/
def supportNode {Tool : Type*} [DecidableEq Tool] (cache : IndexedNodeCache Tool)
    (eligible : Finset Tool) : Option cache.NodeId :=
  if eligible = ∅ then none else findNodeId cache.nodes eligible

theorem prepared_fullSearch_found (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full) :
    (searchWalk (prepareNormalization q full).indexed eligible.card (prepareNormalization q full).indexed.nodes.size
      (fullSearchStart q full hq eligible)).found = supportNode (prepareNormalization q full).indexed eligible := by
  cases hc : (fullScan eligible).selected with
  | none =>
    have he := (fullScan_selected_none_iff q eligible).mp hc
    have hn : (fullSearchStart q full hq eligible).current = none := by simp only [fullSearchStart, hc, Option.map_none]
    rw [searchWalk_none _ _ _ _ hn]
    simp only [fullSearchStart, supportNode, he, ite_true]
  | some tool =>
    have ht := fullScan_selected_mem q eligible tool hc
    have he : eligible ≠ ∅ := by intro hz; exact (Finset.notMem_empty tool) (hz ▸ ht)
    have hmem := heligible.resolve_left he
    obtain ⟨target, htarget⟩ := prepared_indexed_node_exists q full eligible hmem
    have hfind := (findNodeId_eq_some_iff _ (prepared_indexed_nodes_nodup q full) eligible target).mpr htarget
    have hs := prepared_search_target q full hq hlaminar eligible hmem tool ht target htarget
    simpa only [fullSearchStart, hc, Option.map_some, supportNode, he, ite_false, hfind] using hs

theorem execute_locate_found (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full) (initial : State) :
    (execute (rawROM q full hq entry eligible) (locateProgram (prepareNormalization q full).indexed.nodes.size q) initial).register .flag =
      encodedNode (prepareNormalization q full).indexed (supportNode (prepareNormalization q full).indexed eligible) := by
  have hr := searchLoop_represents q full hq entry eligible eligible.card (prepareNormalization q full).indexed.nodes.size
    (scanSearchStart q full hq entry eligible initial) (fullSearchStart q full hq eligible)
    (scanSearchStart_represents q full hq entry eligible initial)
  have hf := hr.2.1
  rw [prepared_fullSearch_found q full hq hlaminar eligible heligible] at hf
  simpa only [locateProgram, IndexedClosureRAM.execute_append, scanSearchStart] using hf

theorem execute_searchLoop_heap (rom : ROM) (fuel : Nat) (initial : State) :
    (execute rom (searchLoop fuel) initial).heap = initial.heap := by
  induction fuel generalizing initial with
  | zero => rfl
  | succ fuel ih =>
    rw [searchLoop, List.replicate_succ, List.flatten_cons, IndexedClosureRAM.execute_append]
    change (execute rom (searchLoop fuel) (execute rom searchBlock initial)).heap = initial.heap
    rw [ih, execute_searchBlock_heap]

theorem execute_locate_heap (q size : Nat) (rom : ROM) (initial : State) :
    (execute rom (locateProgram size q) initial).heap = initial.heap := by
  simp only [locateProgram, IndexedClosureRAM.execute_append, execute_searchLoop_heap,
    execute_flagReset_heap, scanPass, execute_scanTools_heap, execute_scanInit_heap]

def readyProgram (size : Nat) : List Op :=
  [.base (.constant .old 0), .base (.add .address .flag .old),
    .base (.constant .index size), .base (.loadROM .input .flag .index),
    .base (.select .flag .address .flag .old), .base (.constant .total 1)]

def rawExtensionProgram (size q : Nat) : List Op :=
  (copyProgram size).map Op.base ++ locateProgram size q ++ readyProgram size ++
    ancestorLoop 0 size ++ extensionTail size

theorem execute_readyProgram_heap (rom : ROM) (size : Nat) (machine : State) :
    (execute rom (readyProgram size) machine).heap = machine.heap := rfl

theorem execute_readyProgram_address (rom : ROM) (size : Nat) (machine : State) :
    (execute rom (readyProgram size) machine).register .address = machine.register .flag := rfl

theorem execute_readyProgram_total (rom : ROM) (size : Nat) (machine : State) :
    (execute rom (readyProgram size) machine).register .total = 1 := rfl

theorem execute_readyProgram_flag (rom : ROM) (size : Nat) (machine : State) :
    (execute rom (readyProgram size) machine).register .flag =
      if machine.register .flag = 0 then 0 else rom.read .input size := rfl

theorem readyProgram_length (size : Nat) : (readyProgram size).length = 6 := rfl

theorem readyProgram_trace_length (size : Nat) : (trace (readyProgram size)).length = 58 := rfl

def rawStart (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (initial : State) : State :=
  let rom := rawROM q full hq entry eligible
  execute rom (readyProgram (prepareNormalization q full).indexed.nodes.size)
    (execute rom (locateProgram (prepareNormalization q full).indexed.nodes.size q)
      (IndexedRAM.execute rom (copyProgram (prepareNormalization q full).indexed.nodes.size) initial))

theorem rawROM_input_payload (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (node : Option (prepareNormalization q full).indexed.NodeId) (index : Nat)
    (hi : index < (prepareNormalization q full).indexed.nodes.size) :
    (rawROM q full hq entry eligible).read .input index =
      (extensionROM (prepareNormalization q full).indexed entry node).read .input index := by
  simp only [rawROM, IndexedIntersectionRAM.rawExtensionROM, extensionROM, entryWord, hi, ↓reduceDIte]
  cases entry <;> simp only [IndexedIntersectionRAM.payload, hi, ↓reduceDIte, ite_true]

theorem rawROM_input_tag (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q)) :
    (rawROM q full hq entry eligible).read .input (prepareNormalization q full).indexed.nodes.size =
      IndexedIntersectionRAM.tag (prepareNormalization q full).indexed entry := by
  simp only [rawROM, IndexedIntersectionRAM.rawExtensionROM, Nat.lt_irrefl, ite_false, ite_true]

theorem rawStart_heap_eq (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (initial : State) :
    (rawStart q full hq entry eligible initial).heap =
      (extensionStart (prepareNormalization q full).indexed entry
        (supportNode (prepareNormalization q full).indexed eligible) initial).heap := by
  rw [rawStart, execute_readyProgram_heap, execute_locate_heap, extensionStart, extensionInit_heap]
  funext index
  rw [execute_copyProgram_heap, execute_copyProgram_heap]
  by_cases hi : index < (prepareNormalization q full).indexed.nodes.size
  · rw [ite_eq_left hi, ite_eq_left hi]
    exact rawROM_input_payload q full hq entry eligible _ index hi
  · rw [ite_eq_right hi, ite_eq_right hi]

theorem rawStart_registers (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full) (initial : State) :
    let node := supportNode (prepareNormalization q full).indexed eligible
    (rawStart q full hq entry eligible initial).register .address = encodedNode (prepareNormalization q full).indexed node ∧
      (rawStart q full hq entry eligible initial).register .total = 1 ∧
      (rawStart q full hq entry eligible initial).register .flag =
        if encodedNode (prepareNormalization q full).indexed node = 0 then 0 else
          IndexedIntersectionRAM.tag (prepareNormalization q full).indexed entry := by
  dsimp only
  have hf := execute_locate_found q full hq hlaminar entry eligible heligible
    (IndexedRAM.execute (rawROM q full hq entry eligible) (copyProgram (prepareNormalization q full).indexed.nodes.size) initial)
  refine ⟨?_, ?_, ?_⟩
  · exact (execute_readyProgram_address _ _ _).trans hf
  · exact execute_readyProgram_total _ _ _
  · rw [rawStart, execute_readyProgram_flag, hf, rawROM_input_tag]

theorem rawExtension_execute_split (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (initial : State) :
    execute (rawROM q full hq entry eligible) (rawExtensionProgram (prepareNormalization q full).indexed.nodes.size q) initial =
      execute (rawROM q full hq entry eligible) (extensionTail (prepareNormalization q full).indexed.nodes.size)
        (execute (rawROM q full hq entry eligible) (ancestorLoop 0 (prepareNormalization q full).indexed.nodes.size)
          (rawStart q full hq entry eligible initial)) := by
  simp only [rawExtensionProgram, IndexedClosureRAM.execute_append, execute_base, rawStart]

def rawExtensionResult (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (initial : State) : IndexedEntry.FixedEntry (prepareNormalization q full).indexed :=
  decodeResult (prepareNormalization q full).indexed
    (execute (rawROM q full hq entry eligible) (rawExtensionProgram (prepareNormalization q full).indexed.nodes.size q) initial).heap

/-- The raw program's post-lookup ancestor pass is the SAME old extension
execution at its actual found NodeId. Only heap/flag/address/one are needed;
no whole-register or precomputed-result assumption enters the proof. -/
theorem rawExtensionResult_eq_old (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full) (initial : State) :
    rawExtensionResult q full hq entry eligible initial =
      extensionResult (prepareNormalization q full).indexed entry
        (supportNode (prepareNormalization q full).indexed eligible) initial := by
  let cache := (prepareNormalization q full).indexed
  let node := supportNode cache eligible
  let before := extensionStart cache entry node initial
  let value : WalkState cache := ⟨before.heap, before.register .flag, node⟩
  have hs := extensionStart_registers cache entry node initial
  have hr := rawStart_registers q full hq hlaminar entry eligible heligible initial
  have hraw : Represents (rawStart q full hq entry eligible initial) value :=
    ⟨rawStart_heap_eq q full hq entry eligible initial,
      hr.2.2.trans hs.2.2.symm, hr.1, hr.2.1⟩
  have hold : Represents before value := ⟨rfl, rfl, hs.1, hs.2.1⟩
  have er := ancestorLoop_represents cache (rawROM q full hq entry eligible) 0 cache.nodes.size
    (rawROM_parent q full hq entry eligible) _ value hraw
  have eo := ancestorLoop_represents cache (extensionROM cache entry node) 0 cache.nodes.size
    (extensionROM_parent cache entry node) before value hold
  have hh := er.1.trans eo.1.symm
  have hf := er.2.1.trans eo.2.1.symm
  unfold rawExtensionResult extensionResult
  rw [rawExtension_execute_split, extension_execute_split, extensionTail_heap, extensionTail_heap]
  exact congrArg (decodeResult cache) (congrArg₂ (fun heap flag => Function.update heap cache.nodes.size flag) hh hf)

/-- Full raw-support output correctness. No support lookup is carried out by
ROM initialization, no entry normalization/result invariant is assumed, and
the code was selected before eligible or entry was supplied. -/
theorem prepared_rawExtensionResult_eq (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full) (initial : State) :
    rawExtensionResult q full hq entry eligible initial =
      IndexedEntry.extend (prepareNormalization q full).indexed eligible entry := by
  rw [rawExtensionResult_eq_old q full hq hlaminar entry eligible heligible initial,
    prepared_extensionResult_eq q full hq hlaminar]
  rw [supportNode, IndexedStaticMetadata.extendAt_find_eq]
  exact IndexedAncestors.prepared_chainExtend_eq q full hq hlaminar eligible heligible entry

theorem scanPass_length (size q : Nat) : (scanPass size q).length = 6 * q := by
  simp only [scanPass, List.length_flatMap, scanBlock_length, List.map_const',
    List.sum_replicate, List.length_finRange, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem scanPass_trace_length (size q : Nat) : (trace (scanPass size q)).length = 61 * q := by
  simp only [scanPass, trace, List.flatMap_assoc, List.length_flatMap]
  change ((List.finRange q).map (fun tool => (trace (scanBlock size tool.val)).length)).sum = _
  simp only [scanBlock_trace_length, List.map_const', List.sum_replicate,
    List.length_finRange, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem searchLoop_length (fuel : Nat) : (searchLoop fuel).length = 9 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [searchLoop, List.replicate_succ, List.flatten_cons, List.length_append, searchBlock_length]
    change 9 + (searchLoop fuel).length = _
    rw [ih]
    omega

theorem searchLoop_trace_length (fuel : Nat) : (trace (searchLoop fuel)).length = 98 * fuel := by
  induction fuel with
  | zero => rfl
  | succ fuel ih =>
    rw [searchLoop, List.replicate_succ, List.flatten_cons, trace_append, List.length_append,
      searchBlock_trace_length]
    change 98 + (trace (searchLoop fuel)).length = _
    rw [ih]
    omega

theorem rawExtensionProgram_length (size q : Nat) :
    (rawExtensionProgram size q).length = 23 * size + 6 * q + 11 := by
  simp only [rawExtensionProgram, locateProgram, List.length_append, List.length_map,
    copyProgram_length, scanPass_length, searchLoop_length, readyProgram_length,
    ancestorLoop_length, scanInit, flagReset, extensionTail, List.length_cons, List.length_nil]
  omega

theorem rawExtensionProgram_trace_length (size q : Nat) :
    (trace (rawExtensionProgram size q)).length = 246 * size + 61 * q + 101 := by
  have hf : (trace flagReset).length = 8 := rfl
  have ht : (trace (extensionTail size)).length = 19 := rfl
  simp only [rawExtensionProgram, locateProgram, trace_append, List.length_append,
    trace_base_length, copyProgram_trace_length, scanInit_trace_length, scanPass_trace_length,
    hf, searchLoop_trace_length, readyProgram_trace_length, ancestorLoop_trace_length, ht]
  omega

theorem prepared_q_le_nodes (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) :
    q ≤ (prepareNormalization q full).indexed.nodes.size := by
  have hinj : Function.Injective (fun tool : Fin q =>
      ((IndexedStaticMetadata.buildPositive q full hq).toolNodes).get tool) := by
    intro left right he
    have hs := congrArg (prepareNormalization q full).indexed.decode he
    rw [IndexedStaticMetadata.buildPositive_tool_decode, IndexedStaticMetadata.buildPositive_tool_decode] at hs
    exact Finset.singleton_injective hs
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj

theorem rawExtensionProgram_codeWords (size q : Nat) :
    (haltingWords (rawExtensionProgram size q)).length = 115 * size + 30 * q + 60 := by
  rw [haltingWords_length, rawExtensionProgram_length]
  omega

theorem prepared_intersection_codeWords_le (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) :
    (haltingProgramWords (IndexedIntersectionRAM.intersectionProgram (prepareNormalization q full).indexed)).length ≤
      414 * (prepareNormalization q full).indexed.nodes.size := by
  rw [haltingProgramWords_length, IndexedIntersectionRAM.intersectionProgram_length,
    prepared_indexed_edge_count q full hq hlaminar]
  have hqnodes := prepared_q_le_nodes q full hq
  omega

/-- Full raw-support extension, including the charged input scan, lookup,
ancestor operations and encoded HALT. Static preparation/finite-word packing
are still the separate original A06/A17 obligations. -/
theorem prepared_rawExtension_correct_run (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (eligible : Finset (Fin q))
    (heligible : eligible = ∅ ∨ eligible ∈ nodeFamily full)
    (entry : IndexedEntry.FixedEntry (prepareNormalization q full).indexed)
    (hnormalized : IndexedEntry.IsNormalized (prepareNormalization q full).indexed entry)
    (initial : State) (hpc : initial.pc = 0) :
    let cache := (prepareNormalization q full).indexed
    ∃ final operations,
      HaltingRuns (rawROM q full hq entry eligible) (rawExtensionProgram cache.nodes.size q) initial final operations ∧
      decodeResult cache final.heap = IndexedEntry.extend cache eligible entry ∧
      (decodeResult cache final.heap).denote cache = usedExtension eligible (entry.denote cache) ∧
      IndexedEntry.IsNormalized cache (decodeResult cache final.heap) ∧
      (decodeResult cache final.heap).Bounded q ∧ operations.length ≤ 414 * cache.nodes.size := by
  dsimp only
  have hout := prepared_rawExtensionResult_eq q full hq hlaminar entry eligible heligible initial
  change decodeResult (prepareNormalization q full).indexed
    (execute (rawROM q full hq entry eligible)
      (rawExtensionProgram (prepareNormalization q full).indexed.nodes.size q) initial).heap = _ at hout
  refine ⟨_, _, execute_halts _ _ initial hpc, hout, ?_⟩
  rw [hout]
  have hn := IndexedEntry.prepared_extend_normalized q full hq hlaminar eligible heligible entry hnormalized
  refine ⟨IndexedEntry.prepared_extend_denote q full hq hlaminar eligible heligible entry hnormalized,
    hn, IndexedEntry.prepared_normalized_bounded q full hq hlaminar _ hn, ?_⟩
  rw [List.length_append, haltTrace_length, rawExtensionProgram_trace_length]
  have hqnodes := prepared_q_le_nodes q full hq
  omega

/-- The originally stated complete raw closure claim, with one uniform
constant and program selected before any entry or raw eligible set. -/
theorem rawClosureClaims : IndexedIntersectionRAM.RawClosureClaims := by
  refine ⟨414, by omega, ?_⟩
  intro q full hq hlaminar
  dsimp only
  constructor
  · refine ⟨rawExtensionProgram (prepareNormalization q full).indexed.nodes.size q, ?_, ?_⟩
    · rw [haltingWords_length, rawExtensionProgram_length]
      have hqnodes := prepared_q_le_nodes q full hq
      omega
    · intro eligible heligible entry hnormalized initial hpc
      exact prepared_rawExtension_correct_run q full hq hlaminar eligible heligible entry hnormalized initial hpc
  · intro left right hleft _hright initial hpc
    obtain ⟨final, operations, hrun, hout, hdenote, hn, hb, hc⟩ :=
      IndexedIntersectionRAM.prepared_intersection_correct_run q full hq hlaminar left right hleft initial hpc
    exact ⟨final, operations, hrun, hout, hdenote, hn, hb, hc.trans (by omega)⟩

end PaperProofs.Structure.LaminarTree.IndexedRawClosureRAM
