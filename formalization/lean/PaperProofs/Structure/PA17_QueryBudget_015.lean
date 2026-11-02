module

public import PaperProofs.Structure.PA17_QueryLayout_014
public import PaperProofs.Structure.PA17_QueryHeader_009
public import PaperProofs.Structure.PA17_QueryTests_009

/-! Actual fresh query preparation, dynamic current-stage header and all
budget tests. The only incoming semantic assumption is the original correct
tag-first table. No Persistent/Inputs/ReadBounds/cache premise is imposed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryBudget015

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001

def testsProgram (N q size : Nat) : List Op :=
  PA17QueryTests009.program size q (PA17QueryLayout014.header N q size)
    (PA17QueryLayout014.countsBase N q size) (PA17QueryLayout014.parentBase N q size)
    (PA17QueryLayout014.header N q size + 1) (PA17QueryLayout014.goodFlags N q size) (PA17QueryLayout014.badFlags N q size)

def program (N q size : Nat) : List Op :=
  PA17QueryLayout014.prepareProgram N q size ++
    PA17QueryHeader009.program N q size (PA17QueryLayout014.header N q size) ++ testsProgram N q size

def rowIndex {q : Nat} (full : List (Finset (Fin q))) (stage : Fin (full.length + 1)) : Fin (full.length + 1) :=
  if hs : stage.val < full.length then ⟨stage.val + 1, by omega⟩ else ⟨0, by omega⟩

def node {q : Nat} (full : List (Finset (Fin q))) (hq : 0 < q) (stage : Fin (full.length + 1)) :
    Option (prepareNormalization q full).indexed.NodeId :=
  if hs : stage.val < full.length then IndexedQuery.storedStageNode q full hq ⟨stage.val, hs⟩ else none

def rowBase (q size row : Nat) : Nat := row * (q + 2) * (size + 1)

theorem header_rowPointer (q : Nat) (full : List (Finset (Fin q))) (stage : Fin (full.length + 1)) (size : Nat) :
    PA17QueryHeader009.rowPointer full.length q size stage.val = rowBase q size (rowIndex full stage).val := by
  by_cases hs : stage.val < full.length
  · rw [PA17QueryHeader009.rowPointer, ite_eq_left hs, rowIndex, dite_eq_left hs]
    dsimp [rowBase, PA17QueryHeader009.stride]
    ring
  · rw [PA17QueryHeader009.rowPointer, ite_eq_right hs, rowIndex, dite_eq_right hs]
    simp [rowBase]

theorem header_nodeWord (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (stage : Fin (full.length + 1)) :
    PA17QueryHeader009.nodeWord q full hq stage = encodedNode (prepareNormalization q full).indexed (node full hq stage) := by
  by_cases hs : stage.val < full.length <;>
    simp only [PA17QueryHeader009.nodeWord, node, hs, dite_true, dite_false, encodedNode]

theorem row_slot_bound (N q row budget : Nat) (hr : row < N + 1) (hb : budget < q + 2) :
    row * (q + 2) + budget < cells N q := by
  dsimp [cells]
  calc
    row * (q + 2) + budget < row * (q + 2) + (q + 2) := Nat.add_lt_add_left hb _
    _ = (row + 1) * (q + 2) := by ring
    _ ≤ (N + 1) * (q + 2) := Nat.mul_le_mul_right _ (by omega)

theorem row_fits_table (N q size : Nat) (row : Fin (N + 1)) :
    rowBase q size row.val + (q + 2) * (size + 1) ≤ tableWords N q size := by
  have hm := Nat.mul_le_mul_right ((q + 2) * (size + 1)) (show row.val + 1 ≤ N + 1 from row.isLt)
  convert hm using 1 <;> dsimp [rowBase, tableWords, cells] <;> ring

theorem readBounds (N q size : Nat) (row : Fin (N + 1)) :
    PA17QueryTests009.ReadBounds size q (PA17QueryLayout014.header N q size)
      (PA17QueryLayout014.countsBase N q size) (PA17QueryLayout014.parentBase N q size)
      (PA17QueryLayout014.header N q size + 1) (rowBase q size row.val) (PA17QueryLayout014.goodFlags N q size) := by
  constructor
  · dsimp [PA17QueryLayout014.goodFlags]
    omega
  · dsimp [PA17QueryLayout014.goodFlags]
    omega
  · rw [PA17QueryLayout014.counts_before_header]
    dsimp [PA17QueryLayout014.goodFlags]
    omega
  · dsimp [PA17QueryLayout014.parentBase, PA17QueryLayout014.goodFlags, PA17QueryLayout014.header,
      PA17QueryLayout014.countsBase, PA17QueryLayout014.labelBase]
    omega
  · have ht := PA17CellLayout003.table_le_capacityWords N q size
    have hc := (PA17QueryLayout014.capacity_before_queryRegions N q size).2.2.2.2.1
    exact (row_fits_table N q size row).trans (ht.trans hc)

theorem header_below_frame (rom : ROM) (N q size : Nat) (state : State) (address : Nat)
    (ha : address < PA17QueryLayout014.header N q size) :
    (execute rom (PA17QueryHeader009.program N q size (PA17QueryLayout014.header N q size)) state).heap address = state.heap address := by
  have hf := PA17QueryHeader009.program_take_frame rom N q size _
    (PA17QueryHeader009.program N q size (PA17QueryLayout014.header N q size)).length state address (Or.inl ha)
  simpa only [List.take_length] using hf

theorem header_table_take_frame (rom : ROM) (N q size count : Nat) (state : State) (address : Nat)
    (ha : address < tableWords N q size) :
    (execute rom ((PA17QueryHeader009.program N q size (PA17QueryLayout014.header N q size)).take count) state).heap address = state.heap address := by
  have ht := PA17CellLayout003.table_le_capacityWords N q size
  have hc := (PA17QueryLayout014.capacity_before_queryRegions N q size).2.2.2.1
  exact PA17QueryHeader009.program_take_frame rom N q size _ count state address (Or.inl (lt_of_lt_of_le ha (ht.trans hc)))

theorem header_physicalTableCorrect (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (state : State) (htable : PhysicalTableCorrect q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    PhysicalTableCorrect q full (execute (queryROM q full stage used).semantic
      (PA17QueryHeader009.program full.length q size (PA17QueryLayout014.header full.length q size)) state).heap := by
  intro size
  have hf (address : Nat) (ha : address < tableWords full.length q size) :
      (execute (queryROM q full stage used).semantic
        (PA17QueryHeader009.program full.length q size (PA17QueryLayout014.header full.length q size)) state).heap address = state.heap address := by
    have h := header_table_take_frame (queryROM q full stage used).semantic full.length q size
      (PA17QueryHeader009.program full.length q size (PA17QueryLayout014.header full.length q size)).length state address ha
    simpa only [List.take_length] using h
  constructor
  · intro row budget
    have hs := row_slot_bound full.length q row.val budget.val row.isLt budget.isLt
    have he : readEntry size (row.val * (q + 2) + budget.val)
        (execute (queryROM q full stage used).semantic
          (PA17QueryHeader009.program full.length q size (PA17QueryLayout014.header full.length q size)) state).heap =
        readEntry size (row.val * (q + 2) + budget.val) state.heap := by
      apply PA17QueryLayout014.readEntry_congr
      intro index hi
      exact hf _ (PA17CellLayout003.table_slot_bound _ _ _ _ hs index hi)
    rw [he]
    exact htable.1 row budget
  · intro slot hs
    rw [hf _ (by simpa only [Nat.add_zero] using PA17CellLayout003.table_slot_bound full.length q size slot hs 0 (Nat.zero_le _))]
    exact htable.2 slot hs

theorem entries_of_physicalTableCorrect (q : Nat) (full : List (Finset (Fin q)))
    (row : Fin (full.length + 1)) (heap : Nat → Nat) (htable : PhysicalTableCorrect q full heap) :
    let cache := (prepareNormalization q full).indexed
    ∀ budget : Fin (q + 2), TagFirstRep cache heap (rowBase q cache.nodes.size row.val + budget.val * (cache.nodes.size + 1))
      ((IndexedQuery.storedPositiveRow q full row).get budget) := by
  intro cache budget
  let slot := row.val * (q + 2) + budget.val
  have hs := row_slot_bound full.length q row.val budget.val row.isLt budget.isLt
  have hr := rep_of_readEntry cache slot heap _ (htable.2 slot hs) (htable.1 row budget)
  have haddr : slot * (cache.nodes.size + 1) = rowBase q cache.nodes.size row.val + budget.val * (cache.nodes.size + 1) := by
    dsimp [slot, rowBase]
    ring
  rw [haddr] at hr
  exact hr

theorem prepared_inputs (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (state : State)
    (htable : PhysicalTableCorrect q full state.heap) :
    let cache := (prepareNormalization q full).indexed
    let N := full.length
    let size := cache.nodes.size
    let afterPrepare := execute (queryROM q full stage.val used).semantic (PA17QueryLayout014.prepareProgram N q size) state
    let fresh := execute (queryROM q full stage.val used).semantic
      (PA17QueryHeader009.program N q size (PA17QueryLayout014.header N q size)) afterPrepare
    PA17QueryTests009.Inputs cache (PA17QueryLayout014.header N q size) (PA17QueryLayout014.countsBase N q size)
      (PA17QueryLayout014.parentBase N q size) (PA17QueryLayout014.header N q size + 1)
      (rowBase q size (rowIndex full stage).val) (IndexedDescent.usedCounts cache used)
      (IndexedQuery.storedPositiveRow q full (rowIndex full stage)) (node full hq stage) fresh.heap := by
  intro cache N size afterPrepare fresh
  have hp := PA17QueryLayout014.prepared_prepareProgram_correct q full hq hlaminar stage.val used state
  have hh := PA17QueryHeader009.prepared_program_correct q full hq stage used (PA17QueryLayout014.header N q size) afterPrepare
  have hta := PA17QueryLayout014.prepareProgram_physicalTableCorrect q full stage.val used state htable
  have htb := header_physicalTableCorrect q full stage.val used afterPrepare hta
  have hf (address : Nat) (ha : address < PA17QueryLayout014.header N q size) : fresh.heap address = afterPrepare.heap address :=
    header_below_frame _ N q size afterPrepare address ha
  constructor
  · exact hh.1.trans (header_rowPointer q full stage size)
  · exact hh.2.1.trans (header_nodeWord q full hq stage)
  · intro target
    rw [hf _ (by
      dsimp [PA17QueryLayout014.header]
      have ht := target.isLt
      omega)]
    exact hp.2.2 target
  · have hparent := PA17HeapAncestors001.metadata_parentHeapFor q full (PA17QueryLayout014.metadataBase N q size) afterPrepare.heap hp.1
    constructor
    · rw [hf _ (by
        dsimp [PA17QueryLayout014.parentBase, PA17QueryLayout014.header, PA17QueryLayout014.countsBase, PA17QueryLayout014.labelBase]
        omega)]
      exact hparent.1
    · intro target
      rw [hf _ (by
        dsimp [PA17QueryLayout014.parentBase, PA17QueryLayout014.header, PA17QueryLayout014.countsBase, PA17QueryLayout014.labelBase]
        have ht := target.isLt
        omega)]
      exact hparent.2 target
  · exact entries_of_physicalTableCorrect q full (rowIndex full stage) fresh.heap htb

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (state : State)
    (htable : PhysicalTableCorrect q full state.heap) :
    let cache := (prepareNormalization q full).indexed
    let size := cache.nodes.size
    let result := execute (queryROM q full stage.val used).semantic (program full.length q size) state
    ∀ budget : Fin (q + 2),
    result.heap (PA17QueryLayout014.goodFlags full.length q size + budget.val) =
        bit (IndexedQuery.accepts cache (IndexedDescent.usedCounts cache used)
          ((IndexedQuery.storedPositiveRow q full (rowIndex full stage)).get budget)) ∧
      result.heap (PA17QueryLayout014.badFlags full.length q size + budget.val) =
        bit (IndexedQuery.extensionTest cache (IndexedDescent.usedCounts cache used) (node full hq stage)
          ((IndexedQuery.storedPositiveRow q full (rowIndex full stage)).get budget)) := by
  intro cache size result
  have hi := prepared_inputs q full hq hlaminar stage used state htable
  dsimp only [result]
  simp only [program, IndexedClosureRAM.execute_append]
  exact PA17QueryTests009.program_correct cache (queryROM q full stage.val used).semantic
    (PA17QueryLayout014.header full.length q size) (PA17QueryLayout014.countsBase full.length q size)
    (PA17QueryLayout014.parentBase full.length q size) (PA17QueryLayout014.header full.length q size + 1)
    (rowBase q size (rowIndex full stage).val) (PA17QueryLayout014.goodFlags full.length q size)
    (PA17QueryLayout014.goodFlags full.length q size) (PA17QueryLayout014.badFlags full.length q size)
    (IndexedDescent.usedCounts cache used) (IndexedQuery.storedPositiveRow q full (rowIndex full stage)) (node full hq stage)
    _ hi (readBounds full.length q size (rowIndex full stage)) le_rfl
    (by dsimp [PA17QueryLayout014.badFlags]; omega)
    (fun left right => PA17QueryLayout014.flags_disjoint _ _ _ _ _ left.isLt right.isLt)

theorem program_capacity_prefixFrame (rom : ROM) (N q size address : Nat)
    (ha : address < PA17QueryLayout014.capacityWords N q size) :
    UniformFreeTableSafety.PrefixFrame rom (program N q size) address := by
  have hb := PA17QueryLayout014.capacity_before_queryRegions N q size
  rw [program]
  apply UniformFreeTableSafety.PrefixFrame.append
  · apply UniformFreeTableSafety.PrefixFrame.append
    · exact PA17QueryLayout014.prepareProgram_prefixFrame rom N q size address ha
    · exact PA17QueryHeader009.program_prefixFrame rom N q size _ address (Or.inl (ha.trans_le hb.2.2.2.1))
  · exact PA17QueryTests009.program_prefixFrame rom size q _ _ _ _ _ _ address
      (by intro budget _; have hg := hb.2.2.2.2.1; omega)
      (by intro budget _; have hbad := hb.2.2.2.2.2.1; omega)

theorem program_capacity_take_frame (rom : ROM) (N q size count : Nat) (state : State) (address : Nat)
    (ha : address < PA17QueryLayout014.capacityWords N q size) :
    (execute rom ((program N q size).take count) state).heap address = state.heap address := by
  by_cases hc : count ≤ (program N q size).length
  · exact program_capacity_prefixFrame rom N q size address ha state count hc
  · rw [List.take_of_length_le (by omega)]
    simpa only [List.take_length] using program_capacity_prefixFrame rom N q size address ha state (program N q size).length le_rfl

theorem program_table_take_frame (rom : ROM) (N q size count : Nat) (state : State) (address : Nat)
    (ha : address < tableWords N q size) :
    (execute rom ((program N q size).take count) state).heap address = state.heap address :=
  program_capacity_take_frame rom N q size count state address (ha.trans_le (PA17CellLayout003.table_le_capacityWords N q size))

theorem program_capacityThroughout (rom : PhysicalROM) (N q size : Nat) (state : State)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords N q size) state.heap) :
    CapacityThroughout q (PA17QueryLayout014.capacityWords N q size) rom (program N q size) state := by
  intro count hc address ha
  rw [program_capacity_prefixFrame rom.semantic N q size address ha state count hc]
  exact hcap address ha

theorem program_readEntry_frame (rom : ROM) (N q size slot : Nat) (hs : slot < cells N q) (state : State) :
    readEntry size slot (execute rom (program N q size) state).heap = readEntry size slot state.heap := by
  apply PA17QueryLayout014.readEntry_congr
  intro index hi
  have hf := program_table_take_frame rom N q size (program N q size).length state _
    (PA17CellLayout003.table_slot_bound N q size slot hs index hi)
  simpa only [List.take_length] using hf

theorem program_physicalTableCorrect (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (state : State) (htable : PhysicalTableCorrect q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    PhysicalTableCorrect q full (execute (queryROM q full stage used).semantic (program full.length q size) state).heap := by
  intro size
  constructor
  · intro row budget
    rw [program_readEntry_frame _ _ _ _ _ (row_slot_bound full.length q row.val budget.val row.isLt budget.isLt)]
    exact htable.1 row budget
  · intro slot hs
    have hf := program_table_take_frame (queryROM q full stage used).semantic full.length q size
      (program full.length q size).length state (slot * (size + 1))
      (by simpa only [Nat.add_zero] using PA17CellLayout003.table_slot_bound full.length q size slot hs 0 (Nat.zero_le _))
    rw [List.take_length] at hf
    rw [hf]
    exact htable.2 slot hs

theorem tests_totalQueryCost_le (N q size : Nat) (hsize : 0 < size) :
    totalQueryCost q (testsProgram N q size) ≤ 2001 * queryWork q size := by
  have hc := PA17QueryTests009.program_charged_bound size q
    (PA17QueryLayout014.header N q size) (PA17QueryLayout014.countsBase N q size)
    (PA17QueryLayout014.parentBase N q size) (PA17QueryLayout014.header N q size + 1)
    (PA17QueryLayout014.goodFlags N q size) (PA17QueryLayout014.badFlags N q size) hsize
  have hq : q + 1 ≤ queryWork q size := Nat.le_mul_of_pos_right (q + 1) hsize
  change (haltingWords (testsProgram N q size)).length +
    (trace (testsProgram N q size) ++ haltTrace).length + 8 ≤ 2000 * queryWork q size at hc
  dsimp only [totalQueryCost]
  omega

theorem totalQueryCost_le (N q size : Nat) (hsize : 0 < size) :
    totalQueryCost q (program N q size) ≤ 4096 * queryWork q size := by
  have hp := PA17QueryLayout014.prepareProgram_totalQueryCost_le N q size hsize
  have hh := PA17QueryHeader009.totalQueryCost_le N q size (PA17QueryLayout014.header N q size) hsize
  have ht := tests_totalQueryCost_le N q size hsize
  have ha := PA17QueryPrepare013.totalQueryCost_append_le q (PA17QueryLayout014.prepareProgram N q size)
    (PA17QueryHeader009.program N q size (PA17QueryLayout014.header N q size))
  have hb := PA17QueryPrepare013.totalQueryCost_append_le q
    (PA17QueryLayout014.prepareProgram N q size ++ PA17QueryHeader009.program N q size (PA17QueryLayout014.header N q size))
    (testsProgram N q size)
  dsimp only [program]
  omega

theorem tests_protected_frame (rom : ROM) (N q size : Nat) (state : State) (address : Nat)
    (ha : address < PA17QueryLayout014.goodFlags N q size) :
    (execute rom (testsProgram N q size) state).heap address = state.heap address := by
  have hf := PA17QueryTests009.program_protected_prefix rom size q
    (PA17QueryLayout014.header N q size) (PA17QueryLayout014.countsBase N q size)
    (PA17QueryLayout014.parentBase N q size) (PA17QueryLayout014.header N q size + 1)
    (PA17QueryLayout014.goodFlags N q size) (PA17QueryLayout014.badFlags N q size)
    (PA17QueryLayout014.goodFlags N q size) le_rfl (by dsimp [PA17QueryLayout014.badFlags]; omega)
    state (testsProgram N q size).length le_rfl address ha
  change (execute rom ((testsProgram N q size).take (testsProgram N q size).length) state).heap address = state.heap address at hf
  simpa only [List.take_length] using hf

theorem prepared_final_inputs (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (state : State)
    (htable : PhysicalTableCorrect q full state.heap) :
    let cache := (prepareNormalization q full).indexed
    let N := full.length
    let size := cache.nodes.size
    PA17QueryTests009.Inputs cache (PA17QueryLayout014.header N q size) (PA17QueryLayout014.countsBase N q size)
      (PA17QueryLayout014.parentBase N q size) (PA17QueryLayout014.header N q size + 1)
      (rowBase q size (rowIndex full stage).val) (IndexedDescent.usedCounts cache used)
      (IndexedQuery.storedPositiveRow q full (rowIndex full stage)) (node full hq stage)
      (execute (queryROM q full stage.val used).semantic (program N q size) state).heap := by
  intro cache N size
  have hi := prepared_inputs q full hq hlaminar stage used state htable
  rw [program, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  apply PA17QueryTests009.Inputs.transfer hi (readBounds N q size (rowIndex full stage))
  intro address ha
  exact tests_protected_frame _ N q size _ address ha

theorem prepared_labels_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q) (hlaminar : LaminarSchedule full)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (state : State) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    PA17LeafLabels005.LabelsCorrect q full (PA17QueryLayout014.labelBase N q size)
      (execute (queryROM q full stage.val used).semantic (program N q size) state).heap := by
  intro N size target
  let rom := (queryROM q full stage.val used).semantic
  let a := execute rom (PA17QueryLayout014.prepareProgram N q size) state
  let b := execute rom (PA17QueryHeader009.program N q size (PA17QueryLayout014.header N q size)) a
  have hp := PA17QueryLayout014.prepared_prepareProgram_correct q full hq hlaminar stage.val used state
  have hh : PA17QueryLayout014.labelBase N q size + target.val < PA17QueryLayout014.header N q size := by
    dsimp [PA17QueryLayout014.header, PA17QueryLayout014.countsBase]
    have ht := target.isLt
    omega
  rw [program, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  rw [tests_protected_frame _ N q size b _ (by dsimp [PA17QueryLayout014.goodFlags]; omega),
    header_below_frame _ N q size a _ hh]
  exact hp.2.1 target

theorem headerCorrect_of_frame (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin (full.length + 1)) (head : Nat) (old fresh : Nat → Nat)
    (hh : PA17QueryHeader009.HeaderCorrect q full hq stage head old)
    (hf : ∀ offset ≤ 8, fresh (head + offset) = old (head + offset)) :
    PA17QueryHeader009.HeaderCorrect q full hq stage head fresh := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · have h0 : fresh head = old head := by simpa only [Nat.add_zero] using hf 0 (by omega)
    exact h0.trans hh.1
  · exact (hf 1 (by omega)).trans hh.2.1
  · exact (hf 2 (by omega)).trans hh.2.2.1
  · exact (hf 3 (by omega)).trans hh.2.2.2.1
  · intro offset ho
    rw [show head + 4 + offset = head + (4 + offset) from by omega, hf (4 + offset) (by omega)]
    simpa only [Nat.add_assoc] using hh.2.2.2.2 offset ho

theorem prepared_header_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (state : State) :
    let N := full.length
    let size := (prepareNormalization q full).indexed.nodes.size
    PA17QueryHeader009.HeaderCorrect q full hq stage (PA17QueryLayout014.header N q size)
      (execute (queryROM q full stage.val used).semantic (program N q size) state).heap := by
  intro N size
  let rom := (queryROM q full stage.val used).semantic
  let a := execute rom (PA17QueryLayout014.prepareProgram N q size) state
  let b := execute rom (PA17QueryHeader009.program N q size (PA17QueryLayout014.header N q size)) a
  have hh := PA17QueryHeader009.prepared_program_correct q full hq stage used (PA17QueryLayout014.header N q size) a
  rw [program, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  apply headerCorrect_of_frame q full hq stage _ b.heap _ hh
  intro offset ho
  exact tests_protected_frame rom N q size b _ (by dsimp [PA17QueryLayout014.goodFlags]; omega)

theorem program_halting (rom : ROM) (N q size : Nat) (hsize : 0 < size) (state : State) (hpc : state.pc = 0) :
    HaltingRuns rom (program N q size) state (execute rom (program N q size) state)
      (trace (program N q size) ++ haltTrace) ∧
      (trace (program N q size) ++ haltTrace).length ≤ 4096 * queryWork q size := by
  refine ⟨execute_halts _ _ state hpc, ?_⟩
  have hc := totalQueryCost_le N q size hsize
  dsimp only [totalQueryCost] at hc
  omega

end PaperProofs.Structure.LaminarTree.PA17QueryBudget015
