module

public import Structure.PA17_QueryBudget_015
public import Structure.PA17_QueryReply_017
public import Structure.PA17_QuerySelectionSafety_020

/-! The complete actual Nat-RAM query, from arbitrary incoming heap with
only the original correct persistent table. All metadata/counts/leaf labels,
current-stage node, budget scans, selected entry/tool and reply registers
are actually computed. No answer or execution trace is a caller premise. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17Query019

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def ranksProgram (N q size : Nat) : List Op :=
  PA17QueryRanks011.program q (PA17QueryLayout014.goodFlags N q size)
    (PA17QueryLayout014.badFlags N q size) (PA17QueryLayout014.header N q size)

def selectProgram (N q size : Nat) : List Op :=
  PA17QuerySelection010b.program size (PA17QueryLayout014.countsBase N q size)
    (PA17QueryLayout014.labelBase N q size) (PA17QueryLayout014.header N q size) (PA17QueryLayout014.childBase N q size)

def replyProgram (N q size : Nat) : List Op :=
  PA17QueryRanks011.replyProgram q (PA17QueryLayout014.header N q size) (PA17QueryLayout014.toolAddress N q size)

def program (N q size : Nat) : List Op :=
  PA17QueryBudget015.program N q size ++ ranksProgram N q size ++ selectProgram N q size ++ replyProgram N q size

theorem ranks_frame (rom : ROM) (N q size : Nat) (state : State) (address : Nat)
    (ha : address < PA17QueryLayout014.header N q size + 4) :
    (execute rom (ranksProgram N q size) state).heap address = state.heap address := by
  have hf := PA17QueryRanks011.program_prefixFrame q (PA17QueryLayout014.goodFlags N q size)
    (PA17QueryLayout014.badFlags N q size) (PA17QueryLayout014.header N q size) address rom (by
      intro offset hm
      simp only [List.mem_cons, List.mem_nil_iff, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl <;> omega)
      state (ranksProgram N q size).length le_rfl
  change (execute rom ((ranksProgram N q size).take (ranksProgram N q size).length) state).heap address = _ at hf
  simpa only [List.take_length] using hf

theorem rowBounds (N q size : Nat) (row : Fin (N + 1)) :
    PA17QueryTests009.ReadBounds size q (PA17QueryLayout014.header N q size)
      (PA17QueryLayout014.countsBase N q size) (PA17QueryLayout014.parentBase N q size)
      (PA17QueryLayout014.header N q size + 1) (PA17QueryBudget015.rowBase q size row.val)
      (PA17QueryLayout014.header N q size + 4) := by
  constructor
  · omega
  · omega
  · rw [PA17QueryLayout014.counts_before_header]
    omega
  · dsimp [PA17QueryLayout014.parentBase, PA17QueryLayout014.header,
      PA17QueryLayout014.countsBase, PA17QueryLayout014.labelBase]
    omega
  · have ht := PA17CellLayout003.table_le_capacityWords N q size
    have hc := (PA17QueryLayout014.capacity_before_queryRegions N q size).2.2.2.1
    exact (PA17QueryBudget015.row_fits_table N q size row).trans
      (ht.trans (hc.trans (Nat.le_add_right _ _)))

theorem physicalTableCorrect_transfer (q : Nat) (full : List (Finset (Fin q))) (old fresh : Nat → Nat)
    (htable : PhysicalTableCorrect q full old)
    (hf : ∀ address < tableWords full.length q (prepareNormalization q full).indexed.nodes.size, fresh address = old address) :
    PhysicalTableCorrect q full fresh := by
  let size := (prepareNormalization q full).indexed.nodes.size
  constructor
  · intro row budget
    have hs := PA17QueryBudget015.row_slot_bound full.length q row.val budget.val row.isLt budget.isLt
    have he : readEntry size (row.val * (q + 2) + budget.val) fresh = readEntry size (row.val * (q + 2) + budget.val) old := by
      apply PA17QueryLayout014.readEntry_congr
      intro index hi
      exact hf _ (PA17CellLayout003.table_slot_bound _ _ _ _ hs index hi)
    rw [he]
    exact htable.1 row budget
  · intro slot hs
    rw [hf _ (by simpa only [Nat.add_zero] using PA17CellLayout003.table_slot_bound full.length q size slot hs 0 (Nat.zero_le _))]
    exact htable.2 slot hs

theorem selector_regions (N q size : Nat) :
    PA17QueryLayout014.countsBase N q size + size ≤ PA17QueryLayout014.childBase N q size ∧
    PA17QueryLayout014.labelBase N q size + size ≤ PA17QueryLayout014.childBase N q size ∧
    PA17QueryLayout014.header N q size + 7 < PA17QueryLayout014.childBase N q size ∧
    tableWords N q size ≤ PA17QueryLayout014.childBase N q size := by
  have ht := PA17CellLayout003.table_le_capacityWords N q size
  have hc := (PA17QueryLayout014.capacity_before_queryRegions N q size).2.2.2.2.2.2
  refine ⟨?_, ?_, ?_, ht.trans hc⟩ <;>
    dsimp [PA17QueryLayout014.childBase, PA17QueryLayout014.badFlags, PA17QueryLayout014.goodFlags,
      PA17QueryLayout014.header, PA17QueryLayout014.countsBase, PA17QueryLayout014.labelBase] <;> omega

theorem prepared_program_correct (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1)) (used : Finset (Fin q)) (state : State)
    (htable : PhysicalTableCorrect q full state.heap) :
    ReplyCorrect q (expectedReply q full hq stage used)
      (execute (queryROM q full stage.val used).semantic
        (program full.length q (prepareNormalization q full).indexed.nodes.size) state) := by
  let cache := (prepareNormalization q full).indexed
  let N := full.length
  let size := cache.nodes.size
  let rom := (queryROM q full stage.val used).semantic
  let header := PA17QueryLayout014.header N q size
  let counts := IndexedDescent.usedCounts cache used
  let leaves := IndexedDescent.leafTools cache
  let rowId := PA17QueryBudget015.rowIndex full stage
  let row := IndexedQuery.storedPositiveRow q full rowId
  let node := PA17QueryBudget015.node full hq stage
  let good := fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget)
  let bad := IndexedQuery.budgetExtensionTest cache counts row node
  let a := execute rom (PA17QueryBudget015.program N q size) state
  let b := execute rom (ranksProgram N q size) a
  let c := execute rom (selectProgram N q size) b
  have hflags := PA17QueryBudget015.prepared_program_correct q full hq hlaminar stage used state htable
  have hai := PA17QueryBudget015.prepared_final_inputs q full hq hlaminar stage used state htable
  have hal := PA17QueryBudget015.prepared_labels_correct q full hq hlaminar stage used state
  have hah := PA17QueryBudget015.prepared_header_correct q full hq stage used state
  have hgood (budget : Nat) (hb : budget < q + 2) :
      a.heap (PA17QueryLayout014.goodFlags N q size + budget) = bit (good budget) := by
    dsimp only [good]
    rw [IndexedQuery.entryAt_get row budget hb]
    exact (hflags ⟨budget, hb⟩).1
  have hbad (budget : Nat) (hb : budget < q + 2) :
      a.heap (PA17QueryLayout014.badFlags N q size + budget) = bit (bad budget) := by
    dsimp only [bad, IndexedQuery.budgetExtensionTest]
    rw [IndexedQuery.entryAt_get row budget hb]
    exact (hflags ⟨budget, hb⟩).2
  have hbadBase : header + 4 < PA17QueryLayout014.badFlags N q size := by
    dsimp [header, PA17QueryLayout014.badFlags, PA17QueryLayout014.goodFlags]
    omega
  have hrank := PA17QueryRanks011.program_heap q (PA17QueryLayout014.goodFlags N q size)
    (PA17QueryLayout014.badFlags N q size) header rom hbadBase good bad a hgood hbad
  have hcontrol := PA17QueryRanks011.prepared_selection_control q (PA17QueryLayout014.goodFlags N q size)
    (PA17QueryLayout014.badFlags N q size) header rom hbadBase good bad a hgood hbad
  change b.heap = _ at hrank
  change b.heap (header + 6) = PA17QueryRanks011.firstFalseValue q bad - 1 ∧
    b.heap (header + 7) = (if a.heap (header + 2) = 0 then 0 else if PA17QueryRanks011.firstFalseValue q bad = 0 then 0 else 1) ∧
    b.heap (header + 6) ≤ q + 1 at hcontrol
  have hb2 : b.heap (header + 2) = a.heap (header + 2) := ranks_frame rom N q size a _ (by omega)
  have hb4 : b.heap (header + 4) = PA17QueryRanks011.firstFalseValue q good := by rw [hrank]; simp
  have hb5 : b.heap (header + 5) = PA17QueryRanks011.firstFalseValue q bad := by rw [hrank]; simp
  have hbi : PA17QueryTests009.Inputs cache header (PA17QueryLayout014.countsBase N q size)
      (PA17QueryLayout014.parentBase N q size) (header + 1) (PA17QueryBudget015.rowBase q size rowId.val)
      counts row node b.heap := by
    exact PA17QueryTests009.Inputs.transfer hai (rowBounds N q size rowId)
      (fun address ha => ranks_frame rom N q size a address ha)
  have hbl : PA17QuerySelection010b.LabelsFor cache leaves (PA17QueryLayout014.labelBase N q size) b.heap := by
    intro target
    rw [ranks_frame rom N q size a _ (by
      dsimp [PA17QueryLayout014.header, PA17QueryLayout014.countsBase]
      have ht := target.isLt
      omega)]
    exact hal target
  have hta := PA17QueryBudget015.program_physicalTableCorrect q full stage.val used state htable
  have htb : PhysicalTableCorrect q full b.heap := by
    apply physicalTableCorrect_transfer q full a.heap b.heap hta
    intro address ha
    change address < tableWords N q size at ha
    have ht := PA17CellLayout003.table_le_capacityWords N q size
    have hc := (PA17QueryLayout014.capacity_before_queryRegions N q size).2.2.2.1
    exact ranks_frame rom N q size a address (lt_of_lt_of_le (ha.trans_le (ht.trans hc)) (Nat.le_add_right _ _))
  have hbudget : b.heap (header + 6) < q + 2 := by have hb := hcontrol.2.2; omega
  let budget : Fin (q + 2) := ⟨b.heap (header + 6), hbudget⟩
  let sourceSlot := rowId.val * (q + 2) + budget.val
  have hslot : sourceSlot < cells N q := PA17QueryBudget015.row_slot_bound N q rowId.val budget.val rowId.isLt budget.isLt
  have hregions := selector_regions N q size
  have hsource : (sourceSlot + 1) * (size + 1) ≤ PA17QueryLayout014.childBase N q size := by
    have hm := Nat.mul_le_mul_right (size + 1) (Nat.succ_le_of_lt hslot)
    exact hm.trans hregions.2.2.2
  have hptr : b.heap header + (size + 1) * b.heap (header + 6) = sourceSlot * (size + 1) := by
    rw [hbi.row_pointer]
    dsimp [PA17QueryBudget015.rowBase, sourceSlot, budget]
    ring
  have hentry : readEntry size sourceSlot b.heap = IndexedQuery.entryAt row (b.heap (header + 6)) := by
    rw [IndexedQuery.entryAt_get row _ hbudget]
    exact htb.1 rowId budget
  have hselect := PA17QuerySelection010b.prepared_program_selectEntry q full stage.val used counts
    (PA17QueryLayout014.countsBase N q size) (PA17QueryLayout014.labelBase N q size) header
    (PA17QueryLayout014.childBase N q size) sourceSlot hregions.1 hregions.2.1 hregions.2.2.1 hsource b hptr
    hbi.counts hbl node hbi.node_pointer
  have hrom : PA17QuerySelection010.ParentROMFor cache rom := fun n => UniformNormalizationRAM.givenTreeROM_parent q full n
  have hf (address : Nat) (ha : address < PA17QueryLayout014.childBase N q size) : c.heap address = b.heap address :=
    PA17QuerySelection010b.program_frame cache rom hrom _ _ _ _ b address ha
  have hc2 : c.heap (header + 2) = b.heap (header + 2) := hf _ (by have hh := hregions.2.2.1; omega)
  have hc4 : c.heap (header + 4) = b.heap (header + 4) := hf _ (by have hh := hregions.2.2.1; omega)
  have hc5 : c.heap (header + 5) = b.heap (header + 5) := hf _ (by have hh := hregions.2.2.1; omega)
  have hc6 : c.heap (header + 6) = b.heap (header + 6) := hf _ (by have hh := hregions.2.2.1; omega)
  have hc7 : c.heap (header + 7) = b.heap (header + 7) := hf _ hregions.2.2.1
  have ht : c.heap (PA17QueryLayout014.toolAddress N q size) = if c.heap (header + 7) = 0 then 0 else
      PA17QueryReply017.encodeTool (IndexedQuery.selectEntry cache leaves counts node (IndexedQuery.entryAt row (c.heap (header + 6)))) := by
    rw [hc7, hc6]
    have ht := hselect.2
    rw [hentry] at ht
    exact ht
  have hb6 : c.heap (header + 6) = PA17QueryRanks011.firstFalseValue q bad - 1 := hc6.trans hcontrol.1
  have hb7 : c.heap (header + 7) = if c.heap (header + 2) = 0 then 0 else
      if PA17QueryRanks011.firstFalseValue q bad = 0 then 0 else 1 := by
    rw [hc7, hc2, hb2]
    exact hcontrol.2.1
  have hreply := PA17QueryReply017.replyProgram_query cache leaves counts row node rom c header
    (PA17QueryLayout014.toolAddress N q size) (hc4.trans hb4) (hc5.trans hb5) hb6 hb7 ht
  have hactive : c.heap (header + 2) = PA17QueryHeader009.active N stage.val :=
    hc2.trans (hb2.trans hah.2.2.1)
  have heq : (if c.heap (header + 2) = 0 then IndexedQuery.terminalReply q else IndexedQuery.query cache leaves counts row node) =
      expectedReply q full hq stage used := by
    rw [hactive]
    by_cases hs : stage.val < full.length
    · rw [show PA17QueryHeader009.active N stage.val = 1 from by simp [PA17QueryHeader009.active, N, hs],
        ite_eq_right Nat.one_ne_zero, expectedReply, dite_eq_left hs]
      dsimp only [row, rowId, node]
      rw [PA17QueryBudget015.rowIndex, dite_eq_left hs, PA17QueryBudget015.node, dite_eq_left hs]
    · rw [show PA17QueryHeader009.active N stage.val = 0 from by simp [PA17QueryHeader009.active, N, hs],
        ite_eq_left rfl, expectedReply, dite_eq_right hs]
  rw [heq] at hreply
  simp only [program, IndexedClosureRAM.execute_append]
  exact hreply

theorem op_trace_pos (op : Op) : 1 ≤ op.trace.length := by
  cases op with
  | base instruction => cases instruction <;> simp [Op.trace, Instruction.trace, Instruction.operations]
  | subtract target left right => simp [Op.trace]

theorem length_le_trace (code : List Op) : code.length ≤ (trace code).length := by
  induction code with
  | nil => rfl
  | cons op later ih =>
    have ho := op_trace_pos op
    simp only [trace, List.flatMap_cons, List.length_append, List.length_cons] at *
    omega

theorem selector_totalQueryCost_le (N q size : Nat) (hsize : 0 < size) :
    totalQueryCost q (selectProgram N q size) ≤ 4096 * queryWork q size := by
  have hl := length_le_trace (selectProgram N q size)
  have ht : (trace (selectProgram N q size)).length = 324 * size + 271 :=
    PA17QuerySelection010b.program_trace_length _ _ _ _ _
  rw [ht] at hl
  rw [totalQueryCost, haltingWords_length, List.length_append, haltTrace_length, ht]
  have hs : size ≤ queryWork q size := Nat.le_mul_of_pos_left size (by omega)
  have hq : q + 1 ≤ queryWork q size := Nat.le_mul_of_pos_right (q + 1) hsize
  omega

theorem totalQueryCost_le (N q size : Nat) (hsize : 0 < size) :
    totalQueryCost q (program N q size) ≤ 16384 * queryWork q size := by
  have hb := PA17QueryBudget015.totalQueryCost_le N q size hsize
  have hr := PA17QueryRanks011.program_totalQueryCost_le q size (PA17QueryLayout014.goodFlags N q size)
    (PA17QueryLayout014.badFlags N q size) (PA17QueryLayout014.header N q size) hsize
  have hs := selector_totalQueryCost_le N q size hsize
  have hp := PA17QueryReply017.replyProgram_totalQueryCost_le q size (PA17QueryLayout014.header N q size)
    (PA17QueryLayout014.toolAddress N q size) hsize
  have ha := PA17QueryPrepare013.totalQueryCost_append_le q (PA17QueryBudget015.program N q size) (ranksProgram N q size)
  have hac := PA17QueryPrepare013.totalQueryCost_append_le q
    (PA17QueryBudget015.program N q size ++ ranksProgram N q size) (selectProgram N q size)
  have had := PA17QueryPrepare013.totalQueryCost_append_le q
    (PA17QueryBudget015.program N q size ++ ranksProgram N q size ++ selectProgram N q size) (replyProgram N q size)
  change totalQueryCost q (ranksProgram N q size) ≤ 700 * queryWork q size at hr
  change totalQueryCost q (replyProgram N q size) ≤ 300 * queryWork q size at hp
  dsimp only [program]
  omega

theorem program_capacity_prefixFrame (rom : ROM) (N q size address : Nat)
    (ha : address < PA17QueryLayout014.capacityWords N q size) :
    UniformFreeTableSafety.PrefixFrame rom (program N q size) address := by
  have hb := PA17QueryLayout014.capacity_before_queryRegions N q size
  rw [program]
  apply UniformFreeTableSafety.PrefixFrame.append
  · apply UniformFreeTableSafety.PrefixFrame.append
    · apply UniformFreeTableSafety.PrefixFrame.append
      · exact PA17QueryBudget015.program_capacity_prefixFrame rom N q size address ha
      · exact PA17QueryRanks011.program_prefixFrame q _ _ _ address rom
          (by intro offset _; have hc := hb.2.2.2.1; omega)
    · exact PA17QuerySelectionSafety020.program_prefixFrame rom size _ _ _ _ address (ha.trans_le hb.2.2.2.2.2.2)
  · intro state count _
    exact congrFun (PA17QueryRanks011.replyProgram_prefix_heap q _ _ rom state count) address

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

theorem program_physicalTableCorrect (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q))
    (state : State) (htable : PhysicalTableCorrect q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    PhysicalTableCorrect q full (execute (queryROM q full stage used).semantic (program full.length q size) state).heap := by
  intro size
  apply physicalTableCorrect_transfer q full state.heap _ htable
  intro address ha
  have hf := program_table_take_frame (queryROM q full stage used).semantic full.length q size
    (program full.length q size).length state address ha
  simpa only [List.take_length] using hf

theorem program_halting (rom : ROM) (N q size : Nat) (hsize : 0 < size) (state : State) (hpc : state.pc = 0) :
    HaltingRuns rom (program N q size) state (execute rom (program N q size) state)
      (trace (program N q size) ++ haltTrace) ∧
      (trace (program N q size) ++ haltTrace).length ≤ 16384 * queryWork q size := by
  refine ⟨execute_halts _ _ state hpc, ?_⟩
  have hc := totalQueryCost_le N q size hsize
  dsimp only [totalQueryCost] at hc
  omega

end PaperProofs.Structure.LaminarTree.PA17Query019
