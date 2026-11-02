module

public import PaperProofs.Structure.PA17_QueryBudgetWord_032
public import PaperProofs.Structure.PA17_QueryRanksWord_027
public import PaperProofs.Structure.PA17_QuerySelectWord_029
public import PaperProofs.Structure.PA17_QueryFootprint_025
public import PaperProofs.Structure.PA17_Implementation_030

/-! Complete actual-query numeric and finite-word execution. Each component
receives the actual preceding state; arbitrary untouched scratch words are
bounded only by the original incoming Fits assumption. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17QueryWord033

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022

theorem ranks_layout (B N q size : Nat) (hheap : PA17QueryLayout014.heapWords N q size ≤ B) :
    PA17QueryRanksWord027.Layout (2 * B) (PA17QueryLayout014.heapWords N q size) q
      (PA17QueryLayout014.goodFlags N q size) (PA17QueryLayout014.badFlags N q size)
      (PA17QueryLayout014.header N q size) := by
  constructor <;>
    dsimp only [PA17QueryLayout014.goodFlags, PA17QueryLayout014.badFlags, PA17QueryLayout014.header,
      PA17QueryLayout014.countsBase, PA17QueryLayout014.labelBase, PA17QueryLayout014.metadataBase,
      PA17QueryLayout014.heapWords, PA17QueryLayout014.indexWords] at * <;> omega

theorem selector_layout (B N q size : Nat) (row : Fin (N + 1)) (hsize : 0 < size)
    (hheap : PA17QueryLayout014.heapWords N q size ≤ B) :
    PA17QuerySelectWord029.Layout B (PA17QueryLayout014.heapWords N q size) size q
      (PA17QueryLayout014.countsBase N q size) (PA17QueryLayout014.labelBase N q size)
      (PA17QueryLayout014.header N q size) (PA17QueryBudget015.rowBase q size row.val)
      (PA17QueryLayout014.childBase N q size) := by
  have hs := PA17Query019.selector_regions N q size
  have he := PA17QueryLayout014.toolAddress_end N q size
  dsimp only [PA17QueryLayout014.toolAddress] at he
  refine ⟨by omega, by omega, ?_, hsize, hs.1, hs.2.1, by omega,
    (PA17QueryBudget015.row_fits_table N q size row).trans hs.2.2.2⟩
  dsimp only [PA17QueryLayout014.heapWords, PA17QueryLayout014.indexWords] at hheap
  omega

theorem prepared_program_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1)) (used : Finset (Fin q))
    (state : State)
    (htable : PhysicalTableCorrect q full state.heap)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hregister : RegistersLE (2 * PA17QueryBudgetWord032.bound full.length q) state) :
    NumericSafe (2 * PA17QueryBudgetWord032.bound full.length q)
      (PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (queryROM q full stage.val used)
      (PA17Query019.program full.length q (prepareNormalization q full).indexed.nodes.size) state := by
  let cache := (prepareNormalization q full).indexed
  let N := full.length
  let size := cache.nodes.size
  let B := PA17QueryBudgetWord032.bound N q
  let heapWords := PA17QueryLayout014.heapWords N q size
  let input := queryROM q full stage.val used
  let rom := input.semantic
  let header := PA17QueryLayout014.header N q size
  let counts := IndexedDescent.usedCounts cache used
  let leaves := IndexedDescent.leafTools cache
  let rowId := PA17QueryBudget015.rowIndex full stage
  let row := IndexedQuery.storedPositiveRow q full rowId
  let node := PA17QueryBudget015.node full hq stage
  let good := fun budget => IndexedQuery.accepts cache counts (IndexedQuery.entryAt row budget)
  let bad := IndexedQuery.budgetExtensionTest cache counts row node
  let a := execute rom (PA17QueryBudget015.program N q size) state
  let b := execute rom (PA17Query019.ranksProgram N q size) a
  let c := execute rom (PA17Query019.selectProgram N q size) b
  have hheap : heapWords ≤ B := (PA17QueryBudgetWord032.prepared_layout q full stage.val used).heap_bound
  have hrLayout := ranks_layout B N q size hheap
  have hsize : 0 < size := PA17Implementation030.node_size_pos q full
  have h1 := PA17QueryBudgetWord032.prepared_program_numeric q full hq hlaminar stage used state hregister hcap
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
  have ha2 : a.heap (header + 2) ≤ 1 := by
    rw [hah.2.2.1]
    dsimp only [PA17QueryHeader009.active]
    split_ifs <;> omega
  have h2 := PA17QueryRanksWord027.program_numeric (2 * B) heapWords q
    (PA17QueryLayout014.goodFlags N q size) (PA17QueryLayout014.badFlags N q size) header input
    hrLayout good bad a (h1.final _ _ _ _ _) (ha2.trans (by have := hrLayout.q_bound; omega)) hgood hbad
  have hrank := PA17QueryRanks011.program_heap q (PA17QueryLayout014.goodFlags N q size)
    (PA17QueryLayout014.badFlags N q size) header rom hrLayout.header_before_bad good bad a hgood hbad
  change b.heap = _ at hrank
  have hcontrol := PA17QueryRanks011.prepared_selection_control q (PA17QueryLayout014.goodFlags N q size)
    (PA17QueryLayout014.badFlags N q size) header rom hrLayout.header_before_bad good bad a hgood hbad
  change b.heap (header + 6) = PA17QueryRanks011.firstFalseValue q bad - 1 ∧
    b.heap (header + 7) = (if a.heap (header + 2) = 0 then 0 else
      if PA17QueryRanks011.firstFalseValue q bad = 0 then 0 else 1) ∧ b.heap (header + 6) ≤ q + 1 at hcontrol
  have hb4 : b.heap (header + 4) ≤ q + 2 := by
    rw [hrank]; simp only [Function.update_of_ne (by omega : header + 4 ≠ header + 7),
      Function.update_of_ne (by omega : header + 4 ≠ header + 6),
      Function.update_of_ne (by omega : header + 4 ≠ header + 5), Function.update_self]
    exact PA17QueryRanks011.firstFalseValue_le q good
  have hb5 : b.heap (header + 5) ≤ q + 2 := by
    rw [hrank]; simp only [Function.update_of_ne (by omega : header + 5 ≠ header + 7),
      Function.update_of_ne (by omega : header + 5 ≠ header + 6), Function.update_self]
    exact PA17QueryRanks011.firstFalseValue_le q bad
  have hbi : PA17QueryTests009.Inputs cache header (PA17QueryLayout014.countsBase N q size)
      (PA17QueryLayout014.parentBase N q size) (header + 1) (PA17QueryBudget015.rowBase q size rowId.val)
      counts row node b.heap :=
    PA17QueryTests009.Inputs.transfer hai (PA17Query019.rowBounds N q size rowId)
      (fun address ha => PA17Query019.ranks_frame rom N q size a address ha)
  have hbl : PA17QuerySelection010b.LabelsFor cache leaves (PA17QueryLayout014.labelBase N q size) b.heap := by
    intro target
    rw [PA17Query019.ranks_frame rom N q size a _ (by
      dsimp [PA17QueryLayout014.header, PA17QueryLayout014.countsBase]
      have ht := target.isLt
      omega)]
    exact hal target
  have hcapA : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords N q size) a.heap := by
    have hh := PA17QueryBudget015.program_capacityThroughout input N q size state hcap
      (PA17QueryBudget015.program N q size).length le_rfl
    simpa only [List.take_length] using hh
  have hcapB : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords N q size) b.heap := by
    change CapacityPrefixBounded q (PA17QueryLayout014.capacityWords N q size)
      (execute input.semantic (PA17QueryRanks011.program q (PA17QueryLayout014.goodFlags N q size)
        (PA17QueryLayout014.badFlags N q size) header) a).heap
    have hh := PA17QueryRanks011.program_capacityThroughout q (PA17QueryLayout014.capacityWords N q size)
      (PA17QueryLayout014.goodFlags N q size) (PA17QueryLayout014.badFlags N q size) header input
      (PA17QueryLayout014.capacity_before_queryRegions N q size).2.2.2.1 a hcapA
      (PA17QueryRanks011.program q (PA17QueryLayout014.goodFlags N q size)
        (PA17QueryLayout014.badFlags N q size) header).length le_rfl
    simpa only [List.take_length] using hh
  have hregions := PA17Query019.selector_regions N q size
  have hl := selector_layout B N q size rowId hsize hheap
  have hv : PA17QuerySelectWord029.ReadValuesBound size q (PA17QueryLayout014.countsBase N q size)
      (PA17QueryLayout014.labelBase N q size) header (PA17QueryBudget015.rowBase q size rowId.val) b.heap := by
    apply PA17QuerySelectWord029.ReadValuesBound.of_capacity size q _ _ _ _
      (PA17QueryLayout014.capacityWords N q size) b.heap hbi.row_pointer hcontrol.2.2
    · rw [hbi.node_pointer]
      exact UniformNormalizationRAM.encodedNode_le cache node
    · rw [hcontrol.2.1]; split_ifs <;> omega
    · intro target ht
      rw [hbi.counts ⟨target, ht⟩, IndexedDescent.usedCounts_get]
      simpa only [Fintype.card_fin] using Finset.card_le_univ (used ∩ cache.decode ⟨target, ht⟩)
    · intro target ht
      rw [hbl ⟨target, ht⟩]
      exact PA17QuerySelectWord029.encodeTool_le q _
    · exact (PA17QueryBudget015.row_fits_table N q size rowId).trans
        (PA17CellLayout003.table_le_capacityWords N q size)
    · exact hcapB
  have h3 := PA17QuerySelectWord029.prepared_program_numeric q full stage.val used B heapWords
    (PA17QueryLayout014.countsBase N q size) (PA17QueryLayout014.labelBase N q size) header
    (PA17QueryBudget015.rowBase q size rowId.val) (PA17QueryLayout014.childBase N q size) hl b hv (h2.final _ _ _ _ _)
  have hbudget : b.heap (header + 6) < q + 2 := by have := hcontrol.2.2; omega
  let budget : Fin (q + 2) := ⟨b.heap (header + 6), hbudget⟩
  let sourceSlot := rowId.val * (q + 2) + budget.val
  have hslot := PA17QueryBudget015.row_slot_bound N q rowId.val budget.val rowId.isLt budget.isLt
  have hsource : (sourceSlot + 1) * (size + 1) ≤ PA17QueryLayout014.childBase N q size :=
    (Nat.mul_le_mul_right (size + 1) (Nat.succ_le_of_lt hslot)).trans hregions.2.2.2
  have hptr : b.heap header + (size + 1) * b.heap (header + 6) = sourceSlot * (size + 1) := by
    rw [hbi.row_pointer]
    dsimp [PA17QueryBudget015.rowBase, sourceSlot, budget]
    ring
  have htool := PA17QuerySelectWord029.prepared_program_tool_le q full stage.val used counts
    (PA17QueryLayout014.countsBase N q size) (PA17QueryLayout014.labelBase N q size) header
    (PA17QueryLayout014.childBase N q size) sourceSlot hregions.1 hregions.2.1 hregions.2.2.1 hsource b hptr
    hbi.counts hbl node hbi.node_pointer
  have hf (address : Nat) (ha : address < PA17QueryLayout014.childBase N q size) : c.heap address = b.heap address := by
    change (execute rom (PA17QuerySelection010b.program size (PA17QueryLayout014.countsBase N q size)
      (PA17QueryLayout014.labelBase N q size) header (PA17QueryLayout014.childBase N q size)) b).heap address = _
    have hh := PA17QuerySelectionSafety020.program_prefixFrame rom size _ _ _ _ address ha b
      (PA17QuerySelection010b.program size (PA17QueryLayout014.countsBase N q size)
        (PA17QueryLayout014.labelBase N q size) header (PA17QueryLayout014.childBase N q size)).length le_rfl
    simpa only [List.take_length] using hh
  have hc2 : c.heap (header + 2) ≤ 2 * B := by
    rw [hf _ (by have := hl.header; omega), PA17Query019.ranks_frame rom N q size a _ (by omega)]
    exact ha2.trans (by have := hrLayout.q_bound; omega)
  have hc4 : c.heap (header + 4) ≤ q + 2 := by rw [hf _ (by have := hl.header; omega)]; exact hb4
  have hc5 : c.heap (header + 5) ≤ q + 2 := by rw [hf _ (by have := hl.header; omega)]; exact hb5
  have htoolAccess : PA17QueryLayout014.toolAddress N q size < heapWords := by
    have := PA17QueryLayout014.toolAddress_end N q size
    omega
  have h4 := PA17QueryRanksWord027.reply_numeric (2 * B) heapWords q header
    (PA17QueryLayout014.toolAddress N q size) input (by have := hrLayout.header_access; omega)
    (by have := hrLayout.header_bound; omega)
    htoolAccess (by omega) hrLayout.q_bound c (h3.final _ _ _ _ _) hc2 hc4 hc5 (htool.2.trans (by have := hrLayout.q_bound; omega))
  change NumericSafe (2 * B) heapWords input
    (PA17QueryBudget015.program N q size ++ PA17Query019.ranksProgram N q size ++
      PA17Query019.selectProgram N q size ++ PA17Query019.replyProgram N q size) state
  apply NumericSafe.append _ _ _ _ _ state
    (NumericSafe.append _ _ _ _ _ state (NumericSafe.append _ _ _ _ _ state h1 h2) ?_) ?_
  · rw [IndexedClosureRAM.execute_append]
    exact h3
  · rw [IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
    exact h4

theorem prepared_executionClaims (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1)) (used : Finset (Fin q))
    (heap : Nat → Nat) (htable : PhysicalTableCorrect q full heap)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) heap)
    (hfits : ∀ address < PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size,
      Fits (indexWidth 32 full.length q) (heap address)) :
    ExecutionClaims 32 full.length q
      (PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (queryROM q full stage.val used)
      (PA17Query019.program full.length q (prepareNormalization q full).indexed.nodes.size) (initial heap) := by
  have hn := prepared_program_numeric q full hq hlaminar stage used (initial heap) htable hcap
    (by intro register; exact Nat.zero_le _)
  apply PA17WordBounds023.executionClaims_of_numeric_prefix full.length q _ _ _ (initial heap) rfl
    (PA17WordBounds023.queryROM_wordsFit q full stage used)
    (PA17QueryFootprint025.prepared_query_footprint q full hq hlaminar stage used) hfits
  · intro count hc register
    simpa only [PA17QueryBudgetWord032.twice_bound] using hn.1 count hc register
  · exact hn.2

theorem prepared_queryClaims (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1)) (used : Finset (Fin q))
    (heap : Nat → Nat) (htable : PhysicalTableCorrect q full heap)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) heap)
    (hfits : ∀ address < PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size,
      Fits (indexWidth 32 full.length q) (heap address)) :
    QueryClaims PA17Implementation030.constant 32 PA17Implementation030.implementation q full hq
      (prepareNormalization q full).indexed.nodes.size
      (PA17QueryLayout014.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size) stage used heap :=
  PA17Implementation030.queryClaims_of_execution 32 q full hq hlaminar heap htable hcap stage used
    (prepared_executionClaims q full hq hlaminar stage used heap htable hcap hfits)

/-- Actual repeated queries on the previous query's heap, at the original
three incoming-heap conditions. There is no per-request execution oracle. -/
theorem prepared_requests_claims (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (heap : Nat → Nat) (htable : PhysicalTableCorrect q full heap)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q
      (prepareNormalization q full).indexed.nodes.size) heap)
    (hfits : ∀ address < PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size,
      Fits (indexWidth 32 full.length q) (heap address))
    (requests : List (Request q full.length)) (hrequests : requests.length ≤ full.length) :
    let size := (prepareNormalization q full).indexed.nodes.size
    pathCost PA17Implementation030.implementation q full size requests ≤
        PA17Implementation030.constant * full.length * queryWork q size ∧
      PathClaims PA17Implementation030.constant 32 PA17Implementation030.implementation q full hq size
        (PA17QueryLayout014.capacityWords full.length q size) (PA17QueryLayout014.heapWords full.length q size)
        requests heap ∧
      PhysicalTableCorrect q full (pathExecute PA17Implementation030.implementation q full size requests heap) := by
  apply PA17RequestPaths016.bounded_requests_claims PA17Implementation030.constant 32
    PA17Implementation030.implementation q full hq _ _ ?_ requests hrequests heap ⟨htable, hcap, hfits⟩
  intro fresh hfTable hfCap hfFits stage used
  exact prepared_queryClaims q full hq hlaminar stage used fresh hfTable hfCap hfFits

end PaperProofs.Structure.LaminarTree.PA17QueryWord033
