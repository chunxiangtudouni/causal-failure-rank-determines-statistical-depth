module
public import PaperProofs.Structure.PA17_GivenWord_031e
public import PaperProofs.Structure.PA17_Rolling_018C
public import PaperProofs.Structure.PA17_QueryTestsWord_028

/-! Actual two-row construction on its exact allocation: concrete metadata,
incidence matching and cell-prefix certificates composed from zero heap. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17GivenWord031f

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022 PA17Rolling018

def heapWords (q size : Nat) : Nat := capacityWords q size + PA17Rolling018B.indexWords q size

structure Layout (B q size : Nat) (rom : PhysicalROM) : Prop where
  heap_bound : heapWords q size ≤ B
  input_bound : rom.input.length ≤ B
  q_bound : q ≤ B
  size_bound : size ≤ B
  one_bound : 1 ≤ B

theorem parentHeap_bound {Tool : Type*} (cache : IndexedNodeCache Tool) (parents : Nat) (heap : Nat → Nat)
    (hp : PA17HeapAncestors001.ParentHeapFor cache parents heap) :
    ∀ encoded ≤ cache.nodes.size, heap (parents + encoded) ≤ cache.nodes.size := by
  intro encoded he
  cases encoded with
  | zero => rw [Nat.add_zero, hp.1]; exact Nat.zero_le _
  | succ index =>
    let node : cache.NodeId := ⟨index, by omega⟩
    rw [hp.2 node]
    exact UniformNormalizationRAM.encodedNode_le cache _

theorem cellLayout (B q size goodSlot : Nat) (rom : PhysicalROM) (hl : Layout B q size rom)
    (hsize : 0 < size) (hgood : goodSlot < 2 * (q + 2)) :
    PA17GivenWord031d.Layout B (heapWords q size) q (capacityWords q size) size
      (workBase q size) (base size goodSlot) (accumulatorBase q size) (metadataBase q size + size) (stageWord q size) := by
  have hcap : capacityWords q size ≤ heapWords q size := Nat.le_add_right _ _
  have hparent : metadataBase q size + size + size < heapWords q size := by
    unfold heapWords PA17Rolling018B.indexWords metadataBase; omega
  have hstage : stageWord q size < heapWords q size := by
    unfold heapWords PA17Rolling018B.indexWords stageWord metadataBase; omega
  refine {
    cap_access := hcap, cap_bound := hcap.trans hl.heap_bound,
    q_bound := hl.q_bound, size_bound := hl.size_bound, size_pos := hsize,
    work_region := by unfold capacityWords; omega,
    parent_access := hparent, parent_bound := hparent.le.trans hl.heap_bound,
    stage_access := hstage, stage_bound := hstage.le.trans hl.heap_bound,
    disjoint := work_parent_disjoint q size,
    good_region := ?_, accumulator := ?_ }
  · have hh := slot_word_lt_work q size goodSlot hgood size le_rfl
    unfold capacityWords
    omega
  · unfold capacityWords accumulatorBase
    omega

theorem freeSlot_numeric (q : Nat) (full : List (Finset (Fin q))) (B slot : Nat)
    (rom : PhysicalROM) (hl : Layout B q (prepareNormalization q full).indexed.nodes.size rom)
    (hs : slot < 2 * (q + 2)) (state : State) (hi : RegistersLE (2 * B) state)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    NumericSafe (2 * B) (heapWords q (prepareNormalization q full).indexed.nodes.size) rom
      (freeSlot q (prepareNormalization q full).indexed.nodes.size slot) state := by
  let size := (prepareNormalization q full).indexed.nodes.size
  have hB : heapWords q size ≤ B := hl.heap_bound
  have hmeta : metadataBase q size + size ≤ heapWords q size := by
    unfold heapWords metadataBase PA17Rolling018B.indexWords; omega
  have htarget : base size slot + 1 + size ≤ heapWords q size := by
    have hh := slot_word_lt_work q size slot hs size le_rfl
    unfold heapWords capacityWords
    omega
  have hp := PA17GivenWord031a.copyWords_numeric B (heapWords q size) size (metadataBase q size) (base size slot + 1) rom
    hmeta (hmeta.trans hl.heap_bound) htarget (htarget.trans hl.heap_bound) state hi (by
      intro index hindex
      exact (UniformTreeMetadataRAM.metadata_card_bound q full _ state.heap hm ⟨index, hindex⟩).trans (by have := hl.q_bound; omega))
  rw [freeSlot]
  apply NumericSafe.append _ _ rom _ _ state hp
  exact PA17GivenWord031a.constantBlock_numeric B (heapWords q size) (base size slot) 1 rom
    ⟨by omega, by omega⟩ (by have := hl.one_bound; omega) _ (NumericSafe.final _ _ _ _ _ hp)

theorem freeSlots_numeric (q : Nat) (full : List (Finset (Fin q))) (B : Nat)
    (rom : PhysicalROM) (hl : Layout B q (prepareNormalization q full).indexed.nodes.size rom)
    (slots : List Nat) (hs : ∀ slot ∈ slots, slot < 2 * (q + 2)) (state : State) (hi : RegistersLE (2 * B) state)
    (hm : UniformTreeMetadataRAM.MetadataCorrect q full (metadataBase q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    NumericSafe (2 * B) (heapWords q (prepareNormalization q full).indexed.nodes.size) rom
      (slots.flatMap (freeSlot q (prepareNormalization q full).indexed.nodes.size)) state := by
  induction slots generalizing state with
  | nil => exact PA17GivenWord031a.NumericSafe.nil _ _ rom state hi
  | cons head later ih =>
    rw [List.flatMap_cons]
    have hh := freeSlot_numeric q full B head rom hl (hs head List.mem_cons_self) state hi hm
    exact NumericSafe.append _ _ rom _ _ state hh
      (ih (fun slot hm => hs slot (List.mem_cons_of_mem _ hm)) _ (hh.final _ _ _ _ _)
        (freeSlot_metadata q full head (hs head List.mem_cons_self) rom.semantic state hm))

theorem prepareProgram_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used))
    (state : State) (hi : RegistersLE (2 * B) state) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (prepareProgram full.length q size) state := by
  intro size
  have hmeta : metadataBase q size + 3 * size + 1 ≤ heapWords q size := by
    unfold heapWords metadataBase PA17Rolling018B.indexWords; omega
  have hm := PA17QueryDataWord024c.prepared_program_numeric q full 0 used B (heapWords q size) (metadataBase q size)
    ⟨hl.input_bound, hmeta.trans hl.heap_bound, hmeta, hl.q_bound⟩ state hi
  rw [prepareProgram]
  apply NumericSafe.append _ _ _ _ _ state hm
  exact freeSlots_numeric q full B (queryROM q full 0 used) hl (List.range (2 * (q + 2)))
    (fun _ hn => List.mem_range.mp hn) _ (hm.final _ _ _ _ _)
    (PA17QueryMetadata010.prepared_program_metadata q full hq hlaminar 0 used _ state)

theorem stageProgram_numeric (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (B : Nat) (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used))
    (stage : Fin full.length) (state : State) (hi : RegistersLE (2 * B) state) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (stageProgram full.length q size stage.val) state := by
  intro size
  have hstage : stageWord q size < heapWords q size := by
    unfold stageWord metadataBase heapWords PA17Rolling018B.indexWords; omega
  exact PA17GivenWord031e.matchedStage_numeric B (heapWords q size) full.length q size stage.val (stageWord q size)
    (queryROM q full 0 used) (PA17GivenWord031e.queryROM_data q full ⟨0, by omega⟩ used)
    hl.input_bound hl.q_bound hl.size_bound hl.one_bound stage.isLt ⟨hstage, hstage.le.trans hl.heap_bound⟩ state hi

theorem cell_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used))
    (stage : Fin full.length) (budget : Fin (q + 2)) (state : State) (hr : RegistersLE (2 * B) state)
    (hi : Invariant q full state) (hs : StageReady q full hq stage state)
    (hb : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hc : PA17Rolling018C.PhysicalCard q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (cellProgram q size stage.val budget.val) state := by
  intro size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hp := parentHeap_bound (prepareNormalization q full).indexed _ state.heap
    (PA17HeapAncestors001.metadata_parentHeapFor q full _ state.heap hi.1)
  have hstage : state.heap (stageWord q size) ≤ size := by
    rw [hs]
    exact UniformNormalizationRAM.encodedNode_le _ _
  have hsafe := PA17Rolling018C.cell_safe q full hq hlaminar used stage budget state hi hs hb hc
  apply PA17GivenWord031d.cell_numeric_of_capacity B (heapWords q size) q (capacityWords q size) size (workBase q size)
    (base size (slot q (stage.val + 1) budget.val)) (base size (slot q (stage.val + 1) (budget.val - 1)))
    (accumulatorBase q size) (metadataBase q size + size) (stageWord q size) (base size (slot q stage.val budget.val))
    (queryROM q full 0 used) (cellLayout B q size _ _ hl hsize (slot_lt q _ budget.val budget.isLt))
    (PA17GivenWord031b.queryROM_internalData q full 0 used)
  · have hh := slot_word_lt_work q size (slot q (stage.val + 1) (budget.val - 1))
      (slot_lt q _ _ (by have := budget.isLt; omega)) size le_rfl
    unfold capacityWords; omega
  · have hh := slot_word_lt_work q size (slot q stage.val budget.val) (slot_lt q _ _ budget.isLt) size le_rfl
    unfold capacityWords; omega
  · intro left hl right hr
    exact (work_slot_disjoint q size _ (slot_lt q _ _ (by have := budget.isLt; omega)) right hr left hl).symm
  · exact work_slot_disjoint q size _ (slot_lt q _ _ budget.isLt)
  · unfold metadataBase; omega
  · unfold stageWord metadataBase; omega
  · exact hr
  · exact hstage
  · exact hp
  · exact hsafe.1

theorem budgets_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used))
    (stage : Fin full.length) (budgets : List Nat) (hbudgets : ∀ budget ∈ budgets, 0 < budget ∧ budget < q + 2)
    (state : State) (hr : RegistersLE (2 * B) state) (hi : Invariant q full state) (hs : StageReady q full hq stage state)
    (hnext : RowReady q full ⟨stage.val + 1, by omega⟩ state)
    (hb : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hc : PA17Rolling018C.PhysicalCard q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (budgets.flatMap (cellProgram q size stage.val)) state := by
  dsimp only
  induction budgets generalizing state with
  | nil => exact PA17GivenWord031a.NumericSafe.nil _ _ _ state hr
  | cons head later ih =>
    have hh := hbudgets head List.mem_cons_self
    have hn := cell_numeric q full hq hlaminar used B hl stage ⟨head, hh.2⟩ state hr hi hs hb hc
    have hm := cell_preserves_invariant q full hq hlaminar used stage ⟨head, hh.2⟩ hh.1 state hi hs hnext
    have hsafe := PA17Rolling018C.cell_safe q full hq hlaminar used stage ⟨head, hh.2⟩ state hi hs hb hc
    rw [List.flatMap_cons]
    apply NumericSafe.append _ _ _ _ _ state hn
    exact ih (fun budget hm => hbudgets budget (List.mem_cons_of_mem _ hm)) _ (hn.final _ _ _ _ _)
      hm.1 hm.2.1 hm.2.2.1 (by simpa only [List.take_length] using hsafe.1 _ le_rfl) hsafe.2

theorem rowProgram_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used))
    (stage : Fin full.length) (state : State) (hr : RegistersLE (2 * B) state) (hi : Invariant q full state)
    (hnext : RowReady q full ⟨stage.val + 1, by omega⟩ state)
    (hb : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hc : PA17Rolling018C.PhysicalCard q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (rowProgram full.length q size stage.val) state := by
  intro size
  have hn := stageProgram_numeric q full used B hl stage state hr
  have hsafe := PA17Rolling018C.stageProgram_capacityThroughout q full.length size stage.val (queryROM q full 0 used) state hb
  rw [rowProgram]
  apply NumericSafe.append _ _ _ _ _ state hn
  exact budgets_numeric q full hq hlaminar used B hl stage (positiveBudgets q)
    (fun budget hm => (positiveBudgets_mem q budget).mp hm) _ (hn.final _ _ _ _ _)
    (stageProgram_preserves_invariant q full used stage.val state hi) (prepared_stageProgram q full hq used stage state)
    (stageProgram_preserves_row q full used stage.val _ state hnext)
    (by simpa only [List.take_length] using hsafe _ le_rfl)
    (PA17Rolling018C.stageProgram_physicalCard q full stage.val _ state hc)

theorem scheduleProgram_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used))
    (count : Nat) (hcount : count ≤ full.length) (state : State) (hr : RegistersLE (2 * B) state) (hi : Invariant q full state)
    (hrow : RowReady q full ⟨count, by omega⟩ state)
    (hb : CapacityPrefixBounded q (capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hc : PA17Rolling018C.PhysicalCard q full state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (scheduleProgram full.length q size count) state := by
  dsimp only
  induction count generalizing state with
  | zero => exact PA17GivenWord031a.NumericSafe.nil _ _ _ state hr
  | succ count ih =>
    have hs : count < full.length := by omega
    have hn := rowProgram_numeric q full hq hlaminar used B hl ⟨count, hs⟩ state hr hi hrow hb hc
    have hm := PA17Rolling018C.rowProgram_safe q full hq hlaminar used ⟨count, hs⟩ state hi hrow hb hc
    rw [scheduleProgram_succ]
    apply NumericSafe.append _ _ _ _ _ state hn
    exact ih (by omega) _ (hn.final _ _ _ _ _) hm.2.2.1 hm.2.2.2
      (by simpa only [List.take_length] using hm.1 _ le_rfl) hm.2.1

theorem prepared_buildProgram_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (buildProgram full.length q size) (initial (fun _ => 0)) := by
  intro size
  have hn := prepareProgram_numeric q full hq hlaminar used B hl (initial (fun _ => 0)) (fun _ => Nat.zero_le _)
  let seed := execute (queryROM q full 0 used).semantic (prepareProgram full.length q size) (initial (fun _ => 0))
  have hp := prepared_prepare q full hq hlaminar used (initial (fun _ => 0))
  have hsafe := PA17Rolling018C.prepareProgram_safe q full hq hlaminar used (initial (fun _ => 0)) (fun _ _ => Nat.zero_le _)
  have hi : Invariant q full seed := by
    refine ⟨hp.1, ?_, ?_⟩
    · intro index hs
      exact tag_le_one _ _ _ _ (hp.2 index hs)
    · intro stage
      exact hp.2 _ (slot_lt q stage 0 (by omega))
  have hrow : RowReady q full ⟨full.length, by omega⟩ seed := by
    intro budget
    unfold CellReady
    rw [storedRow_terminal]
    exact hp.2 _ (slot_lt q full.length budget.val budget.isLt)
  rw [buildProgram]
  apply NumericSafe.append _ _ _ _ _ _ hn
  exact scheduleProgram_numeric q full hq hlaminar used B hl full.length le_rfl seed (hn.final _ _ _ _ _) hi hrow
    (by simpa only [List.take_length] using hsafe.1 _ le_rfl) hsafe.2

end PaperProofs.Structure.LaminarTree.PA17GivenWord031f
