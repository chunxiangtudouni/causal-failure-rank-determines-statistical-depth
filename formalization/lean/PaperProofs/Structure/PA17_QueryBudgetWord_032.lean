module

public import PaperProofs.Structure.PA17_QueryBudget_015
public import PaperProofs.Structure.PA17_QueryDataWord_024b
public import PaperProofs.Structure.PA17_QueryDataWord_024c
public import PaperProofs.Structure.PA17_QueryHeaderWord_022
public import PaperProofs.Structure.PA17_QueryTestsWord_028

/-! Actual prefix register/access safety for the complete dynamic budget
pass. Freshly executed preparation supplies the local count/parent values;
only the original capacity region is bounded in the incoming heap. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryBudgetWord032

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022

structure Layout (B N q size : Nat) (rom : PhysicalROM) : Prop where
  heap_bound : PA17QueryLayout014.heapWords N q size ≤ B
  input_bound : rom.input.length ≤ B
  q_bound : q ≤ B
  N_bound : N + 1 ≤ B

theorem regions_fit (N q size : Nat) :
    PA17QueryLayout014.metadataBase N q size + 3 * size + 1 ≤ PA17QueryLayout014.heapWords N q size ∧
      PA17QueryLayout014.labelBase N q size + size ≤ PA17QueryLayout014.heapWords N q size ∧
      PA17QueryLayout014.countsBase N q size + size ≤ PA17QueryLayout014.heapWords N q size ∧
      PA17QueryLayout014.header N q size + 16 ≤ PA17QueryLayout014.heapWords N q size ∧
      PA17QueryLayout014.badFlags N q size + q + 2 ≤ PA17QueryLayout014.heapWords N q size ∧
      size + 1 ≤ PA17QueryLayout014.heapWords N q size ∧
      tableWords N q size ≤ PA17QueryLayout014.heapWords N q size ∧
      1 ≤ PA17QueryLayout014.heapWords N q size := by
  dsimp [PA17QueryLayout014.metadataBase, PA17QueryLayout014.labelBase,
    PA17QueryLayout014.countsBase, PA17QueryLayout014.header, PA17QueryLayout014.goodFlags,
    PA17QueryLayout014.badFlags, PA17QueryLayout014.heapWords, PA17QueryLayout014.indexWords,
    PA17QueryLayout014.capacityWords, PA17CellLayout003.capacityWords, PA17CellLayout003.workBase]
  omega

theorem Layout.metadata (B N q size : Nat) (rom : PhysicalROM) (hl : Layout B N q size rom) :
    PA17QueryDataWord024c.Layout B (PA17QueryLayout014.heapWords N q size) q size
      (PA17QueryLayout014.metadataBase N q size) rom :=
  ⟨hl.input_bound, (regions_fit N q size).1.trans hl.heap_bound, (regions_fit N q size).1, hl.q_bound⟩

theorem Layout.leaf (B N q size : Nat) (rom : PhysicalROM) (hl : Layout B N q size rom) :
    PA17QueryDataWord024a.Layout B (PA17QueryLayout014.heapWords N q size) q size
      (PA17QueryLayout014.labelBase N q size) rom :=
  ⟨hl.input_bound, (regions_fit N q size).2.1.trans hl.heap_bound, (regions_fit N q size).2.1,
    hl.q_bound, (regions_fit N q size).2.2.2.2.2.2.2.trans hl.heap_bound⟩

theorem Layout.counts (B N q size : Nat) (rom : PhysicalROM) (hl : Layout B N q size rom) :
    PA17QueryDataWord024a.Layout B (PA17QueryLayout014.heapWords N q size) q size
      (PA17QueryLayout014.countsBase N q size) rom :=
  ⟨hl.input_bound, (regions_fit N q size).2.2.1.trans hl.heap_bound, (regions_fit N q size).2.2.1,
    hl.q_bound, (regions_fit N q size).2.2.2.2.2.2.2.trans hl.heap_bound⟩

theorem Layout.header (B N q size : Nat) (rom : PhysicalROM) (hl : Layout B N q size rom) :
    PA17QueryHeaderWord022.Layout B (PA17QueryLayout014.heapWords N q size) N q size
      (PA17QueryLayout014.header N q size) rom := by
  have hr := regions_fit N q size
  exact ⟨by omega, hl.input_bound, hr.2.2.2.2.2.2.1.trans hl.heap_bound,
    hr.2.2.2.1.trans hl.heap_bound, hl.q_bound, hr.2.2.2.2.2.1.trans hl.heap_bound,
    hl.N_bound, hr.2.2.2.2.2.2.2.trans hl.heap_bound⟩

theorem Layout.tests (B N q size : Nat) (rom : PhysicalROM) (hl : Layout B N q size rom) (hs : 0 < size) :
    PA17QueryTestsWord028.Layout B (PA17QueryLayout014.heapWords N q size) size q
      (PA17QueryLayout014.goodFlags N q size) (PA17QueryLayout014.goodFlags N q size)
      (PA17QueryLayout014.badFlags N q size) := by
  have hr := regions_fit N q size
  have hh := hl.heap_bound
  have hgood : PA17QueryLayout014.goodFlags N q size + q + 2 ≤ PA17QueryLayout014.heapWords N q size := by
    dsimp [PA17QueryLayout014.badFlags] at hr
    omega
  have hgb : PA17QueryLayout014.goodFlags N q size ≤ PA17QueryLayout014.badFlags N q size := by
    dsimp [PA17QueryLayout014.badFlags]
    omega
  constructor
  all_goals first | exact hl.q_bound | exact hs | exact le_rfl | exact hgb | omega

theorem prepared_prepareProgram_numeric (q : Nat) (full : List (Finset (Fin q)))
    (stage : Nat) (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B full.length q (prepareNormalization q full).indexed.nodes.size (queryROM q full stage used))
    (state : State) (hi : RegistersLE (2 * B) state) :
    NumericSafe (2 * B) (PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (queryROM q full stage used) (PA17QueryLayout014.prepareProgram full.length q (prepareNormalization q full).indexed.nodes.size) state := by
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := queryROM q full stage used
  let a := execute rom.semantic (PA17QueryMetadata010.program full.length q size (PA17QueryLayout014.metadataBase full.length q size)) state
  let b := execute rom.semantic (PA17LeafLabels005.program full.length q size (PA17QueryLayout014.labelBase full.length q size)) a
  have h1 := PA17QueryDataWord024c.prepared_program_numeric q full stage used B _ _ (hl.metadata _ _ _ _ _) state hi
  have h2 := PA17QueryDataWord024b.prepared_leafProgram_numeric q full stage used B _ _ (hl.leaf _ _ _ _ _) a (h1.final _ _ _ _ _)
  have h3 := PA17QueryDataWord024a.prepared_program_numeric q full stage used B _ _ (hl.counts _ _ _ _ _) b (h2.final _ _ _ _ _)
  dsimp only [PA17QueryLayout014.prepareProgram, PA17QueryPrepare013.program]
  rw [List.append_assoc]
  exact NumericSafe.append _ _ _ _ _ _ h1 (NumericSafe.append _ _ _ _ _ _ h2 h3)

theorem prepared_readValues (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1)) (used : Finset (Fin q))
    (state : State)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let prepared := execute (queryROM q full stage.val used).semantic (PA17QueryLayout014.prepareProgram full.length q size) state
    let fresh := execute (queryROM q full stage.val used).semantic
      (PA17QueryHeader009.program full.length q size (PA17QueryLayout014.header full.length q size)) prepared
    PA17QueryTestsWord028.ReadValuesBound size q (PA17QueryLayout014.header full.length q size)
      (PA17QueryLayout014.countsBase full.length q size) (PA17QueryLayout014.parentBase full.length q size)
      (PA17QueryLayout014.header full.length q size + 1)
      (PA17QueryBudget015.rowBase q size (PA17QueryBudget015.rowIndex full stage).val) fresh.heap := by
  intro size prepared fresh
  have hp := PA17QueryLayout014.prepared_prepareProgram_correct q full hq hlaminar stage.val used state
  have hh := PA17QueryHeader009.prepared_program_correct q full hq stage used (PA17QueryLayout014.header full.length q size) prepared
  have hf (address : Nat) (ha : address < PA17QueryLayout014.header full.length q size) : fresh.heap address = prepared.heap address :=
    PA17QueryBudget015.header_below_frame _ _ _ _ prepared address ha
  have hc : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q size) fresh.heap := by
    intro address ha
    rw [hf address (ha.trans_le (PA17QueryLayout014.capacity_before_queryRegions full.length q size).2.2.2.1)]
    have hr := PA17QueryLayout014.prepareProgram_prefixFrame (queryROM q full stage.val used).semantic full.length q size address ha state
      (PA17QueryLayout014.prepareProgram full.length q size).length le_rfl
    have he : prepared.heap address = state.heap address := by simpa only [List.take_length] using hr
    rw [he]
    exact hcap address ha
  apply PA17QueryTestsWord028.ReadValuesBound.of_capacity size q _ _ _ _ _ _ fresh.heap
  · exact hh.1.trans (PA17QueryBudget015.header_rowPointer q full stage size)
  · rw [hh.2.1]
    rw [PA17QueryBudget015.header_nodeWord]
    exact UniformNormalizationRAM.encodedNode_le _ _
  · intro node hn
    rw [hf _ (by dsimp [PA17QueryLayout014.header]; omega), hp.2.2 ⟨node, hn⟩, IndexedDescent.usedCounts_get]
    simpa only [Fintype.card_fin] using (Finset.card_le_univ (used ∩ (prepareNormalization q full).indexed.decode ⟨node, hn⟩))
  · intro encoded he
    rw [hf _ (by
      dsimp [PA17QueryLayout014.parentBase, PA17QueryLayout014.header, PA17QueryLayout014.countsBase,
        PA17QueryLayout014.labelBase]
      omega)]
    have hparent := PA17HeapAncestors001.metadata_parentHeapFor q full _ prepared.heap hp.1
    change prepared.heap (PA17QueryLayout014.parentBase full.length q size) = 0 ∧
      (∀ node : (prepareNormalization q full).indexed.NodeId,
        prepared.heap (PA17QueryLayout014.parentBase full.length q size + (node.val + 1)) =
          encodedNode (prepareNormalization q full).indexed ((prepareNormalization q full).indexed.parents.get node)) at hparent
    by_cases hz : encoded = 0
    · subst encoded
      simpa only [Nat.add_zero, hparent.1] using (Nat.zero_le size)
    · obtain ⟨node, hnode⟩ : ∃ node : (prepareNormalization q full).indexed.NodeId, node.val + 1 = encoded :=
        ⟨⟨encoded - 1, by omega⟩, by change encoded - 1 + 1 = encoded; omega⟩
      rw [← hnode, hparent.2 node]
      exact UniformNormalizationRAM.encodedNode_le _ _
  · exact (PA17QueryBudget015.row_fits_table full.length q size (PA17QueryBudget015.rowIndex full stage)).trans
      (PA17CellLayout003.table_le_capacityWords full.length q size)
  · exact hc

theorem prepared_program_numeric_of_layout (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1)) (used : Finset (Fin q))
    (B : Nat)
    (hl : Layout B full.length q (prepareNormalization q full).indexed.nodes.size (queryROM q full stage.val used))
    (state : State) (hi : RegistersLE (2 * B) state)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    NumericSafe (2 * B) (PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (queryROM q full stage.val used) (PA17QueryBudget015.program full.length q (prepareNormalization q full).indexed.nodes.size) state := by
  let size := (prepareNormalization q full).indexed.nodes.size
  let rom := queryROM q full stage.val used
  let a := execute rom.semantic (PA17QueryLayout014.prepareProgram full.length q size) state
  let b := execute rom.semantic (PA17QueryHeader009.program full.length q size (PA17QueryLayout014.header full.length q size)) a
  have hs : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have h1 := prepared_prepareProgram_numeric q full stage.val used B hl state hi
  have h2 := PA17QueryHeaderWord022.program_numeric B _ full.length q size _ stage.val rom
    (hl.header _ _ _ _ _) (PA17QueryHeaderWord022.queryROM_data q full stage used) a (h1.final _ _ _ _ _)
  have h3 := PA17QueryTestsWord028.program_numeric B _ size q _ _ _ _ _ _ _ _ rom (hl.tests _ _ _ _ _ hs)
    (PA17QueryBudget015.readBounds full.length q size (PA17QueryBudget015.rowIndex full stage)) b
    (prepared_readValues q full hq hlaminar stage used state hcap) (h2.final _ _ _ _ _)
  dsimp only [PA17QueryBudget015.program, PA17QueryBudget015.testsProgram]
  rw [List.append_assoc]
  exact NumericSafe.append _ _ _ _ _ _ h1 (NumericSafe.append _ _ _ _ _ _ h2 h3)

def bound (N q : Nat) : Nat := 32768 * (N + q + 2) ^ 3

theorem twice_bound (N q : Nat) : 2 * bound N q = 65536 * (N + q + 2) ^ 3 := by
  dsimp [bound]
  ring

theorem powers_dominate (N q : Nat) :
    1 ≤ (N + q + 2) ^ 3 ∧ N + q + 2 ≤ (N + q + 2) ^ 3 ∧
      (N + q + 2) ^ 2 ≤ (N + q + 2) ^ 3 := by
  let base := N + q + 2
  have hb : 1 ≤ base := by dsimp [base]; omega
  have hs : base ≤ base ^ 2 := by
    simpa only [Nat.mul_one, pow_two] using Nat.mul_le_mul_left base hb
  have hc : base ^ 2 ≤ base ^ 3 := by
    change base ^ 2 ≤ base ^ 2 * base
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (base ^ 2) hb
  exact ⟨le_trans hb (hs.trans hc), hs.trans hc, hc⟩

theorem heapWords_le_cube (N q size : Nat) (hsize : size ≤ N + q + 1) :
    PA17QueryLayout014.heapWords N q size ≤ 36 * (N + q + 2) ^ 3 := by
  let base := N + q + 2
  have hN : N + 1 ≤ base := by dsimp [base]; omega
  have hq : q + 2 ≤ base := by dsimp [base]; omega
  have ht : size + 1 ≤ base := by dsimp [base]; omega
  have htable : (N + 1) * (q + 2) * (size + 1) ≤ base ^ 3 := by
    calc
      _ ≤ (base * base) * base := Nat.mul_le_mul (Nat.mul_le_mul hN hq) ht
      _ = base ^ 3 := by ring
  have hp := powers_dominate N q
  change 1 ≤ base ^ 3 ∧ base ≤ base ^ 3 ∧ base ^ 2 ≤ base ^ 3 at hp
  dsimp [PA17QueryLayout014.heapWords, PA17QueryLayout014.capacityWords,
    PA17CellLayout003.capacityWords, PA17CellLayout003.workBase, tableWords, cells,
    PA17QueryLayout014.indexWords]
  change (N + 1) * (q + 2) * (size + 1) + 2 * (size + 1) + (6 * size + N + 2 * q + 24) ≤ 36 * base ^ 3
  nlinarith

theorem layout_of_sizeBound (N q size : Nat) (rom : PhysicalROM)
    (hsize : size ≤ N + q + 1) (hlen : rom.input.length = 4 + N * q + size * q + q) :
    Layout (bound N q) N q size rom := by
  let base := N + q + 2
  have hN : N ≤ base := by dsimp [base]; omega
  have hq : q ≤ base := by dsimp [base]; omega
  have ht : size ≤ base := by dsimp [base]; omega
  have hNq : N * q ≤ base ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul hN hq
  have htq : size * q ≤ base ^ 2 := by simpa only [pow_two] using Nat.mul_le_mul ht hq
  have hp := powers_dominate N q
  change 1 ≤ base ^ 3 ∧ base ≤ base ^ 3 ∧ base ^ 2 ≤ base ^ 3 at hp
  have hh := heapWords_le_cube N q size hsize
  change PA17QueryLayout014.heapWords N q size ≤ 36 * base ^ 3 at hh
  constructor
  · change PA17QueryLayout014.heapWords N q size ≤ 32768 * base ^ 3
    omega
  · rw [hlen]
    change 4 + N * q + size * q + q ≤ 32768 * base ^ 3
    nlinarith
  · change q ≤ 32768 * base ^ 3
    omega
  · change N + 1 ≤ 32768 * base ^ 3
    dsimp only [base] at hN
    have hNb : N + 1 ≤ base := by dsimp [base]; omega
    omega

theorem prepared_layout (q : Nat) (full : List (Finset (Fin q))) (stage : Nat) (used : Finset (Fin q)) :
    Layout (bound full.length q) full.length q (prepareNormalization q full).indexed.nodes.size (queryROM q full stage used) :=
  layout_of_sizeBound full.length q _ _ (prepared_indexed_size_le q full)
    (PA17QueryDataWord024a.queryROM_data q full stage used).input_length

theorem prepared_program_numeric (q : Nat) (full : List (Finset (Fin q)))
    (hq : 0 < q) (hlaminar : LaminarSchedule full) (stage : Fin (full.length + 1)) (used : Finset (Fin q))
    (state : State) (hi : RegistersLE (2 * bound full.length q) state)
    (hcap : CapacityPrefixBounded q (PA17QueryLayout014.capacityWords full.length q (prepareNormalization q full).indexed.nodes.size) state.heap) :
    NumericSafe (2 * bound full.length q)
      (PA17QueryLayout014.heapWords full.length q (prepareNormalization q full).indexed.nodes.size)
      (queryROM q full stage.val used) (PA17QueryBudget015.program full.length q (prepareNormalization q full).indexed.nodes.size) state :=
  prepared_program_numeric_of_layout q full hq hlaminar stage used (bound full.length q)
    (prepared_layout q full stage.val used) state hi hcap

end PaperProofs.Structure.LaminarTree.PA17QueryBudgetWord032
