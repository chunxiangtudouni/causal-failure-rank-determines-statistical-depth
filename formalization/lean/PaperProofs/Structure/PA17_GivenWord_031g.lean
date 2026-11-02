module
public import PaperProofs.Structure.PA17_GivenWord_031f
public import PaperProofs.Structure.PA17_QueryFootprint_025

/-! Actual raw-used count/test/rank finish on the exact rolling allocation. -/
@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000
namespace PaperProofs.Structure.LaminarTree.PA17GivenWord031g

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17QueryHeaderWord022 PA17Rolling018B
open PA17GivenWord031f

theorem countProgram_numeric (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used))
    (state : State) (hi : RegistersLE (2 * B) state) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (countProgram full.length q size) state := by
  intro size
  have hrow : rowPointer q size < heapWords q size := by
    unfold rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase heapWords indexWords; omega
  have hcounts : countsBase q size + size ≤ heapWords q size := by
    unfold countsBase rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase heapWords indexWords; omega
  have hclear := PA17GivenWord031a.clearBlock_numeric B (heapWords q size) (rowPointer q size) (queryROM q full 0 used)
    ⟨hrow, hrow.le.trans hl.heap_bound⟩ state hi
  rw [countProgram]
  apply NumericSafe.append _ _ _ _ _ state hclear
  exact PA17QueryDataWord024a.prepared_program_numeric q full 0 used B (heapWords q size) (countsBase q size)
    ⟨hl.input_bound, hcounts.trans hl.heap_bound, hcounts, hl.q_bound, hl.one_bound⟩ _ (hclear.final _ _ _ _ _)

theorem testsLayout (q size B : Nat) (rom : PhysicalROM) (hl : Layout B q size rom) (hsize : 0 < size) :
    PA17QueryTestsWord028.Layout B (heapWords q size) size q (goodFlags q size) (goodFlags q size) (badFlags q size) := by
  have hg : goodFlags q size + q + 2 ≤ heapWords q size := by
    unfold goodFlags countsBase rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase heapWords indexWords; omega
  have hb : badFlags q size + q + 2 ≤ heapWords q size := by
    unfold badFlags goodFlags countsBase rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase heapWords indexWords; omega
  exact ⟨(Nat.le_add_right _ (q + 2)).trans (hg.trans hl.heap_bound), (Nat.le_add_right _ (q + 2)).trans hg,
    hl.q_bound, hl.size_bound, hsize, le_rfl, by unfold badFlags; omega,
    hg.trans hl.heap_bound, hb.trans hl.heap_bound, hg, hb⟩

theorem countProgram_readValues (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (state : State) (hi : PA17Rolling018.Invariant q full state)
    (hb : CapacityPrefixBounded q (PA17Rolling018.capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hrow : ∀ budget : Fin (q + 2), readEntry (prepareNormalization q full).indexed.nodes.size budget.val state.heap =
      (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (queryROM q full 0 used).semantic (countProgram full.length q cache.nodes.size) state
    PA17QueryTestsWord028.ReadValuesBound cache.nodes.size q (rowPointer q cache.nodes.size) (countsBase q cache.nodes.size)
      (parentBase q cache.nodes.size) (parentBase q cache.nodes.size) 0 result.heap := by
  intro cache result
  have hin := countProgram_inputs q full used state hi hrow
  have hc : CapacityPrefixBounded q (PA17Rolling018.capacityWords q cache.nodes.size) result.heap := by
    intro address ha
    have hf := countProgram_prefixFrame (queryROM q full 0 used).semantic full.length q cache.nodes.size address
      (by unfold rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase; omega)
      state (countProgram full.length q cache.nodes.size).length le_rfl
    rw [List.take_length] at hf
    rw [hf]
    exact hb address ha
  refine ⟨hin.row_pointer, ?_, ?_, parentHeap_bound cache _ _ hin.parents, ?_⟩
  · rw [hin.node_pointer]
    exact Nat.zero_le _
  · intro node hn
    rw [hin.counts ⟨node, hn⟩, IndexedDescent.usedCounts_get]
    simpa only [Fintype.card_fin] using Finset.card_le_univ (used ∩ cache.decode ⟨node, hn⟩)
  · intro budget offset ho
    have hh := PA17Rolling018.slot_word_lt_work q cache.nodes.size budget.val
      (by have := budget.isLt; omega) offset ho
    apply hc
    dsimp only [PA17Rolling018.base] at hh
    unfold PA17Rolling018.capacityWords
    omega

theorem finishProgram_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used))
    (state : State) (hr : RegistersLE (2 * B) state) (hi : PA17Rolling018.Invariant q full state)
    (hb : CapacityPrefixBounded q (PA17Rolling018.capacityWords q (prepareNormalization q full).indexed.nodes.size) state.heap)
    (hrow : ∀ budget : Fin (q + 2), readEntry (prepareNormalization q full).indexed.nodes.size budget.val state.heap =
      (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (finishProgram full.length q size) state := by
  intro size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hcounts := countProgram_numeric q full used B hl state hr
  have ht := PA17QueryTestsWord028.program_numeric B (heapWords q size) size q (rowPointer q size) (countsBase q size)
    (parentBase q size) (parentBase q size) 0 (goodFlags q size) (goodFlags q size) (badFlags q size)
    (queryROM q full 0 used) (testsLayout q size B _ hl hsize) (readBounds q size)
    _ (countProgram_readValues q full used state hi hb hrow) (hcounts.final _ _ _ _ _)
  have hleft := NumericSafe.append _ _ _ _ _ state hcounts ht
  have hg : goodFlags q size + (q + 2) ≤ heapWords q size := by
    unfold goodFlags countsBase rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase heapWords indexWords; omega
  have hrank := PA17Rolling018B.lastWord_allocated q size
  have hqB : q + 2 ≤ B := by have := hg.trans hl.heap_bound; omega
  have hn := PA17QueryRanksWord027.rankProgram_numeric (2 * B) (heapWords q size) q (goodFlags q size) (rankWord q size)
    (queryROM q full 0 used) hg (by have := hg.trans hl.heap_bound; omega)
    hrank (by have := hrank.le.trans hl.heap_bound; omega) (by omega)
    (execute (queryROM q full 0 used).semantic (countProgram full.length q size ++ testProgram q size) state)
    (hleft.final _ _ _ _ _) (by
      intro budget hbudget
      have hf := (prepared_finish_flags q full used state hi hrow ⟨budget, hbudget⟩).1
      rw [IndexedClosureRAM.execute_append]
      rw [hf]
      unfold bit
      split_ifs <;> omega)
  rw [finishProgram]
  exact NumericSafe.append _ _ _ _ _ state hleft hn

theorem prepared_program_numeric (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (B : Nat)
    (hl : Layout B q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    NumericSafe (2 * B) (heapWords q size) (queryROM q full 0 used) (program full.length q size) (initial (fun _ => 0)) := by
  intro size
  have hn := prepared_buildProgram_numeric q full hq hlaminar used B hl
  have hc := PA17Rolling018C.prepared_build_safe q full hq hlaminar used
  have hs := PA17Rolling018.prepared_build_rowZero q full hq hlaminar used
  rw [program]
  apply NumericSafe.append _ _ _ _ _ _ hn
  exact finishProgram_numeric q full hq used B hl _ (hn.final _ _ _ _ _) hs.1
    (by simpa only [List.take_length] using hc.1 _ le_rfl) hs.2

def numericBound (N q : Nat) : Nat := 32768 * (N + q + 2) ^ 3

theorem twice_numericBound (N q : Nat) : 2 * numericBound N q = 65536 * (N + q + 2) ^ 3 := by
  unfold numericBound
  ring

theorem work_le_cube (N q size : Nat) (hsize : size ≤ N + q + 1) : work N q size ≤ (N + q + 2) ^ 3 := by
  have hN : N + 1 ≤ N + q + 2 := by omega
  have hq : q + 1 ≤ N + q + 2 := by omega
  have ht : size ≤ N + q + 2 := by omega
  have hh := Nat.mul_le_mul (Nat.mul_le_mul hN hq) ht
  calc
    work N q size ≤ (N + q + 2) * (N + q + 2) * (N + q + 2) := hh
    _ = (N + q + 2) ^ 3 := by ring

theorem prepared_footprint (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    (queryROM q full 0 used).size + heapWords q size + (haltingWords (program full.length q size)).length ≤
      16000 * (full.length + q + 2) ^ 3 := by
  intro size
  have hc : totalBuildCost (queryROM q full 0 used) (program full.length q size) (heapWords q size) ≤
      16000 * work full.length q size := PA17Rolling018B.prepared_program_totalCost q full hq hlaminar used
  have hw := work_le_cube full.length q size (prepared_indexed_size_le q full)
  unfold totalBuildCost at hc
  nlinarith

theorem prepared_layout (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    Layout (numericBound full.length q) q (prepareNormalization q full).indexed.nodes.size (queryROM q full 0 used) := by
  let size := (prepareNormalization q full).indexed.nodes.size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have hf := prepared_footprint q full hq hlaminar used
  have hd := PA17Rolling018.dimension_le_work full.length q size hsize
  have hw := work_le_cube full.length q size (prepared_indexed_size_le q full)
  have hi : (queryROM q full 0 used).input.length ≤ (queryROM q full 0 used).size := by
    unfold PhysicalROM.size
    omega
  unfold numericBound
  constructor <;> dsimp only [size] at hf hd hw ⊢ <;> omega

theorem prepared_executionClaims (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    ExecutionClaims 32 full.length q (heapWords q size) (queryROM q full 0 used)
      (program full.length q size) (initial (fun _ => 0)) := by
  intro size
  have hn := prepared_program_numeric q full hq hlaminar used (numericBound full.length q) (prepared_layout q full hq hlaminar used)
  apply PA17WordBounds023.executionClaims_of_numeric_prefix full.length q (heapWords q size) (queryROM q full 0 used)
    (program full.length q size) (initial (fun _ => 0)) rfl
    (PA17WordBounds023.queryROM_wordsFit q full ⟨0, by omega⟩ used)
    (le_trans (prepared_footprint q full hq hlaminar used) (by omega))
  · intro address _
    exact pow_pos (by decide) _
  · intro count hc register
    simpa only [twice_numericBound] using hn.1 count hc register
  · exact hn.2

end PaperProofs.Structure.LaminarTree.PA17GivenWord031g
