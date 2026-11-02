module

public import PaperProofs.Structure.PA17_Rolling_018
public import PaperProofs.Structure.PA17_QueryTests_009
public import PaperProofs.Structure.PA17_QueryRanks_011
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-! Actual raw-used count and first-false rank finish for the two-row
construction. No answer, trace or precomputed counts are program inputs. -/

@[expose] public section
set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

namespace PaperProofs.Structure.LaminarTree.PA17Rolling018B

open IndexedRAM IndexedClosureRAM AlgorithmClaims PA17TagBridge001

def parentBase (q size : Nat) : Nat := PA17Rolling018.metadataBase q size + size
def rowPointer (q size : Nat) : Nat := PA17Rolling018.stageWord q size
def countsBase (q size : Nat) : Nat := rowPointer q size + 1
def goodFlags (q size : Nat) : Nat := countsBase q size + size
def badFlags (q size : Nat) : Nat := goodFlags q size + q + 2
def rankWord (q size : Nat) : Nat := badFlags q size + q + 2
def indexWords (q size : Nat) : Nat := 4 * size + 2 * q + 7

def countProgram (N q size : Nat) : List Op :=
  UniformNormalizationRAM.clearBlock (rowPointer q size) ++
    PA17QueryCounts008.program N q size (countsBase q size)

def testProgram (q size : Nat) : List Op :=
  PA17QueryTests009.program size q (rowPointer q size) (countsBase q size)
    (parentBase q size) (parentBase q size) (goodFlags q size) (badFlags q size)

def finishProgram (N q size : Nat) : List Op :=
  countProgram N q size ++ testProgram q size ++
    PA17QueryRanks011.rankProgram q (goodFlags q size) (rankWord q size)

def program (N q size : Nat) : List Op :=
  PA17Rolling018.buildProgram N q size ++ finishProgram N q size

theorem rankProgram_value (q flagsBase output : Nat) (rom : ROM) (test : Nat → Bool)
    (state : State) (hflags : ∀ budget < q + 2, state.heap (flagsBase + budget) = bit (test budget)) :
    (execute rom (PA17QueryRanks011.rankProgram q flagsBase output) state).register .value =
      encodeRank q (IndexedQuery.rankFromTests q test) := by
  rw [PA17QueryRanks011.rankProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  change (execute rom (PA17QueryRanks011.scan flagsBase (List.range' 0 (q + 2)))
    (execute rom [.base (.constant .value (q + 2))] state)).register .value = _
  rw [PA17QueryRanks011.scan_value rom flagsBase (List.range' 0 (q + 2)) test]
  · exact PA17QueryRanks011.firstFalseValue_eq_encodeRank q test
  · intro budget hb
    obtain ⟨index, hi, heq⟩ := List.mem_range'.mp hb
    exact hflags budget (by omega)

theorem countProgram_prefixFrame (rom : ROM) (N q size address : Nat)
    (ha : address < rowPointer q size) :
    UniformFreeTableSafety.PrefixFrame rom (countProgram N q size) address := by
  apply UniformFreeTableSafety.PrefixFrame.append
  · exact UniformFreeTableSafety.clearBlock_prefixFrame rom _ address (by omega)
  · intro state count _
    exact PA17QueryCounts008.program_take_frame rom N q size (countsBase q size) count state address
      (Or.inl (by unfold countsBase; omega))

theorem countProgram_pointer (rom : ROM) (N q size : Nat) (state : State) :
    (execute rom (countProgram N q size) state).heap (rowPointer q size) = 0 := by
  rw [countProgram, IndexedClosureRAM.execute_append]
  have hf := PA17QueryCounts008.program_take_frame rom N q size (countsBase q size)
    (PA17QueryCounts008.program N q size (countsBase q size)).length
    (execute rom (UniformNormalizationRAM.clearBlock (rowPointer q size)) state)
    (rowPointer q size) (Or.inl (by unfold countsBase; omega))
  rw [List.take_length] at hf
  rw [hf, UniformNormalizationRAM.execute_clearBlock_heap, Function.update_self]

theorem countProgram_counts (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (state : State) :
    PA17QueryCounts008.CountsCorrect q full used (countsBase q (prepareNormalization q full).indexed.nodes.size)
      (execute (queryROM q full 0 used).semantic
        (countProgram full.length q (prepareNormalization q full).indexed.nodes.size) state).heap := by
  rw [countProgram, IndexedClosureRAM.execute_append]
  exact PA17QueryCounts008.prepared_program_correct q full 0 used _ _

theorem readBounds (q size : Nat) :
    PA17QueryTests009.ReadBounds size q (rowPointer q size) (countsBase q size)
      (parentBase q size) (parentBase q size) 0 (goodFlags q size) := by
  constructor
  · unfold goodFlags countsBase; omega
  · unfold parentBase goodFlags countsBase rowPointer PA17Rolling018.stageWord; omega
  · unfold goodFlags; omega
  · unfold parentBase goodFlags countsBase rowPointer PA17Rolling018.stageWord; omega
  · have hm : (q + 2) * (size + 1) ≤ PA17Rolling018.workBase q size := by
      unfold PA17Rolling018.workBase
      rw [Nat.mul_assoc]
      omega
    unfold goodFlags countsBase rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase
      PA17Rolling018.capacityWords
    omega

theorem flags_disjoint (q size : Nat) (left right : Fin (q + 2)) :
    goodFlags q size + left.val ≠ badFlags q size + right.val := by
  have hl := left.isLt
  unfold badFlags
  omega

theorem countProgram_inputs (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (state : State) (hinv : PA17Rolling018.Invariant q full state)
    (hrow : ∀ budget : Fin (q + 2),
      readEntry (prepareNormalization q full).indexed.nodes.size budget.val state.heap =
        (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget) :
    let cache := (prepareNormalization q full).indexed
    let result := execute (queryROM q full 0 used).semantic (countProgram full.length q cache.nodes.size) state
    PA17QueryTests009.Inputs cache (rowPointer q cache.nodes.size) (countsBase q cache.nodes.size)
      (parentBase q cache.nodes.size) (parentBase q cache.nodes.size) 0
      (IndexedDescent.usedCounts cache used) (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩) none result.heap := by
  intro cache result
  have hf (address : Nat) (ha : address < rowPointer q cache.nodes.size) : result.heap address = state.heap address := by
    have hh := countProgram_prefixFrame (queryROM q full 0 used).semantic full.length q cache.nodes.size address ha
      state (countProgram full.length q cache.nodes.size).length le_rfl
    simpa only [List.take_length] using hh
  have hm := PA17Rolling018.metadata_transfer q full (PA17Rolling018.metadataBase q cache.nodes.size)
    state.heap result.heap hinv.1 (by
      intro address _ ha
      apply hf address
      simpa only [rowPointer, PA17Rolling018.stageWord] using ha)
  have hp := PA17HeapAncestors001.metadata_parentHeapFor q full _ _ hm
  change PA17HeapAncestors001.ParentHeapFor cache (parentBase q cache.nodes.size) result.heap at hp
  refine ⟨countProgram_pointer _ _ _ _ state, hp.1, countProgram_counts q full used state, hp, ?_⟩
  intro budget
  have hr := PA17TagBridge001.rep_of_readEntry cache budget.val state.heap _
    (hinv.2.1 budget.val (by have := budget.isLt; omega)) (hrow budget)
  rw [Nat.zero_add]
  apply PA17Rolling018.tagFirst_transfer cache state.heap result.heap _ _ hr
  intro offset ho
  apply hf
  have hh := PA17Rolling018.slot_word_lt_work q cache.nodes.size budget.val
    (by have := budget.isLt; omega) offset ho
  dsimp only [PA17Rolling018.base] at hh
  unfold rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase PA17Rolling018.capacityWords
  omega

theorem prepared_finish_flags (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q))
    (state : State) (hinv : PA17Rolling018.Invariant q full state)
    (hrow : ∀ budget : Fin (q + 2),
      readEntry (prepareNormalization q full).indexed.nodes.size budget.val state.heap =
        (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget) :
    let cache := (prepareNormalization q full).indexed
    let afterCounts := execute (queryROM q full 0 used).semantic (countProgram full.length q cache.nodes.size) state
    let result := execute (queryROM q full 0 used).semantic (testProgram q cache.nodes.size) afterCounts
    ∀ budget : Fin (q + 2),
      result.heap (goodFlags q cache.nodes.size + budget.val) =
        bit (IndexedQuery.accepts cache (IndexedDescent.usedCounts cache used)
          ((IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget)) ∧
        result.heap (badFlags q cache.nodes.size + budget.val) = 0 := by
  intro cache afterCounts result budget
  have hc := PA17QueryTests009.program_correct cache (queryROM q full 0 used).semantic
    (rowPointer q cache.nodes.size) (countsBase q cache.nodes.size) (parentBase q cache.nodes.size)
    (parentBase q cache.nodes.size) 0 (goodFlags q cache.nodes.size) (goodFlags q cache.nodes.size)
    (badFlags q cache.nodes.size) (IndexedDescent.usedCounts cache used)
    (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩) none afterCounts
    (countProgram_inputs q full used state hinv hrow) (readBounds q cache.nodes.size)
    le_rfl (by unfold badFlags; omega) (flags_disjoint q cache.nodes.size) budget
  simpa only [result, testProgram, IndexedQuery.extensionTest_none, bit, Bool.false_eq_true, ↓reduceIte] using hc

theorem prepared_finish_rank (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) (state : State)
    (hinv : PA17Rolling018.Invariant q full state)
    (hrow : ∀ budget : Fin (q + 2),
      readEntry (prepareNormalization q full).indexed.nodes.size budget.val state.heap =
        (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let result := execute (queryROM q full 0 used).semantic (finishProgram full.length q size) state
    result.register .value = encodeRank q (errorRank full (Finset.univ \ used)) ∧
      result.heap (rankWord q size) = encodeRank q (errorRank full (Finset.univ \ used)) := by
  intro size result
  let cache := (prepareNormalization q full).indexed
  let row := IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩
  let test := fun budget => IndexedQuery.accepts cache (IndexedDescent.usedCounts cache used) (IndexedQuery.entryAt row budget)
  let before := execute (queryROM q full 0 used).semantic
    (countProgram full.length q size ++ testProgram q size) state
  have hflags (budget : Nat) (hb : budget < q + 2) :
      before.heap (goodFlags q size + budget) = bit (test budget) := by
    have hh := (prepared_finish_flags q full used state hinv hrow ⟨budget, hb⟩).1
    dsimp only [before]
    rw [IndexedClosureRAM.execute_append]
    simpa only [test, IndexedQuery.entryAt_get row budget hb] using hh
  have hvalue := rankProgram_value q (goodFlags q size) (rankWord q size)
    (queryROM q full 0 used).semantic test before hflags
  have hheap := PA17QueryRanks011.rankProgram_heap q (goodFlags q size) (rankWord q size)
    (queryROM q full 0 used).semantic test before hflags
  have hcorrect : IndexedQuery.rankFromTests q test = errorRank full (Finset.univ \ used) := by
    change IndexedQuery.goodRank cache (IndexedDescent.usedCounts cache used) row = _
    apply IndexedQuery.goodRank_eq_of_rowCorrect cache used full row
    simpa only [List.drop_zero] using IndexedQuery.storedPositiveRow_correct q full hq hlaminar ⟨0, by omega⟩
  have heq : result = execute (queryROM q full 0 used).semantic
      (PA17QueryRanks011.rankProgram q (goodFlags q size) (rankWord q size)) before := by
    dsimp only [result, finishProgram, before]
    rw [IndexedClosureRAM.execute_append]
  rw [hcorrect] at hvalue hheap
  rw [heq]
  exact ⟨hvalue, by rw [hheap, Function.update_self]⟩

theorem prepared_program_rank (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let result := execute (queryROM q full 0 used).semantic (program full.length q size) (initial (fun _ => 0))
    result.register .value = encodeRank q (errorRank full (Finset.univ \ used)) ∧
      result.heap (rankWord q size) = encodeRank q (errorRank full (Finset.univ \ used)) := by
  intro size result
  have hb := PA17Rolling018.prepared_build_rowZero q full hq hlaminar used
  have hf := prepared_finish_rank q full hq hlaminar used _ hb.1 hb.2
  dsimp only [result, program]
  rw [IndexedClosureRAM.execute_append]
  exact hf

theorem finishProgram_prefixFrame (rom : ROM) (N q size address : Nat)
    (ha : address < rowPointer q size) :
    UniformFreeTableSafety.PrefixFrame rom (finishProgram N q size) address := by
  apply UniformFreeTableSafety.PrefixFrame.append
  · apply UniformFreeTableSafety.PrefixFrame.append
    · exact countProgram_prefixFrame rom N q size address ha
    · exact PA17QueryTests009.program_prefixFrame rom size q (rowPointer q size) (countsBase q size)
        (parentBase q size) (parentBase q size) (goodFlags q size) (badFlags q size) address
        (by intro budget _; unfold goodFlags countsBase; omega)
        (by intro budget _; unfold badFlags goodFlags countsBase; omega)
  · exact PA17QueryRanks011.rankProgram_prefixFrame q (goodFlags q size) (rankWord q size)
      address rom (by unfold rankWord badFlags goodFlags countsBase; omega)

theorem finishProgram_capacityThroughout (q N size : Nat) (rom : PhysicalROM) (state : State)
    (hbound : CapacityPrefixBounded q (PA17Rolling018.capacityWords q size) state.heap) :
    CapacityThroughout q (PA17Rolling018.capacityWords q size) rom (finishProgram N q size) state := by
  intro count hc address ha
  rw [finishProgram_prefixFrame rom.semantic N q size address
    (by unfold rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase; omega) state count hc]
  exact hbound address ha

theorem prepared_program_rowZero (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let result := execute (queryROM q full 0 used).semantic (program full.length q size) (initial (fun _ => 0))
    ∀ budget : Fin (q + 2), readEntry size budget.val result.heap =
      (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget := by
  intro size result budget
  let cache := (prepareNormalization q full).indexed
  let before := execute (queryROM q full 0 used).semantic
    (PA17Rolling018.buildProgram full.length q size) (initial (fun _ => 0))
  have hb := PA17Rolling018.prepared_build_rowZero q full hq hlaminar used
  have hr := PA17TagBridge001.rep_of_readEntry cache budget.val before.heap _
    (hb.1.2.1 budget.val (by have := budget.isLt; omega)) (hb.2 budget)
  have hf : TagFirstRep cache result.heap (budget.val * (size + 1))
      ((IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget) := by
    apply PA17Rolling018.tagFirst_transfer cache before.heap result.heap _ _ hr
    intro offset ho
    have hh := PA17Rolling018.slot_word_lt_work q size budget.val
      (by have := budget.isLt; omega) offset ho
    dsimp only [PA17Rolling018.base] at hh
    have hx := finishProgram_prefixFrame (queryROM q full 0 used).semantic full.length q size
      (budget.val * (size + 1) + offset)
      (by unfold rowPointer PA17Rolling018.stageWord PA17Rolling018.metadataBase
            PA17Rolling018.capacityWords; omega)
      before (finishProgram full.length q size).length le_rfl
    rw [List.take_length] at hx
    dsimp only [result, program]
    rw [IndexedClosureRAM.execute_append]
    exact hx
  exact PA17TagBridge001.readEntry_eq_of_rep cache budget.val result.heap _ hf

theorem prepared_program_semantics (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    let result := execute (queryROM q full 0 used).semantic (program full.length q size) (initial (fun _ => 0))
    result.register .value = encodeRank q (errorRank full (Finset.univ \ used)) ∧
      ∀ budget : Fin (q + 2), readEntry size budget.val result.heap =
        (IndexedQuery.storedPositiveRow q full ⟨0, by omega⟩).get budget :=
  ⟨(prepared_program_rank q full hq hlaminar used).1, prepared_program_rowZero q full hq hlaminar used⟩

theorem countProgram_trace_length (N q size : Nat) :
    (trace (countProgram N q size)).length = 27 + (69 * q + 27) * size := by
  rw [countProgram, trace_append, List.length_append, PA17QueryCounts008.program_trace_length]
  rfl

theorem finishProgram_trace_length (N q size : Nat) :
    (trace (finishProgram N q size)).length =
      27 + (69 * q + 27) * size + (q + 2) * (284 * size + 162) + 39 * q + 105 := by
  rw [finishProgram, trace_append, trace_append, List.length_append, List.length_append,
    countProgram_trace_length, testProgram, PA17QueryTests009.program_trace_length,
    PA17QueryRanks011.rankProgram_trace_length]
  omega

theorem finishProgram_trace_le (N q size : Nat) (hsize : 0 < size) :
    (trace (finishProgram N q size)).length ≤ 1200 * queryWork q size := by
  rw [finishProgram_trace_length]
  have hq : q + 2 ≤ 2 * (q + 1) := by omega
  have hs : 284 * size + 162 ≤ 446 * size := by omega
  have ht := Nat.mul_le_mul hq hs
  unfold queryWork
  nlinarith

theorem program_trace_le (N q size : Nat) (hsize : 0 < size) :
    (trace (program N q size)).length ≤ 2450 * work N q size := by
  rw [program, trace_append, List.length_append]
  have hb := PA17Rolling018.buildProgram_trace_le N q size hsize
  have hf := finishProgram_trace_le N q size hsize
  have hm : queryWork q size ≤ work N q size := by
    have hh := Nat.le_mul_of_pos_left ((q + 1) * size) (show 0 < N + 1 by omega)
    simpa only [queryWork, work, Nat.mul_assoc] using hh
  omega

theorem indexWords_le (q size : Nat) : indexWords q size ≤ 7 * (q + size + 1) := by
  unfold indexWords
  omega

theorem lastWord_allocated (q size : Nat) :
    rankWord q size < PA17Rolling018.capacityWords q size + indexWords q size := by
  unfold rankWord badFlags goodFlags countsBase rowPointer PA17Rolling018.stageWord
    PA17Rolling018.metadataBase indexWords
  omega

theorem heapWords_le (q size : Nat) (hsize : 0 < size) :
    PA17Rolling018.capacityWords q size + indexWords q size ≤ 25 * queryWork q size := by
  have hc := PA17Rolling018.capacityWords_le q size hsize
  unfold indexWords queryWork at hc ⊢
  nlinarith

theorem prepared_program_totalCost (q : Nat) (full : List (Finset (Fin q))) (hq : 0 < q)
    (hlaminar : LaminarSchedule full) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    totalBuildCost (queryROM q full 0 used) (program full.length q size)
      (PA17Rolling018.capacityWords q size + indexWords q size) ≤ 16000 * work full.length q size := by
  intro size
  have hsize : 0 < size := by
    obtain ⟨root, _⟩ := prepared_indexed_node_exists q full Finset.univ (root_mem full)
    exact Nat.lt_of_le_of_lt (Nat.zero_le root.val) root.isLt
  have htrace := program_trace_le full.length q size hsize
  have hlen := PA17Rolling018.program_length_le_trace (program full.length q size)
  have hrom := PA17Rolling018.queryROM_size_le q full hq hlaminar used
  have hheap := heapWords_le q size hsize
  have hqwork : queryWork q size ≤ work full.length q size := by
    have hm := Nat.le_mul_of_pos_left ((q + 1) * size) (show 0 < full.length + 1 by omega)
    simpa only [queryWork, work, Nat.mul_assoc] using hm
  have hpositive := (PA17Rolling018.dimension_le_work full.length q size hsize).2.2
  rw [totalBuildCost, haltingWords_length, List.length_append, haltTrace_length]
  change (queryROM q full 0 used).size ≤ 9 * work full.length q size at hrom
  nlinarith [htrace, hlen, hrom, hheap, hqwork, hpositive]

theorem prepared_program_halting (q : Nat) (full : List (Finset (Fin q))) (used : Finset (Fin q)) :
    let size := (prepareNormalization q full).indexed.nodes.size
    HaltingRuns (queryROM q full 0 used).semantic (program full.length q size) (initial (fun _ => 0))
      (execute (queryROM q full 0 used).semantic (program full.length q size) (initial (fun _ => 0)))
      (trace (program full.length q size) ++ haltTrace) := by
  intro size
  exact execute_halts _ _ _ rfl

end PaperProofs.Structure.LaminarTree.PA17Rolling018B
