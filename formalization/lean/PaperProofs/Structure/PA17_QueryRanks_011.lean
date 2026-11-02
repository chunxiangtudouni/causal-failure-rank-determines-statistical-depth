module

public import PaperProofs.Structure.AlgorithmClaims
public import PaperProofs.Structure.UniformFreeTableSafety
public import PaperProofs.Structure.PA17_StageMap_001

/-! Actual flag-array scans, encoding the original first-false rank.
The scan runs from high budget to low budget, replacing its current result
at every false flag; hence the final answer is the first false budget. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryRanks011

open IndexedRAM IndexedClosureRAM AlgorithmClaims

def flagBlock (flagsBase budget : Nat) : List Op :=
  [.base (.constant .index (flagsBase + budget)), .base (.loadHeap .flag .index),
   .base (.constant .old budget), .base (.select .value .flag .value .old)]

def scan (flagsBase : Nat) (budgets : List Nat) : List Op :=
  budgets.reverse.flatMap (flagBlock flagsBase)

theorem flagBlock_heap (rom : ROM) (flagsBase budget : Nat) (state : State) :
    (execute rom (flagBlock flagsBase budget) state).heap = state.heap := rfl

theorem flagBlock_value (rom : ROM) (flagsBase budget : Nat) (state : State) :
    (execute rom (flagBlock flagsBase budget) state).register .value =
      if state.heap (flagsBase + budget) = 0 then budget else state.register .value := rfl

theorem scan_heap (rom : ROM) (flagsBase : Nat) (budgets : List Nat) (state : State) :
    (execute rom (scan flagsBase budgets) state).heap = state.heap := by
  induction budgets generalizing state with
  | nil => rfl
  | cons budget later ih =>
    rw [scan, List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, IndexedClosureRAM.execute_append, flagBlock_heap]
    exact ih state

theorem scan_value (rom : ROM) (flagsBase : Nat) (budgets : List Nat) (test : Nat → Bool)
    (state : State) (hflags : ∀ budget ∈ budgets, state.heap (flagsBase + budget) = bit (test budget)) :
    (execute rom (scan flagsBase budgets) state).register .value =
      (budgets.find? (fun budget => !(test budget))).getD (state.register .value) := by
  induction budgets generalizing state with
  | nil => rfl
  | cons budget later ih =>
    rw [scan, List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil, IndexedClosureRAM.execute_append, flagBlock_value]
    change (if (execute rom (scan flagsBase later) state).heap (flagsBase + budget) = 0
      then budget else (execute rom (scan flagsBase later) state).register .value) = _
    rw [scan_heap, hflags budget List.mem_cons_self,
      ih state (fun other ho => hflags other (List.mem_cons_of_mem _ ho))]
    cases ht : test budget <;> simp [bit, ht]

theorem scan_prefix_heap (rom : ROM) (flagsBase : Nat) (budgets : List Nat)
    (count : Nat) (state : State) :
    (execute rom ((scan flagsBase budgets).take count) state).heap = state.heap := by
  apply PA17StageMap001.execute_noStore_heap
  intro op ho
  have hm := List.mem_of_mem_take ho
  obtain ⟨budget, _, hb⟩ := List.mem_flatMap.mp hm
  simp only [flagBlock, List.mem_cons, List.mem_nil_iff, or_false] at hb
  rcases hb with rfl | rfl | rfl | rfl <;> trivial

def firstFalseValue (q : Nat) (test : Nat → Bool) : Nat :=
  (IndexedQuery.firstFalse q test).getD (q + 2)

theorem firstFalse_bound (q : Nat) (test : Nat → Bool) (budget : Nat)
    (hfirst : IndexedQuery.firstFalse q test = some budget) : budget < q + 2 := by
  have hm : budget ∈ List.range' 0 (q + 2) := List.mem_of_find?_eq_some hfirst
  obtain ⟨index, hi, heq⟩ := List.mem_range'.mp hm
  omega

theorem firstFalseValue_eq_encodeRank (q : Nat) (test : Nat → Bool) :
    firstFalseValue q test = encodeRank q (IndexedQuery.rankFromTests q test) := by
  cases hf : IndexedQuery.firstFalse q test with
  | none => simp [firstFalseValue, IndexedQuery.rankFromTests, hf, encodeRank]
  | some budget => simp [firstFalseValue, IndexedQuery.rankFromTests, hf, encodeRank]

theorem firstFalseValue_le (q : Nat) (test : Nat → Bool) : firstFalseValue q test ≤ q + 2 := by
  cases hf : IndexedQuery.firstFalse q test with
  | none => simp [firstFalseValue, hf]
  | some budget =>
    simp only [firstFalseValue, hf, Option.getD_some]
    exact (firstFalse_bound q test budget hf).le

def rankProgram (q flagsBase output : Nat) : List Op :=
  [.base (.constant .value (q + 2))] ++ scan flagsBase (List.range' 0 (q + 2)) ++
    [.base (.constant .index output), .base (.storeHeap .index .value)]

theorem rankProgram_heap (q flagsBase output : Nat) (rom : ROM) (test : Nat → Bool)
    (state : State) (hflags : ∀ budget < q + 2, state.heap (flagsBase + budget) = bit (test budget)) :
    (execute rom (rankProgram q flagsBase output) state).heap =
      Function.update state.heap output (encodeRank q (IndexedQuery.rankFromTests q test)) := by
  rw [rankProgram, IndexedClosureRAM.execute_append, IndexedClosureRAM.execute_append]
  have htail (before : State) :
      (execute rom [.base (.constant .index output), .base (.storeHeap .index .value)] before).heap =
        Function.update before.heap output (before.register .value) := rfl
  rw [htail, scan_heap, scan_value rom flagsBase (List.range' 0 (q + 2)) test]
  · change Function.update state.heap output (firstFalseValue q test) = _
    rw [firstFalseValue_eq_encodeRank]
  · intro budget hb
    obtain ⟨index, hi, heq⟩ := List.mem_range'.mp hb
    apply hflags budget
    omega

theorem rankProgram_frame (q flagsBase output : Nat) (rom : ROM) (test : Nat → Bool)
    (state : State) (hflags : ∀ budget < q + 2, state.heap (flagsBase + budget) = bit (test budget))
    (address : Nat) (hne : address ≠ output) :
    (execute rom (rankProgram q flagsBase output) state).heap address = state.heap address := by
  rw [rankProgram_heap q flagsBase output rom test state hflags, Function.update_of_ne hne]

theorem scan_length (flagsBase : Nat) (budgets : List Nat) :
    (scan flagsBase budgets).length = 4 * budgets.length := by
  have hl (budget : Nat) : (flagBlock flagsBase budget).length = 4 := rfl
  simp only [scan, List.length_flatMap, hl, List.map_const', List.sum_replicate,
    List.length_reverse, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem scan_trace_length (flagsBase : Nat) (budgets : List Nat) :
    (trace (scan flagsBase budgets)).length = 39 * budgets.length := by
  have hl (budget : Nat) : (trace (flagBlock flagsBase budget)).length = 39 := rfl
  rw [scan, UniformNormalizationRAM.trace_flatMap_length]
  simp only [hl, List.map_const', List.sum_replicate, List.length_reverse, Nat.nsmul_eq_mul, Nat.mul_comm]

theorem rankProgram_length (q flagsBase output : Nat) :
    (rankProgram q flagsBase output).length = 4 * q + 11 := by
  rw [rankProgram, List.length_append, List.length_append, scan_length, List.length_range']
  simp only [List.length_cons, List.length_nil]
  omega

theorem rankProgram_trace_length (q flagsBase output : Nat) :
    (trace (rankProgram q flagsBase output)).length = 39 * q + 105 := by
  have hi : (trace [.base (.constant .value (q + 2))]).length = 8 := rfl
  have ht : (trace [.base (.constant .index output), .base (.storeHeap .index .value)]).length = 19 := rfl
  rw [rankProgram, IndexedClosureRAM.trace_append, IndexedClosureRAM.trace_append,
    List.length_append, List.length_append, hi, ht, scan_trace_length, List.length_range']
  omega

theorem rankProgram_totalQueryCost_le (q size flagsBase output : Nat) (hsize : 0 < size) :
    totalQueryCost q (rankProgram q flagsBase output) ≤ 180 * queryWork q size := by
  rw [totalQueryCost, haltingWords_length, rankProgram_length,
    List.length_append, rankProgram_trace_length, haltTrace_length]
  dsimp [queryWork]
  nlinarith

theorem rankProgram_prefixFrame (q flagsBase output address : Nat) (rom : ROM) (hne : address ≠ output) :
    UniformFreeTableSafety.PrefixFrame rom (rankProgram q flagsBase output) address := by
  rw [rankProgram]
  apply UniformFreeTableSafety.PrefixFrame.append rom _ _ address
  · apply UniformFreeTableSafety.PrefixFrame.append rom _ _ address
    · intro state count hc
      change count ≤ 1 at hc
      interval_cases count <;> rfl
    · intro state count _
      exact congrFun (scan_prefix_heap rom flagsBase _ count state) address
  · intro state count hc
    change count ≤ 2 at hc
    interval_cases count <;> first
      | rfl
      | exact Function.update_of_ne hne _ _

theorem rankProgram_capacityThroughout (q capWords flagsBase output : Nat) (rom : PhysicalROM)
    (houtput : capWords ≤ output) (state : State) (hcapacity : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords rom (rankProgram q flagsBase output) state := by
  intro count hc address ha
  rw [rankProgram_prefixFrame q flagsBase output address rom.semantic (by omega) state count hc]
  exact hcapacity address ha

def optionBudgetWord : Option Nat → Nat
  | none => 0
  | some budget => budget + 1

theorem selectedBudget_word (q : Nat) (test : Nat → Bool) :
    optionBudgetWord (IndexedQuery.selectedBudget q test) = firstFalseValue q test := by
  cases hf : IndexedQuery.firstFalse q test with
  | none => simp only [IndexedQuery.selectedBudget, hf, firstFalseValue, Option.getD_none, optionBudgetWord]
  | some budget =>
    cases budget with
    | zero => simp only [IndexedQuery.selectedBudget, hf, firstFalseValue, Option.getD_some, optionBudgetWord]
    | succ budget => simp only [IndexedQuery.selectedBudget, hf, firstFalseValue, Option.getD_some, optionBudgetWord]

theorem encode_currentRank (q : Nat) (good bad : Nat → Bool) :
    encodeRank q (min (IndexedQuery.rankFromTests q good) (1 + IndexedQuery.rankFromTests q bad)) =
      min (firstFalseValue q good) (firstFalseValue q bad + 1) := by
  cases hg : IndexedQuery.firstFalse q good with
  | none =>
    cases hb : IndexedQuery.firstFalse q bad with
    | none => simp [IndexedQuery.rankFromTests, hg, hb, firstFalseValue, encodeRank]
    | some b =>
      have hbound : b + 1 ≤ q + 2 := by have := firstFalse_bound q bad b hb; omega
      have hadd : (1 : ℕ∞) + (b : ℕ∞) = ((b + 1 : Nat) : ℕ∞) := by rw [add_comm]; rfl
      simp [IndexedQuery.rankFromTests, hg, hb, firstFalseValue, encodeRank, hadd,
        Nat.min_eq_right hbound]
  | some g =>
    have hgBound : g ≤ q + 2 + 1 := by have := firstFalse_bound q good g hg; omega
    cases hb : IndexedQuery.firstFalse q bad with
    | none =>
      simp [IndexedQuery.rankFromTests, hg, hb, firstFalseValue, encodeRank, Nat.min_eq_left hgBound]
    | some b =>
      have hadd : (1 : ℕ∞) + (b : ℕ∞) = ((b + 1 : Nat) : ℕ∞) := by rw [add_comm]; rfl
      have hmin : min (g : ℕ∞) ((b + 1 : Nat) : ℕ∞) = ((min g (b + 1) : Nat) : ℕ∞) := by
        by_cases h : g ≤ b + 1
        · rw [min_eq_left (ENat.natCast_le_natCast.mpr h), Nat.min_eq_left h]
        · have h' : b + 1 ≤ g := by omega
          rw [min_eq_right (ENat.natCast_le_natCast.mpr h'), Nat.min_eq_right h']
      simp only [IndexedQuery.rankFromTests, firstFalseValue, hg, hb, Option.getD_some]
      rw [hadd, hmin]
      simp [encodeRank]

def finish (q header : Nat) : List Op :=
  [.base (.constant .address (header + 2)), .base (.loadHeap .index .address),
   .base (.constant .address (header + 4)), .base (.loadHeap .old .address),
   .base (.constant .address (header + 5)), .base (.loadHeap .fresh .address),
   .base (.constant .total 1), .base (.add .value .fresh .total), .base (.minimum .value .old .value),
   .subtract .total .fresh .total,
   .base (.constant .address (header + 6)), .base (.storeHeap .address .total),
   .base (.constant .total 0), .base (.constant .flag 1), .base (.select .flag .fresh .flag .total),
   .base (.select .flag .index .flag .total),
   .base (.constant .address (header + 7)), .base (.storeHeap .address .flag),
   .base (.constant .flag (q + 2)), .base (.select .old .index .old .flag),
   .base (.select .fresh .index .fresh .total), .base (.select .value .index .value .flag),
   .base (.constant .index 0)]

theorem finish_registers (q header : Nat) (rom : ROM) (state : State) :
    let result := execute rom (finish q header) state
    result.register .old = (if state.heap (header + 2) = 0 then q + 2 else state.heap (header + 4)) ∧
    result.register .fresh = (if state.heap (header + 2) = 0 then 0 else state.heap (header + 5)) ∧
    result.register .value = (if state.heap (header + 2) = 0 then q + 2 else
      min (state.heap (header + 4)) (state.heap (header + 5) + 1)) ∧ result.register .index = 0 := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem finish_heap (q header : Nat) (rom : ROM) (state : State) :
    (execute rom (finish q header) state).heap =
      Function.update
        (Function.update state.heap (header + 6) (state.heap (header + 5) - 1))
        (header + 7)
        (if state.heap (header + 2) = 0 then 0 else if state.heap (header + 5) = 0 then 0 else 1) := rfl

def program (q goodFlags badFlags header : Nat) : List Op :=
  rankProgram q goodFlags (header + 4) ++ rankProgram q badFlags (header + 5) ++ finish q header

theorem prepared_program_registers (q goodFlags badFlags header : Nat) (rom : ROM)
    (hbad : header + 4 < badFlags) (good bad : Nat → Bool) (state : State)
    (hgoodFlags : ∀ budget < q + 2, state.heap (goodFlags + budget) = bit (good budget))
    (hbadFlags : ∀ budget < q + 2, state.heap (badFlags + budget) = bit (bad budget)) :
    let result := execute rom (program q goodFlags badFlags header) state
    result.register .old = (if state.heap (header + 2) = 0 then q + 2 else
      encodeRank q (IndexedQuery.rankFromTests q good)) ∧
    result.register .fresh = (if state.heap (header + 2) = 0 then 0 else
      encodeRank q (IndexedQuery.rankFromTests q bad)) ∧
    result.register .value = (if state.heap (header + 2) = 0 then q + 2 else
      encodeRank q (min (IndexedQuery.rankFromTests q good) (1 + IndexedQuery.rankFromTests q bad))) ∧
      result.register .index = 0 := by
  let first := execute rom (rankProgram q goodFlags (header + 4)) state
  have hgheap := rankProgram_heap q goodFlags (header + 4) rom good state hgoodFlags
  have hbflags (budget : Nat) (hb : budget < q + 2) : first.heap (badFlags + budget) = bit (bad budget) := by
    rw [hgheap, Function.update_of_ne (by omega)]
    exact hbadFlags budget hb
  let second := execute rom (rankProgram q badFlags (header + 5)) first
  have hbheap := rankProgram_heap q badFlags (header + 5) rom bad first hbflags
  have ha : second.heap (header + 2) = state.heap (header + 2) := by
    rw [hbheap, hgheap, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hg : second.heap (header + 4) = encodeRank q (IndexedQuery.rankFromTests q good) := by
    rw [hbheap, hgheap, Function.update_of_ne (by omega), Function.update_self]
  have hb : second.heap (header + 5) = encodeRank q (IndexedQuery.rankFromTests q bad) := by
    rw [hbheap, Function.update_self]
  have hf := finish_registers q header rom second
  rw [ha, hg, hb, ← firstFalseValue_eq_encodeRank, ← firstFalseValue_eq_encodeRank, ← encode_currentRank] at hf
  rw [firstFalseValue_eq_encodeRank, firstFalseValue_eq_encodeRank] at hf
  simpa only [program, IndexedClosureRAM.execute_append, first, second] using hf

theorem finish_length (q header : Nat) : (finish q header).length = 23 := rfl

set_option maxRecDepth 10000 in
theorem finish_trace_length (q header : Nat) : (trace (finish q header)).length = 228 := rfl

theorem program_length (q goodFlags badFlags header : Nat) :
    (program q goodFlags badFlags header).length = 8 * q + 45 := by
  rw [program, List.length_append, List.length_append, rankProgram_length, rankProgram_length, finish_length]
  omega

theorem program_trace_length (q goodFlags badFlags header : Nat) :
    (trace (program q goodFlags badFlags header)).length = 78 * q + 438 := by
  rw [program, IndexedClosureRAM.trace_append, IndexedClosureRAM.trace_append,
    List.length_append, List.length_append, rankProgram_trace_length, rankProgram_trace_length, finish_trace_length]
  omega

theorem program_heap (q goodFlags badFlags header : Nat) (rom : ROM)
    (hbad : header + 4 < badFlags) (good bad : Nat → Bool) (state : State)
    (hgoodFlags : ∀ budget < q + 2, state.heap (goodFlags + budget) = bit (good budget))
    (hbadFlags : ∀ budget < q + 2, state.heap (badFlags + budget) = bit (bad budget)) :
    (execute rom (program q goodFlags badFlags header) state).heap =
      Function.update
        (Function.update
          (Function.update
            (Function.update state.heap (header + 4) (firstFalseValue q good))
            (header + 5) (firstFalseValue q bad))
          (header + 6) (firstFalseValue q bad - 1))
        (header + 7)
        (if state.heap (header + 2) = 0 then 0 else if firstFalseValue q bad = 0 then 0 else 1) := by
  let first := execute rom (rankProgram q goodFlags (header + 4)) state
  have hgheap := rankProgram_heap q goodFlags (header + 4) rom good state hgoodFlags
  have hbflags (budget : Nat) (hb : budget < q + 2) : first.heap (badFlags + budget) = bit (bad budget) := by
    rw [hgheap, Function.update_of_ne (by omega)]
    exact hbadFlags budget hb
  let second := execute rom (rankProgram q badFlags (header + 5)) first
  have hbheap := rankProgram_heap q badFlags (header + 5) rom bad first hbflags
  have ha : second.heap (header + 2) = state.heap (header + 2) := by
    rw [hbheap, hgheap, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
  have hb : second.heap (header + 5) = encodeRank q (IndexedQuery.rankFromTests q bad) := by
    rw [hbheap, Function.update_self]
  have hf := finish_heap q header rom second
  rw [ha, hb, hbheap, hgheap, ← firstFalseValue_eq_encodeRank, ← firstFalseValue_eq_encodeRank] at hf
  simpa only [program, IndexedClosureRAM.execute_append, first, second] using hf

theorem prepared_selection_control (q goodFlags badFlags header : Nat) (rom : ROM)
    (hbad : header + 4 < badFlags) (good bad : Nat → Bool) (state : State)
    (hgoodFlags : ∀ budget < q + 2, state.heap (goodFlags + budget) = bit (good budget))
    (hbadFlags : ∀ budget < q + 2, state.heap (badFlags + budget) = bit (bad budget)) :
    let result := execute rom (program q goodFlags badFlags header) state
    result.heap (header + 6) = firstFalseValue q bad - 1 ∧
      result.heap (header + 7) =
        (if state.heap (header + 2) = 0 then 0 else if firstFalseValue q bad = 0 then 0 else 1) ∧
      result.heap (header + 6) ≤ q + 1 := by
  have hh := program_heap q goodFlags badFlags header rom hbad good bad state hgoodFlags hbadFlags
  have hb : firstFalseValue q bad - 1 ≤ q + 1 := by have := firstFalseValue_le q bad; omega
  dsimp only
  rw [hh]
  simp only [Function.update_self, Function.update_of_ne (show header + 6 ≠ header + 7 from by omega)]
  exact ⟨True.intro, True.intro, hb⟩

set_option maxRecDepth 10000 in
theorem finish_prefix_heap (q header : Nat) (rom : ROM) (state : State)
    (count : Nat) (hc : count ≤ (finish q header).length) :
    (execute rom ((finish q header).take count) state).heap =
      if count ≤ 11 then state.heap else
      if count ≤ 17 then Function.update state.heap (header + 6) (state.heap (header + 5) - 1)
      else (execute rom (finish q header) state).heap := by
  change count ≤ 23 at hc
  interval_cases count <;> rfl

theorem finish_prefixFrame (q header address : Nat) (rom : ROM)
    (hne6 : address ≠ header + 6) (hne7 : address ≠ header + 7) :
    UniformFreeTableSafety.PrefixFrame rom (finish q header) address := by
  intro state count hc
  rw [finish_prefix_heap q header rom state count hc]
  split_ifs
  · rfl
  · exact Function.update_of_ne hne6 _ _
  · rw [finish_heap, Function.update_of_ne hne7, Function.update_of_ne hne6]

theorem program_prefixFrame (q goodFlags badFlags header address : Nat) (rom : ROM)
    (hne : ∀ offset ∈ [4, 5, 6, 7], address ≠ header + offset) :
    UniformFreeTableSafety.PrefixFrame rom (program q goodFlags badFlags header) address := by
  rw [program]
  apply UniformFreeTableSafety.PrefixFrame.append rom _ _ address
  · exact UniformFreeTableSafety.PrefixFrame.append rom _ _ address
      (rankProgram_prefixFrame q goodFlags (header + 4) address rom (hne 4 (by simp)))
      (rankProgram_prefixFrame q badFlags (header + 5) address rom (hne 5 (by simp)))
  · exact finish_prefixFrame q header address rom (hne 6 (by simp)) (hne 7 (by simp))

theorem program_capacityThroughout (q capWords goodFlags badFlags header : Nat) (rom : PhysicalROM)
    (hheader : capWords ≤ header) (state : State) (hcapacity : CapacityPrefixBounded q capWords state.heap) :
    CapacityThroughout q capWords rom (program q goodFlags badFlags header) state := by
  intro count hc address ha
  rw [program_prefixFrame q goodFlags badFlags header address rom.semantic
    (by intro offset _; omega) state count hc]
  exact hcapacity address ha

theorem program_totalQueryCost_le (q size goodFlags badFlags header : Nat) (hsize : 0 < size) :
    totalQueryCost q (program q goodFlags badFlags header) ≤ 700 * queryWork q size := by
  rw [totalQueryCost, haltingWords_length, program_length,
    List.length_append, program_trace_length, haltTrace_length]
  dsimp [queryWork]
  nlinarith

def replyProgram (q header toolAddress : Nat) : List Op :=
  [.base (.constant .address toolAddress), .base (.loadHeap .index .address),
   .base (.constant .address (header + 2)), .base (.loadHeap .flag .address),
   .base (.constant .address (header + 4)), .base (.loadHeap .old .address),
   .base (.constant .address (header + 5)), .base (.loadHeap .fresh .address),
   .base (.constant .total 1), .base (.add .value .fresh .total), .base (.minimum .value .old .value),
   .base (.constant .total (q + 2)), .base (.select .old .flag .old .total),
   .base (.select .value .flag .value .total), .base (.constant .total 0),
   .base (.select .fresh .flag .fresh .total), .base (.select .index .flag .index .total)]

theorem replyProgram_heap (q header toolAddress : Nat) (rom : ROM) (state : State) :
    (execute rom (replyProgram q header toolAddress) state).heap = state.heap := rfl

theorem replyProgram_registers (q header toolAddress : Nat) (rom : ROM) (state : State) :
    let result := execute rom (replyProgram q header toolAddress) state
    result.register .old = (if state.heap (header + 2) = 0 then q + 2 else state.heap (header + 4)) ∧
    result.register .fresh = (if state.heap (header + 2) = 0 then 0 else state.heap (header + 5)) ∧
    result.register .value = (if state.heap (header + 2) = 0 then q + 2 else
      min (state.heap (header + 4)) (state.heap (header + 5) + 1)) ∧
    result.register .index = (if state.heap (header + 2) = 0 then 0 else state.heap toolAddress) := by
  exact ⟨rfl, rfl, rfl, rfl⟩

theorem replyProgram_correct {q : Nat} (rom : ROM) (header toolAddress : Nat) (state : State)
    (good bad : Nat → Bool) (tool : Option (Fin q))
    (hgood : state.heap (header + 4) = firstFalseValue q good)
    (hbad : state.heap (header + 5) = firstFalseValue q bad)
    (htool : state.heap toolAddress = match tool with | none => 0 | some tool => tool.val + 1) :
    ReplyCorrect q
      (if state.heap (header + 2) = 0 then IndexedQuery.terminalReply q else
        ⟨min (IndexedQuery.rankFromTests q good) (1 + IndexedQuery.rankFromTests q bad),
         IndexedQuery.rankFromTests q good, IndexedQuery.rankFromTests q bad, tool⟩)
      (execute rom (replyProgram q header toolAddress) state) := by
  obtain ⟨hg, hb, hr, ht⟩ := replyProgram_registers q header toolAddress rom state
  by_cases hactive : state.heap (header + 2) = 0
  · simp only [hactive, ite_true] at hg hb hr ht ⊢
    exact ⟨hr, hg, hb, ht⟩
  · simp only [hactive, ite_false] at hg hb hr ht ⊢
    refine ⟨?_, ?_, ?_, ht.trans htool⟩
    · rw [hr, hgood, hbad, encode_currentRank]
    · exact hg.trans (hgood.trans (firstFalseValue_eq_encodeRank q good))
    · exact hb.trans (hbad.trans (firstFalseValue_eq_encodeRank q bad))

theorem replyProgram_prefix_heap (q header toolAddress : Nat) (rom : ROM) (state : State) (count : Nat) :
    (execute rom ((replyProgram q header toolAddress).take count) state).heap = state.heap := by
  apply PA17StageMap001.execute_noStore_heap
  intro op ho
  have hm := List.mem_of_mem_take ho
  simp only [replyProgram, List.mem_cons, List.mem_nil_iff, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> trivial

theorem replyProgram_length (q header toolAddress : Nat) : (replyProgram q header toolAddress).length = 17 := rfl

set_option maxRecDepth 10000 in
theorem replyProgram_trace_length (q header toolAddress : Nat) : (trace (replyProgram q header toolAddress)).length = 170 := rfl

end PaperProofs.Structure.LaminarTree.PA17QueryRanks011
