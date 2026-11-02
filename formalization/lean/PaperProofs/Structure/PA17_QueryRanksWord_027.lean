module

public import PaperProofs.Structure.PA17_QueryRanks_011
public import PaperProofs.Structure.PA17_QueryHeaderWord_022a

/-! Numeric register and actual-access certificates for the original
query's flag scans, aggregate arithmetic and final reply reload. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA17QueryRanksWord027

open IndexedRAM IndexedClosureRAM AlgorithmClaims
open PA17QueryHeaderWord022

theorem flagBlock_numeric (B heapWords flagsBase budget : Nat) (rom : PhysicalROM)
    (haddress : flagsBase + budget < heapWords) (haddrBound : flagsBase + budget ≤ B)
    (hbudget : budget ≤ B) (state : State) (hregister : RegistersLE B state)
    (hvalue : state.heap (flagsBase + budget) ≤ B) :
    NumericSafe B heapWords rom (PA17QueryRanks011.flagBlock flagsBase budget) state := by
  constructor
  · intro count hc register
    have hr := hregister register
    have hv := hregister .value
    change count ≤ 4 at hc
    interval_cases count <;> cases register <;>
      simp [PA17QueryRanks011.flagBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro count hc
    change count < 4 at hc
    interval_cases count <;>
      simp [PA17QueryRanks011.flagBlock, IndexedClosureRAM.execute, Op.execute, Instruction.execute,
        AccessFits, haddress]

theorem reverseBlocks_numeric (B heapWords flagsBase : Nat) (rom : PhysicalROM) (budgets : List Nat)
    (haddress : ∀ budget ∈ budgets, flagsBase + budget < heapWords)
    (haddrBound : ∀ budget ∈ budgets, flagsBase + budget ≤ B)
    (hbudget : ∀ budget ∈ budgets, budget ≤ B) (state : State) (hregister : RegistersLE B state)
    (hvalues : ∀ budget ∈ budgets, state.heap (flagsBase + budget) ≤ B) :
    NumericSafe B heapWords rom (PA17QueryRanks011.scan flagsBase budgets) state := by
  induction budgets generalizing state with
  | nil =>
    constructor
    · intro count _
      simpa only [PA17QueryRanks011.scan, List.reverse_nil, List.flatMap_nil, List.take_nil,
        IndexedClosureRAM.execute] using hregister
    · intro count hc
      change count < 0 at hc
      omega
  | cons head later ih =>
    have hs := ih (fun budget hb => haddress budget (List.mem_cons_of_mem _ hb))
      (fun budget hb => haddrBound budget (List.mem_cons_of_mem _ hb))
      (fun budget hb => hbudget budget (List.mem_cons_of_mem _ hb)) state hregister
      (fun budget hb => hvalues budget (List.mem_cons_of_mem _ hb))
    rw [PA17QueryRanks011.scan, List.reverse_cons, List.flatMap_append, List.flatMap_cons, List.flatMap_nil,
      List.append_nil]
    apply NumericSafe.append B heapWords rom _ _ state hs
    apply flagBlock_numeric B heapWords flagsBase head rom (haddress head List.mem_cons_self)
      (haddrBound head List.mem_cons_self) (hbudget head List.mem_cons_self) _
      (NumericSafe.final _ _ _ _ _ hs)
    rw [PA17QueryRanks011.scan_heap]
    exact hvalues head List.mem_cons_self

theorem constant_numeric (B heapWords value : Nat) (rom : PhysicalROM) (target : Register)
    (hvalue : value ≤ B) (state : State) (hregister : RegistersLE B state) :
    NumericSafe B heapWords rom [.base (.constant target value)] state := by
  constructor
  · intro count hc register
    change count ≤ 1 at hc
    interval_cases count
    · exact hregister register
    · change Function.update state.register target value register ≤ B
      by_cases heq : register = target
      · rw [heq, Function.update_self]; exact hvalue
      · rw [Function.update_of_ne heq]; exact hregister register
  · intro count hc
    change count < 1 at hc
    have heq : count = 0 := by omega
    subst count
    trivial

theorem storeValue_numeric (B heapWords output : Nat) (rom : PhysicalROM)
    (houtput : output < heapWords) (houtputBound : output ≤ B) (state : State)
    (hregister : RegistersLE B state) :
    NumericSafe B heapWords rom [.base (.constant .index output), .base (.storeHeap .index .value)] state := by
  constructor
  · intro count hc register
    have hr := hregister register
    change count ≤ 2 at hc
    interval_cases count <;> cases register <;> simp [IndexedClosureRAM.execute, Op.execute, Instruction.execute] <;> omega
  · intro count hc
    change count < 2 at hc
    interval_cases count <;> simp [IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits, houtput]

theorem rankProgram_numeric (B heapWords q flagsBase output : Nat) (rom : PhysicalROM)
    (hflags : flagsBase + (q + 2) ≤ heapWords) (hflagsBound : flagsBase + (q + 2) ≤ B)
    (houtput : output < heapWords) (houtputBound : output ≤ B) (hq : q + 2 ≤ B)
    (state : State) (hregister : RegistersLE B state)
    (hvalues : ∀ budget < q + 2, state.heap (flagsBase + budget) ≤ B) :
    NumericSafe B heapWords rom (PA17QueryRanks011.rankProgram q flagsBase output) state := by
  let init : List Op := [.base (.constant .value (q + 2))]
  have hi := constant_numeric B heapWords (q + 2) rom .value hq state hregister
  have hs := reverseBlocks_numeric B heapWords flagsBase rom (List.range' 0 (q + 2))
    (by intro budget hb; obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hb; omega)
    (by intro budget hb; obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hb; omega)
    (by intro budget hb; obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hb; omega)
    (execute rom.semantic init state) (NumericSafe.final _ _ _ _ _ hi) (by
      intro budget hb
      obtain ⟨i, hi, heq⟩ := List.mem_range'.mp hb
      exact hvalues budget (by omega))
  rw [PA17QueryRanks011.rankProgram]
  apply NumericSafe.append B heapWords rom _ _ state (NumericSafe.append B heapWords rom _ _ state hi hs)
  exact storeValue_numeric B heapWords output rom houtput houtputBound _
    (NumericSafe.final _ _ _ _ _ (NumericSafe.append B heapWords rom _ _ state hi hs))

set_option maxRecDepth 20000 in
theorem finish_numeric (B heapWords q header : Nat) (rom : PhysicalROM)
    (haccess : header + 8 ≤ heapWords) (haddress : header + 8 ≤ B) (hq : q + 3 ≤ B)
    (state : State) (hregister : RegistersLE B state)
    (hactive : state.heap (header + 2) ≤ B)
    (hgood : state.heap (header + 4) ≤ q + 2) (hbad : state.heap (header + 5) ≤ q + 2) :
    NumericSafe B heapWords rom (PA17QueryRanks011.finish q header) state := by
  have hmin : min (state.heap (header + 4)) (state.heap (header + 5) + 1) ≤ B :=
    (min_le_left _ _).trans (hgood.trans (by omega))
  constructor
  · intro count hc register
    have hr := hregister register
    change count ≤ 23 at hc
    interval_cases count <;> cases register <;>
      simp [PA17QueryRanks011.finish, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro count hc
    change count < 23 at hc
    interval_cases count <;>
      simp [PA17QueryRanks011.finish, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

set_option maxRecDepth 20000 in
theorem reply_numeric (B heapWords q header toolAddress : Nat) (rom : PhysicalROM)
    (haccess : header + 6 ≤ heapWords) (haddress : header + 6 ≤ B)
    (htoolAccess : toolAddress < heapWords) (htoolAddress : toolAddress ≤ B) (hq : q + 3 ≤ B)
    (state : State) (hregister : RegistersLE B state)
    (hactive : state.heap (header + 2) ≤ B)
    (hgood : state.heap (header + 4) ≤ q + 2) (hbad : state.heap (header + 5) ≤ q + 2)
    (htool : state.heap toolAddress ≤ B) :
    NumericSafe B heapWords rom (PA17QueryRanks011.replyProgram q header toolAddress) state := by
  have hmin : min (state.heap (header + 4)) (state.heap (header + 5) + 1) ≤ B :=
    (min_le_left _ _).trans (hgood.trans (by omega))
  constructor
  · intro count hc register
    have hr := hregister register
    change count ≤ 17 at hc
    interval_cases count <;> cases register <;>
      simp [PA17QueryRanks011.replyProgram, IndexedClosureRAM.execute, Op.execute, Instruction.execute]
    all_goals (try split_ifs)
    all_goals omega
  · intro count hc
    change count < 17 at hc
    interval_cases count <;>
      simp [PA17QueryRanks011.replyProgram, IndexedClosureRAM.execute, Op.execute, Instruction.execute, AccessFits]
    all_goals omega

structure Layout (B heapWords q goodFlags badFlags header : Nat) : Prop where
  good_access : goodFlags + (q + 2) ≤ heapWords
  bad_access : badFlags + (q + 2) ≤ heapWords
  good_bound : goodFlags + (q + 2) ≤ B
  bad_bound : badFlags + (q + 2) ≤ B
  header_access : header + 8 ≤ heapWords
  header_bound : header + 8 ≤ B
  q_bound : q + 3 ≤ B
  header_before_bad : header + 4 < badFlags

theorem program_numeric (B heapWords q goodFlags badFlags header : Nat) (rom : PhysicalROM)
    (hl : Layout B heapWords q goodFlags badFlags header) (good bad : Nat → Bool)
    (state : State) (hregister : RegistersLE B state) (hactive : state.heap (header + 2) ≤ B)
    (hgoodFlags : ∀ budget < q + 2, state.heap (goodFlags + budget) = bit (good budget))
    (hbadFlags : ∀ budget < q + 2, state.heap (badFlags + budget) = bit (bad budget)) :
    NumericSafe B heapWords rom (PA17QueryRanks011.program q goodFlags badFlags header) state := by
  have hq : q + 2 ≤ B := by have := hl.q_bound; omega
  have hbit (value : Bool) : bit value ≤ B := by
    have h1 : 1 ≤ B := by have := hl.q_bound; omega
    cases value
    · simp [bit]
    · simpa [bit] using h1
  let first := execute rom.semantic (PA17QueryRanks011.rankProgram q goodFlags (header + 4)) state
  have hgheap := PA17QueryRanks011.rankProgram_heap q goodFlags (header + 4) rom.semantic good state hgoodFlags
  have hg := rankProgram_numeric B heapWords q goodFlags (header + 4) rom hl.good_access hl.good_bound
    (by have := hl.header_access; omega) (by have := hl.header_bound; omega) hq state hregister
    (by intro budget hb; rw [hgoodFlags budget hb]; exact hbit _)
  have hbf (budget : Nat) (hb : budget < q + 2) : first.heap (badFlags + budget) = bit (bad budget) := by
    rw [hgheap, Function.update_of_ne (by have := hl.header_before_bad; omega)]
    exact hbadFlags budget hb
  have hb := rankProgram_numeric B heapWords q badFlags (header + 5) rom hl.bad_access hl.bad_bound
    (by have := hl.header_access; omega) (by have := hl.header_bound; omega) hq first
    (NumericSafe.final _ _ _ _ _ hg) (by intro budget hbudget; rw [hbf budget hbudget]; exact hbit _)
  let second := execute rom.semantic (PA17QueryRanks011.rankProgram q badFlags (header + 5)) first
  have hbheap := PA17QueryRanks011.rankProgram_heap q badFlags (header + 5) rom.semantic bad first hbf
  have ha : second.heap (header + 2) ≤ B := by
    rw [hbheap, hgheap, Function.update_of_ne (by omega), Function.update_of_ne (by omega)]
    exact hactive
  have hgood : second.heap (header + 4) ≤ q + 2 := by
    rw [hbheap, hgheap, Function.update_of_ne (by omega), Function.update_self,
      ← PA17QueryRanks011.firstFalseValue_eq_encodeRank]
    exact PA17QueryRanks011.firstFalseValue_le q good
  have hbad : second.heap (header + 5) ≤ q + 2 := by
    rw [hbheap, Function.update_self, ← PA17QueryRanks011.firstFalseValue_eq_encodeRank]
    exact PA17QueryRanks011.firstFalseValue_le q bad
  rw [PA17QueryRanks011.program]
  apply NumericSafe.append B heapWords rom _ _ state (NumericSafe.append B heapWords rom _ _ state hg hb)
  simpa only [IndexedClosureRAM.execute_append] using
    finish_numeric B heapWords q header rom hl.header_access hl.header_bound hl.q_bound second
    (NumericSafe.final _ _ _ _ _ hb) ha hgood hbad

end PaperProofs.Structure.LaminarTree.PA17QueryRanksWord027
