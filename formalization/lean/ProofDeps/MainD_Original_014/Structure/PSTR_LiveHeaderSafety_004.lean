module

public import Structure.PSTR_LiveHeader_003
import Mathlib.Tactic.IntervalCases

/-! Every physical header-loader prefix is safe on the original callInput.
Only numeric word/footprint premises appear here; the fixed controller's
global layout must later discharge them. No call-performance claim is assumed. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLiveHeaderSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open RawTreePreprocessingClaims PackingMachine PSTRLiveHeader

theorem input_fit {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (hb : 8 ≤ bits) (hN : Fits bits full.length) (hq : Fits bits q) :
    ∀ region, WordsFit bits ((callInput q full command).words region) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have h0 : Fits bits 0 := by unfold Fits; omega
  have h1 : Fits bits 1 := by unfold Fits; omega
  have h2 : Fits bits 2 := by unfold Fits; omega
  intro region value hv
  cases region with
  | input =>
    change value ∈ ([full.length, q] ++ incidence full) ++ [command.word] at hv
    rcases List.mem_append.mp hv with hraw | hcmd
    · rcases List.mem_append.mp hraw with hd | hi
      · simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
        rcases hd with rfl | rfl
        · exact hN
        · exact hq
      · obtain ⟨eligible, _he, hi⟩ := List.mem_flatMap.mp hi
        obtain ⟨tool, _ht, rfl⟩ := List.mem_map.mp hi
        unfold bit
        split <;> assumption
    · have he : value = command.word := List.mem_singleton.mp hcmd
      subst value
      cases command <;> assumption
  | internal => cases hv
  | children => cases hv

theorem access_prefix {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heapWords : Nat) (state : WordState bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hq : Fits bits q) (hpos : Fits bits (2 + full.length * q))
    (count : Nat) (hc : count < program.length) :
    packingAccessFits (callInput q full command) heapWords
      (executeOps (callInput q full command) (program.take count) state) program[count] := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have h0 : (0 : Nat) < 2 ^ bits := by omega
  have h1 : (1 : Nat) < 2 ^ bits := by omega
  have hread0 : ((callInput q full command).words .input).getD 0 0 = full.length := input_N q full command
  have hread1 : ((callInput q full command).words .input).getD 1 0 = q := input_q q full command
  have hlen := input_length q full command
  change count < 8 at hc
  interval_cases count <;>
    simp +decide only [program, List.take_succ_cons, List.take_zero,
      List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
      executeOps, packingExecuteOp, wordOp, wordInstruction, packingArithmetic,
      Function.update_apply, ↓reduceIte, hread0, hread1, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt h0, Nat.mod_eq_of_lt h1,
      Nat.mod_eq_of_lt hN, Nat.mod_eq_of_lt hq,
      BitVec.ofNat_add_ofNat, Nat.add_comm (full.length * q) 2, Nat.mod_eq_of_lt hpos]
  all_goals change _ < (callInput q full command).input.length
  all_goals omega

theorem dynamic_correct {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heapWords : Nat) (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (hN : Fits bits full.length) (hq : Fits bits q) (hpos : Fits bits (2 + full.length * q))
    (hfoot : Fits bits ((callInput q full command).size + heapWords + (packingCode program).length)) :
    DynamicRunCorrect heapWords (callInput q full command) program 9 heap := by
  let rom := callInput q full command
  let state := packingInitial heap
  have code := program_code_fit hb
  have pcfit := program_pc_fit hb
  refine ⟨code, input_fit full command hb hN hq, hfoot,
    (actual_run full command state hb hN hq hpos rfl rfl).1, ?_⟩
  intro count hc
  have hcount : count ≤ program.length := by rw [program_length]; omega
  have run := packingRun_eq_executeOps_take rom program state program_straight code pcfit rfl rfl count hcount
  have active : (packingRun rom program count state).halted = false := by
    rw [run, executeOps_halted]
    rfl
  have pc : (packingRun rom program count state).pc.toNat = 5 * count := by
    rw [run, executeOps_pc rom _ state (fun op ho => program_straight op (List.mem_of_mem_take ho))]
    change (BitVec.ofNat bits 0 + BitVec.ofNat bits (5 * (program.take count).length)).toNat = _
    rw [BitVec.zero_add, List.length_take_of_le hcount, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt (lt_of_le_of_lt (Nat.mul_le_mul_left 5 hcount) pcfit)
  have fetchEq : fetch program (packingRun rom program count state) = natFetch program (5 * count) := by
    change physicalFetch bits (packingCode program) _ = _
    rw [physicalFetch_eq bits _ _ code, pc]
    rfl
  refine ⟨active, ?_, ?_⟩
  · rw [pc, program_code_length]
    rw [program_length] at hcount
    omega
  · rw [fetchEq]
    by_cases hbody : count < program.length
    · rw [natFetch_body program count hbody, decode_encode]
      rw [run]
      exact access_prefix full command heapWords state hb hN hq hpos count hbody
    · have he : count = program.length := by omega
      subst count
      rw [natFetch_halt, decode_halt]

theorem actual_call_cost {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits) :
    callCost q full program command 9 heap ≤ 310 := by
  have ht := actual_trace_bound (callInput q full command) (packingInitial heap) hb rfl rfl
  unfold callCost
  rw [program_code_length]
  omega

theorem actual_prefix_heap {bits : Nat} (rom : PhysicalROM) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (count : Nat) (hc : count ≤ 9) :
    (packingRun rom program count (packingInitial heap)).heap = heap := by
  by_cases hbody : count ≤ program.length
  · rw [packingRun_eq_executeOps_take rom _ _ program_straight (program_code_fit hb)
      (program_pc_fit hb) rfl rfl count hbody]
    exact execute_prefix_heap rom (packingInitial heap) count
  · have he : count = program.length + 1 := by rw [program_length] at *; omega
    rw [he, packingRun_executeOps_halt rom _ _ program_straight (program_code_fit hb)
      (program_pc_fit hb) rfl rfl]
    exact execute_heap rom (packingInitial heap)

theorem actual_prefix_capacity {bits q : Nat} (full : List (Finset (Fin q))) (command : Command)
    (capWords : Nat) (heap : BitVec bits → BitVec bits) (hb : 8 ≤ bits)
    (bounded : CapacityPrefixBounded q capWords (logicalHeap q capWords heap))
    (count : Nat) (hc : count ≤ 9) :
    CapacityPrefixBounded q capWords (logicalHeap q capWords
      (packingRun (callInput q full command) program count (packingInitial heap)).heap) := by
  rw [actual_prefix_heap _ heap hb count hc]
  exact bounded

end PaperProofs.Structure.LaminarTree.PSTRLiveHeaderSafety
