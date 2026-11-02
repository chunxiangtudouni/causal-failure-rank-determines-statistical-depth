module

public import PaperProofs.Structure.PSTR_RuntimePackedRead_008
public import PaperProofs.Structure.RawTreePreprocessingClaims
import Mathlib.Tactic.IntervalCases

/-! Physical access/decoder safety and complete heap frame for every actual
prefix of the fixed runtime-width packed reader. Layout premises remain
explicit until the whole controller discharges them. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimePackedReadSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims RawTreePreprocessingClaims
open PSTRRuntimePackedRead

set_option maxRecDepth 10000 in
theorem access_prefix {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (heapWords : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hn : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hheap : 4 + (state.register .address).toNat * CapacityBits.width q / bits + 1 < heapWords)
    (count : Nat) (hc : count < program.length) :
    packingAccessFits rom heapWords (executeOps rom (program.take count) state) program[count] := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hstart : start < 2 ^ bits := hs
  have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hthree : 3 < 2 ^ bits := by omega
  have hwidthFit : CapacityBits.width q < 2 ^ bits := hw.trans_lt hbits
  have hdiv : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hstart
  have hprod : start / bits * bits < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hstart
  have hphysical1 : 4 + start / bits + 1 < 2 ^ bits := hn
  have hphysical0 : 4 + start / bits < 2 ^ bits := by omega
  have haccess : 4 + start / bits + 1 < heapWords := hheap
  have hheaderAccess : 3 < heapWords :=
    ((show 3 ≤ 4 by decide).trans
      ((Nat.le_add_right 4 (start / bits)).trans (Nat.le_add_right _ 1))).trans_lt haccess
  have hphysicalComm : start / bits + 4 = 4 + start / bits := by omega
  change count < 17 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [program, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
    executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
    ↓reduceIte, hwidth, header_word state hh, arithmetic_multiply, arithmetic_divide,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hbits, Nat.mod_eq_of_lt hthree,
    Nat.mod_eq_of_lt hwidthFit,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hstart, Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hprod,
    hphysicalComm, Nat.mod_eq_of_lt hphysical0, Nat.mod_eq_of_lt hphysical1]
  all_goals first | exact hheaderAccess | omega

theorem execute_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (count : Nat) : (executeOps rom (program.take count) state).heap = state.heap := by
  by_cases hc : count ≤ 17
  · interval_cases count <;> rfl
  · rw [List.take_of_length_le (show program.length ≤ count by rw [program_length]; omega)]
    rfl

theorem actual_prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (count : Nat) (hc : count ≤ 18) :
    (packingRun rom program count state).heap = state.heap := by
  by_cases hbody : count ≤ program.length
  · rw [packingRun_eq_executeOps_take rom _ _ program_straight (code_fit hb) (pc_fit hb) hp ha count hbody]
    exact execute_prefix_heap rom state count
  · have he : count = program.length + 1 := by rw [program_length] at *; omega
    rw [he, packingRun_executeOps_halt rom _ _ program_straight (code_fit hb) (pc_fit hb) hp ha]
    exact execute_heap rom state

theorem actual_path {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (heapWords : Nat) (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hn : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hheap : 4 + (state.register .address).toNat * CapacityBits.width q / bits + 1 < heapWords)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    ∀ count < 18,
      let current := packingRun rom program count state
      current.halted = false ∧ current.pc.toNat + 4 < (packingCode program).length ∧
      match PackingOp.decode (fetch program current) with
      | none => fetch program current = haltWords
      | some op => packingAccessFits rom heapWords current op := by
  intro count hc
  have hcount : count ≤ program.length := by rw [program_length]; omega
  have run := packingRun_eq_executeOps_take rom program state program_straight (code_fit hb)
    (pc_fit hb) hp ha count hcount
  have active : (packingRun rom program count state).halted = false := by
    rw [run, executeOps_halted, ha]
  have pc : (packingRun rom program count state).pc.toNat = 5 * count := by
    rw [run, executeOps_pc rom _ state (fun op ho => program_straight op (List.mem_of_mem_take ho)),
      hp, BitVec.zero_add, List.length_take_of_le hcount, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hcount).trans_lt (pc_fit hb))
  have fetchEq : fetch program (packingRun rom program count state) = natFetch program (5 * count) := by
    change physicalFetch bits (packingCode program) _ = _
    rw [physicalFetch_eq bits _ _ (code_fit hb), pc]
    rfl
  refine ⟨active, ?_, ?_⟩
  · rw [pc, code_length]
    rw [program_length] at hcount
    omega
  · rw [fetchEq]
    by_cases hbody : count < program.length
    · rw [natFetch_body program count hbody, decode_encode, run]
      exact access_prefix rom state heapWords hb hw hwidth hh hs hn hheap count hbody
    · have he : count = program.length := by omega
      subst count
      rw [natFetch_halt, decode_halt]

theorem actual_prefix_capacity {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (capWords : Nat) (hb : 8 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (bounded : CapacityPrefixBounded q capWords (logicalHeap q capWords state.heap))
    (count : Nat) (hc : count ≤ 18) :
    CapacityPrefixBounded q capWords
      (logicalHeap q capWords (packingRun rom program count state).heap) := by
  rw [actual_prefix_heap rom state hb hp ha count hc]
  exact bounded

end PaperProofs.Structure.LaminarTree.PSTRRuntimePackedReadSafety
