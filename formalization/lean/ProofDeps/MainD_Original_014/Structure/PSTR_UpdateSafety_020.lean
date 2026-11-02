module

public import Structure.PSTR_RuntimeRepair_017
public import Structure.PSTR_RuntimeFail_019
public import PaperProofs.Structure.RawTreePreprocessingClaims
import Mathlib.Tactic.IntervalCases

/-! Fetched execution and concrete access proofs for the real stage and
failed-word updates. The generic straight-block lemma is discharged below
with actual original ISA access checks, rather than assumed as a full claim. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRUpdateSafety

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open CompactControllerClaims RawTreePreprocessingClaims

theorem straight_path {bits : Nat} (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (heapWords : Nat)
    (hstraight : StraightProgram program) (hcode : WordsFit bits (packingCode program))
    (hpcfit : Fits bits (5 * program.length))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false)
    (haccess : ∀ count (hc : count < program.length),
      packingAccessFits rom heapWords (executeOps rom (program.take count) state) program[count]) :
    ∀ count < program.length + 1,
      let current := packingRun rom program count state
      current.halted = false ∧ current.pc.toNat + 4 < (packingCode program).length ∧
      match PackingOp.decode (fetch program current) with
      | none => fetch program current = haltWords
      | some op => packingAccessFits rom heapWords current op := by
  intro count hc
  have hcount : count ≤ program.length := by omega
  have run := packingRun_eq_executeOps_take rom program state hstraight hcode hpcfit hp ha count hcount
  have active : (packingRun rom program count state).halted = false := by
    rw [run, executeOps_halted, ha]
  have pc : (packingRun rom program count state).pc.toNat = 5 * count := by
    rw [run, executeOps_pc rom _ state (fun op ho => hstraight op (List.mem_of_mem_take ho)),
      hp, BitVec.zero_add, List.length_take_of_le hcount, BitVec.toNat_ofNat]
    exact Nat.mod_eq_of_lt ((Nat.mul_le_mul_left 5 hcount).trans_lt hpcfit)
  have fetchEq : fetch program (packingRun rom program count state) = natFetch program (5 * count) := by
    change physicalFetch bits (packingCode program) _ = _
    rw [physicalFetch_eq bits _ _ hcode, pc]
    rfl
  refine ⟨active, ?_, ?_⟩
  · rw [pc, packingCode_length]
    omega
  · rw [fetchEq]
    by_cases hbody : count < program.length
    · rw [natFetch_body program count hbody, decode_encode, run]
      exact haccess count hbody
    · have he : count = program.length := by omega
      subst count
      rw [natFetch_halt, decode_halt]

set_option maxRecDepth 10000 in
theorem advance_access {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (heapWords packed : Nat) (hb : 8 ≤ bits)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hptr : Fits bits (4 + packed)) (hheap : 4 + packed < heapWords)
    (count : Nat) (hc : count < PSTRRuntimeAdvance.program.length) :
    packingAccessFits rom heapWords
      (executeOps rom (PSTRRuntimeAdvance.program.take count) state)
      PSTRRuntimeAdvance.program[count] := by
  have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
  have htwo : 2 < 2 ^ bits := by omega
  have hcomm : packed + 4 = 4 + packed := by omega
  change count < 8 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [PSTRRuntimeAdvance.program, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
    executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
    ↓reduceIte, PSTRRuntimeAdvance.header_word state packed hh,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt htwo,
    hcomm, Nat.mod_eq_of_lt hptr]
  all_goals omega

theorem advance_path {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (heapWords packed : Nat) (hb : 8 ≤ bits)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hptr : Fits bits (4 + packed)) (hheap : 4 + packed < heapWords)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    ∀ count < 9,
      let current := packingRun rom PSTRRuntimeAdvance.program count state
      current.halted = false ∧ current.pc.toNat + 4 < (packingCode PSTRRuntimeAdvance.program).length ∧
      match PackingOp.decode (fetch PSTRRuntimeAdvance.program current) with
      | none => fetch PSTRRuntimeAdvance.program current = haltWords
      | some op => packingAccessFits rom heapWords current op :=
  straight_path rom PSTRRuntimeAdvance.program state heapWords PSTRRuntimeAdvance.program_straight
    (PSTRRuntimeAdvance.code_fit hb) (PSTRRuntimeAdvance.pc_fit hb) hp ha
    (advance_access rom state heapWords packed hb hh hptr hheap)

set_option maxRecDepth 10000 in
theorem fail_access {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (heapWords packed : Nat) (hb : 8 ≤ bits)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hptr : Fits bits (5 + packed)) (hheap : 5 + packed < heapWords)
    (count : Nat) (hc : count < PSTRRuntimeFail.program.length) :
    packingAccessFits rom heapWords
      (executeOps rom (PSTRRuntimeFail.program.take count) state)
      PSTRRuntimeFail.program[count] := by
  have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
  have htwo : 2 < 2 ^ bits := by omega
  have hcomm : packed + 5 = 5 + packed := by omega
  change count < 6 at hc
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [PSTRRuntimeFail.program, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, packingAccessFits, AccessFits,
    executeOps, packingExecuteOp, wordOp, wordInstruction, Function.update_apply,
    ↓reduceIte, PSTRRuntimeAdvance.header_word state packed hh,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt htwo,
    hcomm, Nat.mod_eq_of_lt hptr]
  all_goals omega

theorem fail_path {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (heapWords packed : Nat) (hb : 8 ≤ bits)
    (hh : (state.heap (BitVec.ofNat bits 2)).toNat = packed)
    (hptr : Fits bits (5 + packed)) (hheap : 5 + packed < heapWords)
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    ∀ count < 7,
      let current := packingRun rom PSTRRuntimeFail.program count state
      current.halted = false ∧ current.pc.toNat + 4 < (packingCode PSTRRuntimeFail.program).length ∧
      match PackingOp.decode (fetch PSTRRuntimeFail.program current) with
      | none => fetch PSTRRuntimeFail.program current = haltWords
      | some op => packingAccessFits rom heapWords current op :=
  straight_path rom PSTRRuntimeFail.program state heapWords PSTRRuntimeFail.program_straight
    (PSTRRuntimeFail.code_fit hb) (PSTRRuntimeFail.pc_fit hb) hp ha
    (fail_access rom state heapWords packed hb hh hptr hheap)

theorem advance_dynamic_correct {bits : Nat} (rom : PhysicalROM) (heap : BitVec bits → BitVec bits)
    (heapWords packed : Nat) (hb : 8 ≤ bits)
    (hh : (heap (BitVec.ofNat bits 2)).toNat = packed)
    (hptr : Fits bits (4 + packed)) (hheap : 4 + packed < heapWords)
    (hrom : ∀ region, WordsFit bits (rom.words region))
    (hfoot : Fits bits (rom.size + heapWords + (packingCode PSTRRuntimeAdvance.program).length)) :
    DynamicRunCorrect heapWords rom PSTRRuntimeAdvance.program 9 heap := by
  refine ⟨PSTRRuntimeAdvance.code_fit hb, hrom, hfoot,
    (PSTRRuntimeAdvance.actual_run rom (packingInitial heap) packed hb hh rfl rfl).1, ?_⟩
  exact advance_path rom (packingInitial heap) heapWords packed hb hh hptr hheap rfl rfl

theorem fail_dynamic_correct {bits : Nat} (rom : PhysicalROM) (heap : BitVec bits → BitVec bits)
    (heapWords packed : Nat) (hb : 8 ≤ bits)
    (hh : (heap (BitVec.ofNat bits 2)).toNat = packed)
    (hptr : Fits bits (5 + packed)) (hheap : 5 + packed < heapWords)
    (hrom : ∀ region, WordsFit bits (rom.words region))
    (hfoot : Fits bits (rom.size + heapWords + (packingCode PSTRRuntimeFail.program).length)) :
    DynamicRunCorrect heapWords rom PSTRRuntimeFail.program 7 heap := by
  refine ⟨PSTRRuntimeFail.code_fit hb, hrom, hfoot, ?_, ?_⟩
  · rw [show 7 = PSTRRuntimeFail.program.length + 1 from rfl,
      packingRun_executeOps_halt rom _ _ PSTRRuntimeFail.program_straight
        (PSTRRuntimeFail.code_fit hb) (PSTRRuntimeFail.pc_fit hb) rfl rfl]
  · exact fail_path rom (packingInitial heap) heapWords packed hb hh hptr hheap rfl rfl

end PaperProofs.Structure.LaminarTree.PSTRUpdateSafety
