module

public import PaperProofs.Structure.PSTR_RuntimePackedRead_008

/-! The live used-bitmap update only sets the least-significant bit of its
scalar, so one physical store suffices. Its semantic insertion/frame proof
uses the original zero unused bit, rather than a general capacity replacement. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimeMarkUsed

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def program : List PackingOp :=
  [.arithmetic .multiply .old .address .total,
   .base (.base (.constant .index 3)),
   .base (.base (.loadHeap .total .index)),
   .arithmetic .divide .index .old .total,
   .arithmetic .multiply .fresh .index .total,
   .base (.subtract .old .old .fresh),
   .base (.base (.constant .fresh 4)),
   .base (.base (.add .index .index .fresh)),
   .base (.base (.loadHeap .value .index)),
   .base (.base (.constant .fresh 1)),
   .arithmetic .shiftLeft .fresh .fresh .old,
   .arithmetic .bitOr .value .value .fresh,
   .base (.base (.storeHeap .index .value))]

def markHeap {bits : Nat} (start : Nat) (heap : BitVec bits → BitVec bits) :
    BitVec bits → BitVec bits :=
  Function.update heap (BitVec.ofNat bits (4 + start / bits))
    (heap (BitVec.ofNat bits (4 + start / bits)) |||
      ((BitVec.ofNat bits 1) <<< (start % bits)))

theorem program_length : program.length = 13 := rfl

theorem program_straight : StraightProgram program := by
  simp [StraightProgram, StraightOp, program]

theorem code_length : (packingCode program).length = 70 := by
  rw [packingCode_length, program_length]

theorem code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  simp [packingCode, program, PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
    PackingPrimitive.word, Register.word, Region.word, haltWords] at hv
  unfold Fits
  omega

theorem pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 65 < 2 ^ bits
  omega

set_option maxRecDepth 6000 in
theorem execute_heap {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q)) :
    (executeOps rom program state).heap =
      markHeap ((state.register .address).toNat * CapacityBits.width q) state.heap := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hstart : start < 2 ^ bits := hs
  have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hwidthFit : CapacityBits.width q < 2 ^ bits := hw.trans_lt hbits
  have hdiv : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hstart
  have hprod : start / bits * bits < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hstart
  have hmod : start % bits < bits := Nat.mod_lt _ hb
  have hmodFit : start % bits < 2 ^ bits := hmod.trans hbits
  have hsub : start - start / bits * bits = start % bits := by
    have he := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at he
    omega
  have hphysComm : start / bits + 4 = 4 + start / bits := by omega
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hwidth, PSTRRuntimePackedRead.header_word state hh,
    arithmetic_or, arithmetic_shiftLeft, arithmetic_multiply, arithmetic_divide,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hbits,
    Nat.mod_eq_of_lt hwidthFit,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hstart, Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hprod,
    hsub, Nat.mod_eq_of_lt hmodFit, hphysComm, markHeap]

theorem prefix_heap {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (count : Nat) (hc : count ≤ 13) :
    (executeOps rom (program.take count) state).heap =
      if count < 13 then state.heap
      else markHeap ((state.register .address).toNat * CapacityBits.width q) state.heap := by
  by_cases hlt : count < 13
  · rw [ite_eq_left hlt]
    interval_cases count <;> rfl
  · have he : count = 13 := by omega
    subst count
    rw [ite_eq_right (by decide), show 13 = program.length from rfl, List.take_length]
    exact execute_heap rom state hb hw hwidth hh hs

theorem markHeap_frame {bits : Nat} (start : Nat) (heap : BitVec bits → BitVec bits)
    (address : BitVec bits) (hne : address ≠ BitVec.ofNat bits (4 + start / bits)) :
    markHeap start heap address = heap address := by
  exact Function.update_of_ne hne _ _

theorem markHeap_header {bits : Nat} (start : Nat) (heap : BitVec bits → BitVec bits)
    (hb : 8 ≤ bits) (hptr : Fits bits (4 + start / bits)) (header : Nat) (hh : header < 4) :
    markHeap start heap (BitVec.ofNat bits header) = heap (BitVec.ofNat bits header) := by
  apply markHeap_frame
  have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hheader : Fits bits header := hh.trans (show 4 < 2 ^ bits by omega)
  apply (ofNat_injective_of_fit header (4 + start / bits) hheader hptr).not.mpr
  exact ne_of_lt (hh.trans_le (Nat.le_add_right 4 (start / bits)))

theorem actual_run {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    let after := packingRun rom program 14 state
    after.halted = true ∧ after.heap =
      markHeap ((state.register .address).toNat * CapacityBits.width q) state.heap := by
  dsimp only
  rw [show 14 = program.length + 1 from rfl,
    packingRun_executeOps_halt rom _ _ program_straight (code_fit hb) (pc_fit hb) hp ha]
  exact ⟨rfl, execute_heap rom state (by omega) hw hwidth hh hs⟩

theorem actual_trace_bound {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (packingDynamicTrace rom program 14 state).length ≤ 168 :=
  packingDynamicTrace_length_le rom program 14 state

end PaperProofs.Structure.LaminarTree.PSTRRuntimeMarkUsed
