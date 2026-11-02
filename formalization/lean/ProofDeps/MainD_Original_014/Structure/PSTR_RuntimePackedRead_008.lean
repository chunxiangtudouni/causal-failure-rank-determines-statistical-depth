module

public import PaperProofs.Structure.PackedCapacityRAM
public import PaperProofs.Structure.CompactControllerClaims
import Mathlib.Tactic.IntervalCases

/-! Fixed packed scalar read for the original four-word A19 header layout.
The width and its mask are ordinary runtime registers; bits is read from
actual heap word 3. Neither q nor bits occurs as a code-generation parameter. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimePackedRead

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
   .arithmetic .shiftRight .value .value .old,
   .base (.base (.constant .fresh 1)),
   .base (.base (.add .index .index .fresh)),
   .base (.base (.loadHeap .fresh .index)),
   .base (.subtract .old .total .old),
   .arithmetic .shiftLeft .fresh .fresh .old,
   .arithmetic .bitOr .value .value .fresh,
   .arithmetic .bitAnd .value .value .flag]

theorem program_length : program.length = 17 := rfl

theorem program_straight : StraightProgram program := by
  simp [StraightProgram, StraightOp, program]

theorem code_length : (packingCode program).length = 90 := by
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
  change 85 < 2 ^ bits
  omega

theorem header_word {bits : Nat} (state : WordState bits)
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits) :
    state.heap (BitVec.ofNat bits 3) = BitVec.ofNat bits bits := by
  have he := congrArg (BitVec.ofNat bits) hh
  simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he

set_option maxRecDepth 6000 in
theorem execute_value {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.register .flag = lowMask bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits + 1)) :
    (executeOps rom program state).register .value =
      readTwoWords (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q % bits)
        (state.heap (BitVec.ofNat bits (4 + (state.register .address).toNat * CapacityBits.width q / bits)))
        (state.heap (BitVec.ofNat bits (4 + (state.register .address).toNat * CapacityBits.width q / bits + 1))) := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hstart : start < 2 ^ bits := hs
  have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hwidthFit : CapacityBits.width q < 2 ^ bits := hw.trans_lt hbits
  have hdiv : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hprod : start / bits * bits < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hs
  have hmod : start % bits < bits := Nat.mod_lt _ hb
  have hmodFit : start % bits < 2 ^ bits := hmod.trans hbits
  have hsub : start - start / bits * bits = start % bits := by
    have he := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at he
    omega
  have hright : bits - start % bits < 2 ^ bits := (Nat.sub_le _ _).trans_lt hbits
  have hphysical : 4 + start / bits < 2 ^ bits := by
    change 4 + start / bits + 1 < 2 ^ bits at hnext
    omega
  have hphysComm : start / bits + 4 = 4 + start / bits := by omega
  simp +decide only [program, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hwidth, hmask, header_word state hh,
    arithmetic_and, arithmetic_or, arithmetic_shiftLeft, arithmetic_shiftRight,
    arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat,
    BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hbits, Nat.mod_eq_of_lt hwidthFit,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hstart, Nat.mod_eq_of_lt hdiv, Nat.mod_eq_of_lt hprod,
    hsub, Nat.mod_eq_of_lt hmodFit, Nat.mod_eq_of_lt hright,
    hphysComm, readTwoWords]

theorem execute_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom program state).heap = state.heap := rfl

theorem dataHeap_at {bits : Nat} (heap : BitVec bits → BitVec bits) (address : Nat)
    (ha : Fits bits address) :
    dataHeap heap (BitVec.ofNat bits address) = heap (BitVec.ofNat bits (4 + address)) := by
  simp only [dataHeap, physicalHeaderWords, BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha]

theorem execute_capacity {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hq : 0 < q) (hb : 0 < bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.register .flag = lowMask bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (capWords : Nat) (ha : (state.register .address).toNat < capWords)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hn : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits + 1)) :
    ((executeOps rom program state).register .value).toNat =
      logicalHeap q capWords state.heap (state.register .address).toNat := by
  rw [execute_value rom state hb hw hwidth hmask hh hs hn]
  have hd : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits) :=
    (Nat.div_le_self _ _).trans_lt hs
  have hd1 : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1) := by
    unfold Fits at hn ⊢
    omega
  have he := readTwoWords_eq_unpackHeap q capWords (state.register .address).toNat
    (dataHeap state.heap) hb hw ha
  rw [dataHeap_at _ _ hd, dataHeap_at _ _ hd1] at he
  simpa only [logicalHeap, ne_of_gt hq, ite_false, Nat.add_assoc] using he

theorem actual_run {bits q : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hw : CapacityBits.width q ≤ bits)
    (hwidth : state.register .total = BitVec.ofNat bits (CapacityBits.width q))
    (hmask : state.register .flag = lowMask bits (CapacityBits.width q))
    (hh : (state.heap (BitVec.ofNat bits 3)).toNat = bits)
    (hs : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hn : Fits bits (4 + (state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hp : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    let after := packingRun rom program 18 state
    after.halted = true ∧ after.heap = state.heap ∧
      after.register .value = readTwoWords (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q % bits)
        (state.heap (BitVec.ofNat bits (4 + (state.register .address).toNat * CapacityBits.width q / bits)))
        (state.heap (BitVec.ofNat bits (4 + (state.register .address).toNat * CapacityBits.width q / bits + 1))) := by
  dsimp only
  rw [show 18 = program.length + 1 from rfl,
    packingRun_executeOps_halt rom _ _ program_straight (code_fit hb) (pc_fit hb) hp hactive]
  exact ⟨rfl, execute_heap rom state, execute_value rom state (by omega) hw hwidth hmask hh hs hn⟩

theorem actual_trace_bound {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (packingDynamicTrace rom program 18 state).length ≤ 216 :=
  packingDynamicTrace_length_le rom program 18 state

end PaperProofs.Structure.LaminarTree.PSTRRuntimePackedRead
