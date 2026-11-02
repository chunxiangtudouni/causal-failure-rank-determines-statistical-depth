module

public import Structure.PA06_A19Prepare_RuntimePacked016
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 20000
set_option maxHeartbeats 2000000

/-! Fixed actual base-four replacement writer. The real runtime source
loads width/mask/allOnes/bits from physical headers and contains only the
small immediates 0,1,2,3,4. It first clears both fragments, then fills both;
it is valid for repeated DP workspace updates, not just zero/OR writes.
Uncompiled private source candidate. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimePacked016

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open CompactControllerClaims (dataHeap)

variable {bits : Nat}

def clear : List PackingOp :=
  [.base (.base (.constant .total 0)),
   .base (.base (.loadHeap .total .total)),
   .arithmetic .multiply .old .address .total,
   .base (.base (.constant .total 3)),
   .base (.base (.loadHeap .total .total)),
   .arithmetic .divide .index .old .total,
   .arithmetic .multiply .fresh .index .total,
   .base (.subtract .old .old .fresh),
   .base (.base (.constant .fresh 4)),
   .base (.base (.add .index .index .fresh)),
   .base (.base (.constant .fresh 1)),
   .base (.base (.loadHeap .fresh .fresh)),
   .arithmetic .shiftLeft .fresh .fresh .old,
   .base (.base (.constant .flag 2)),
   .base (.base (.loadHeap .flag .flag)),
   .base (.subtract .fresh .flag .fresh),
   .base (.base (.loadHeap .flag .index)),
   .arithmetic .bitAnd .flag .flag .fresh,
   .base (.base (.storeHeap .index .flag)),
   .base (.subtract .old .total .old),
   .base (.base (.constant .fresh 1)),
   .base (.base (.loadHeap .fresh .fresh)),
   .arithmetic .shiftRight .fresh .fresh .old,
   .base (.base (.constant .flag 2)),
   .base (.base (.loadHeap .flag .flag)),
   .base (.subtract .fresh .flag .fresh),
   .base (.base (.constant .flag 1)),
   .base (.base (.add .index .index .flag)),
   .base (.base (.loadHeap .flag .index)),
   .arithmetic .bitAnd .flag .flag .fresh,
   .base (.base (.storeHeap .index .flag))]

def directWrite : List PackingOp :=
  [.base (.base (.constant .total 0)),
   .base (.base (.loadHeap .total .total)),
   .arithmetic .multiply .old .address .total,
   .base (.base (.constant .total 3)),
   .base (.base (.loadHeap .total .total)),
   .arithmetic .divide .index .old .total,
   .arithmetic .multiply .fresh .index .total,
   .base (.subtract .old .old .fresh),
   .base (.base (.constant .fresh 4)),
   .base (.base (.add .index .index .fresh)),
   .base (.base (.constant .fresh 1)),
   .base (.base (.loadHeap .fresh .fresh)),
   .arithmetic .shiftLeft .fresh .fresh .old,
   .base (.base (.constant .flag 2)),
   .base (.base (.loadHeap .flag .flag)),
   .base (.subtract .fresh .flag .fresh),
   .base (.base (.loadHeap .flag .index)),
   .arithmetic .bitAnd .flag .flag .fresh,
   .arithmetic .shiftLeft .fresh .value .old,
   .arithmetic .bitOr .flag .flag .fresh,
   .base (.base (.storeHeap .index .flag)),
   .base (.subtract .old .total .old),
   .base (.base (.constant .fresh 1)),
   .base (.base (.loadHeap .fresh .fresh)),
   .arithmetic .shiftRight .fresh .fresh .old,
   .base (.base (.constant .flag 2)),
   .base (.base (.loadHeap .flag .flag)),
   .base (.subtract .fresh .flag .fresh),
   .base (.base (.constant .flag 1)),
   .base (.base (.add .index .index .flag)),
   .base (.base (.loadHeap .flag .index)),
   .arithmetic .bitAnd .flag .flag .fresh,
   .arithmetic .shiftRight .fresh .value .old,
   .arithmetic .bitOr .flag .flag .fresh,
   .base (.base (.storeHeap .index .flag))]

def safeWrite : List PackingOp := clear ++ directWrite

theorem clear_length : clear.length = 31 := rfl
theorem directWrite_length : directWrite.length = 35 := rfl
theorem safeWrite_length : safeWrite.length = 66 := rfl
theorem safeWrite_code_length : (packingCode safeWrite).length = 335 := rfl
theorem safeWrite_trace_length : (packingTrace safeWrite).length = 684 := rfl

def physicalClearLow (width start : Nat) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update heap (BitVec.ofNat bits (start / bits + 4))
    (heap (BitVec.ofNat bits (start / bits + 4)) &&& ~~~(lowMask bits width <<< (start % bits)))

def physicalClear (width start : Nat) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (physicalClearLow width start heap) (BitVec.ofNat bits (start / bits + 4 + 1))
    (heap (BitVec.ofNat bits (start / bits + 4 + 1)) &&& ~~~(lowMask bits width >>> (bits - start % bits)))

def physicalWrite (width start : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update
    (Function.update heap (BitVec.ofNat bits (start / bits + 4))
      (writeLow width (start % bits) value (heap (BitVec.ofNat bits (start / bits + 4)))))
    (BitVec.ofNat bits (start / bits + 4 + 1))
    (writeHigh width (start % bits) value (heap (BitVec.ofNat bits (start / bits + 4 + 1))))

def physicalFillLow (width start : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (physicalClear width start heap) (BitVec.ofNat bits (start / bits + 4))
    (writeLow width (start % bits) value (heap (BitVec.ofNat bits (start / bits + 4))))

theorem dataHeap_update (heap : BitVec bits → BitVec bits) (a : Nat) (value : BitVec bits) :
    dataHeap (Function.update heap (BitVec.ofNat bits (a + 4)) value) =
      Function.update (dataHeap heap) (BitVec.ofNat bits a) value := by
  funext word
  have heq : BitVec.ofNat bits (4 + word.toNat) = BitVec.ofNat bits (a + 4) ↔
      word = BitVec.ofNat bits a := by
    rw [Nat.add_comm a 4, ← BitVec.ofNat_add_ofNat, ← BitVec.ofNat_add_ofNat,
      BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact BitVec.add_right_inj (BitVec.ofNat bits 4)
  simp only [dataHeap, CompactControllerClaims.physicalHeaderWords, Function.update_apply, heq]

theorem dataHeap_physicalClearLow (width start : Nat) (heap : BitVec bits → BitVec bits) :
    dataHeap (physicalClearLow width start heap) = clearLowHeap width start (dataHeap heap) := by
  simp only [physicalClearLow, dataHeap_update, clearLowHeap, dataHeap_word, Nat.add_comm]

theorem dataHeap_physicalClear (width start : Nat) (heap : BitVec bits → BitVec bits) :
    dataHeap (physicalClear width start heap) = clearHeap width start (dataHeap heap) := by
  have haddr : start / bits + 4 + 1 = (start / bits + 1) + 4 := by omega
  simp only [physicalClear, haddr, dataHeap_update, dataHeap_physicalClearLow,
    clearHeap, dataHeap_word, Nat.add_comm]

theorem dataHeap_physicalWrite (width start : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) :
    dataHeap (physicalWrite width start value heap) = writeHeap width start value (dataHeap heap) := by
  have haddr : start / bits + 4 + 1 = (start / bits + 1) + 4 := by omega
  simp only [physicalWrite, haddr, dataHeap_update, writeHeap, dataHeap_word, Nat.add_comm]

theorem dataHeap_physicalFillLow (width start : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) :
    dataHeap (physicalFillLow width start value heap) = fillLowHeap width start value (dataHeap heap) := by
  simp only [physicalFillLow, dataHeap_update, dataHeap_physicalClear, fillLowHeap,
    dataHeap_word, Nat.add_comm]

theorem update_header (q physical : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hh : Header q heap) (hp : 4 ≤ physical) (hf : Fits bits physical) :
    Header q (Function.update heap (BitVec.ofNat bits physical) value) := by
  have hn (h : Nat) (hl : h < 4) : BitVec.ofNat bits h ≠ BitVec.ofNat bits physical :=
    (ofNat_injective_of_fit _ _ ((show h ≤ physical by omega).trans_lt hf) hf).not.mpr (by omega)
  constructor
  · rw [Function.update_of_ne (hn 0 (by decide))]; exact hh.width
  · rw [Function.update_of_ne (hn 1 (by decide))]; exact hh.mask
  · rw [Function.update_of_ne (hn 2 (by decide))]; exact hh.ones
  · rw [Function.update_of_ne (hn 3 (by decide))]; exact hh.wordBits

theorem physicalClear_header (q width start : Nat) (heap : BitVec bits → BitVec bits)
    (hh : Header q heap) (hf : Fits bits (start / bits + 4 + 1)) :
    Header q (physicalClear width start heap) := by
  unfold physicalClear physicalClearLow
  exact update_header q _ _ _ (update_header q _ _ _ hh (Nat.le_add_left 4 (start / bits))
    ((Nat.le_succ (start / bits + 4)).trans_lt hf))
    ((Nat.le_add_left 4 (start / bits)).trans (Nat.le_succ (start / bits + 4))) hf

theorem physicalWrite_header (q width start : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hh : Header q heap) (hf : Fits bits (start / bits + 4 + 1)) :
    Header q (physicalWrite width start value heap) := by
  unfold physicalWrite
  exact update_header q _ _ _ (update_header q _ _ _ hh (Nat.le_add_left 4 (start / bits))
    ((Nat.le_succ (start / bits + 4)).trans_lt hf))
    ((Nat.le_add_left 4 (start / bits)).trans (Nat.le_succ (start / bits + 4))) hf

theorem clear_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom clear state).register .address = state.register .address := rfl

theorem clear_value (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom clear state).register .value = state.register .value := rfl

theorem directWrite_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom directWrite state).register .address = state.register .address := rfl

theorem directWrite_value (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom directWrite state).register .value = state.register .value := rfl

theorem clear_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1)) :
    (executeOps rom clear state).heap =
      physicalClear (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q) state.heap := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hp : start / bits * bits < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hs
  have hr : start % bits < bits := Nat.mod_lt _ hbits
  have hrf : start % bits < 2 ^ bits := hr.trans hb
  have hsub : start - start / bits * bits = start % bits := by
    have h := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at h
    omega
  have hc : bits - start % bits < 2 ^ bits := (Nat.sub_le _ _).trans_lt hb
  have hn : Fits bits (start / bits + 4 + 1) := hphysical
  have hl : Fits bits (start / bits + 4) := (show start / bits + 4 ≤ start / bits + 4 + 1 by omega).trans_lt hn
  have hne : BitVec.ofNat bits (start / bits + 4 + 1) ≠ BitVec.ofNat bits (start / bits + 4) :=
    (ofNat_injective_of_fit _ _ hn hl).not.mpr (by omega)
  have hhead (h : Nat) (hhlt : h < 4) : BitVec.ofNat bits h ≠ BitVec.ofNat bits (start / bits + 4) :=
    (ofNat_injective_of_fit _ _
      ((hhlt.le.trans (Nat.le_add_left 4 (start / bits))).trans_lt hl) hl).not.mpr
      (Nat.ne_of_lt (hhlt.trans_le (Nat.le_add_left 4 (start / bits))))
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by have hpmax := Nat.two_pow_pos bits; omega
  simp +decide only [clear, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hh.width, hh.mask, hh.ones, hh.wordBits,
    arithmetic_and, arithmetic_shiftLeft, arithmetic_shiftRight,
    arithmetic_multiply, arithmetic_divide, complement_nat,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hmax,
    hne, hhead 1 (by decide), hhead 2 (by decide),
    physicalClear, physicalClearLow, lowMask]

theorem directWrite_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1)) :
    (executeOps rom directWrite state).heap =
      physicalWrite (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q) (state.register .value) state.heap := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hp : start / bits * bits < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hs
  have hr : start % bits < bits := Nat.mod_lt _ hbits
  have hrf : start % bits < 2 ^ bits := hr.trans hb
  have hsub : start - start / bits * bits = start % bits := by
    have h := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at h
    omega
  have hc : bits - start % bits < 2 ^ bits := (Nat.sub_le _ _).trans_lt hb
  have hn : Fits bits (start / bits + 4 + 1) := hphysical
  have hl : Fits bits (start / bits + 4) := (show start / bits + 4 ≤ start / bits + 4 + 1 by omega).trans_lt hn
  have hne : BitVec.ofNat bits (start / bits + 4 + 1) ≠ BitVec.ofNat bits (start / bits + 4) :=
    (ofNat_injective_of_fit _ _ hn hl).not.mpr (by omega)
  have hhead (h : Nat) (hhlt : h < 4) : BitVec.ofNat bits h ≠ BitVec.ofNat bits (start / bits + 4) :=
    (ofNat_injective_of_fit _ _
      ((hhlt.le.trans (Nat.le_add_left 4 (start / bits))).trans_lt hl) hl).not.mpr
      (Nat.ne_of_lt (hhlt.trans_le (Nat.le_add_left 4 (start / bits))))
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by have hpmax := Nat.two_pow_pos bits; omega
  simp +decide only [directWrite, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hh.width, hh.mask, hh.ones, hh.wordBits,
    arithmetic_and, arithmetic_or, arithmetic_shiftLeft, arithmetic_shiftRight,
    arithmetic_multiply, arithmetic_divide, complement_nat,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hmax,
    hne, hhead 1 (by decide), hhead 2 (by decide),
    physicalWrite, writeLow, writeHigh, lowMask]

theorem physicalWrite_clear (width start : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hf : Fits bits (start / bits + 4 + 1)) :
    physicalWrite width start value (physicalClear width start heap) = physicalWrite width start value heap := by
  have hl : Fits bits (start / bits + 4) := (show start / bits + 4 ≤ start / bits + 4 + 1 by omega).trans_lt hf
  have hne : BitVec.ofNat bits (start / bits + 4 + 1) ≠ BitVec.ofNat bits (start / bits + 4) :=
    (ofNat_injective_of_fit _ _ hf hl).not.mpr (by omega)
  funext word
  by_cases hh : word = BitVec.ofNat bits (start / bits + 4 + 1)
  · subst word
    simp [physicalWrite, physicalClear, physicalClearLow, writeHigh, BitVec.and_assoc]
  · by_cases hlo : word = BitVec.ofNat bits (start / bits + 4)
    · subst word
      simp only [physicalWrite, physicalClear, physicalClearLow,
        Function.update_of_ne hh, Function.update_self, writeLow, BitVec.and_assoc, BitVec.and_self]
    · simp [physicalWrite, physicalClear, physicalClearLow, hh, hlo]

theorem clear_header (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1)) :
    Header q (executeOps rom clear state).heap := by
  rw [clear_heap q rom state hh hbits hwidth hstart hphysical]
  exact physicalClear_header q _ _ state.heap hh hphysical

theorem safeWrite_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1)) :
    (executeOps rom safeWrite state).heap =
      physicalWrite (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q)
        (state.register .value) state.heap := by
  have hc := clear_header q rom state hh hbits hwidth hstart hphysical
  have hs : Fits bits (((executeOps rom clear state).register .address).toNat * CapacityBits.width q) := by
    rwa [clear_address]
  have hf : Fits bits (((executeOps rom clear state).register .address).toNat * CapacityBits.width q / bits + 4 + 1) := by
    rwa [clear_address]
  rw [safeWrite, executeOps_append, directWrite_heap q rom _ hc hbits hwidth hs hf,
    clear_address, clear_value, clear_heap q rom state hh hbits hwidth hstart hphysical,
    physicalWrite_clear _ _ _ _ hphysical]

theorem safeWrite_dataHeap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1)) :
    dataHeap (executeOps rom safeWrite state).heap =
      writeHeap (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q)
        (state.register .value) (dataHeap state.heap) := by
  rw [safeWrite_heap q rom state hh hbits hwidth hstart hphysical, dataHeap_physicalWrite]

theorem safeWrite_header (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1)) :
    Header q (executeOps rom safeWrite state).heap := by
  rw [safeWrite_heap q rom state hh hbits hwidth hstart hphysical]
  exact physicalWrite_header q _ _ _ state.heap hh hphysical

theorem safeWrite_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom safeWrite state).register .address = state.register .address := by
  rw [safeWrite, executeOps_append, directWrite_address, clear_address]

theorem safeWrite_value (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom safeWrite state).register .value = state.register .value := by
  rw [safeWrite, executeOps_append, directWrite_value, clear_value]

theorem safeWrite_straight : StraightProgram safeWrite := by
  simp [StraightProgram, safeWrite, clear, directWrite, StraightOp]

theorem safeWrite_code_fit (hbits : 7 ≤ bits) : WordsFit bits (packingCode safeWrite) := by
  have hpow : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  intro value hv
  simp [packingCode, safeWrite, clear, directWrite, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, haltWords] at hv
  simp only [Fits]
  omega

theorem safeWrite_pc_fit (hbits : 9 ≤ bits) : Fits bits (5 * safeWrite.length) := by
  have hpow : 2 ^ 9 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  simp only [Fits, safeWrite_length]
  omega

theorem safeWrite_run_body (rom : PhysicalROM) (state : WordState bits)
    (hbits : 9 ≤ bits) (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    packingRun rom safeWrite 66 state = executeOps rom safeWrite state := by
  rw [show 66 = safeWrite.length from rfl,
    packingRun_eq_executeOps_take rom safeWrite state safeWrite_straight (safeWrite_code_fit (by omega))
      (safeWrite_pc_fit hbits) hpc hactive _ le_rfl, List.take_length]

theorem safeWrite_run_halt (rom : PhysicalROM) (state : WordState bits)
    (hbits : 9 ≤ bits) (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    packingRun rom safeWrite 67 state = { executeOps rom safeWrite state with halted := true } := by
  exact packingRun_executeOps_halt rom safeWrite state safeWrite_straight (safeWrite_code_fit (by omega))
    (safeWrite_pc_fit hbits) hpc hactive

theorem safeWrite_dynamicTrace_length (rom : PhysicalROM) (state : WordState bits)
    (hbits : 9 ≤ bits) (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingDynamicTrace rom safeWrite 67 state).length = 684 := by
  rw [show 67 = safeWrite.length + 1 from rfl,
    packingDynamicTrace_eq_packingTrace rom safeWrite state safeWrite_straight (safeWrite_code_fit (by omega))
      (safeWrite_pc_fit hbits) hpc hactive, safeWrite_trace_length]

theorem clear_firstStore_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1)) :
    (executeOps rom (clear.take 19) state).heap =
      physicalClearLow (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q) state.heap := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hp : start / bits * bits < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hs
  have hr : start % bits < bits := Nat.mod_lt _ hbits
  have hrf : start % bits < 2 ^ bits := hr.trans hb
  have hsub : start - start / bits * bits = start % bits := by
    have h := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at h
    omega
  have hc : bits - start % bits < 2 ^ bits := (Nat.sub_le _ _).trans_lt hb
  have hn : Fits bits (start / bits + 4 + 1) := hphysical
  have hl : Fits bits (start / bits + 4) := (show start / bits + 4 ≤ start / bits + 4 + 1 by omega).trans_lt hn
  have hne : BitVec.ofNat bits (start / bits + 4 + 1) ≠ BitVec.ofNat bits (start / bits + 4) :=
    (ofNat_injective_of_fit _ _ hn hl).not.mpr (by omega)
  have hhead (h : Nat) (hhlt : h < 4) : BitVec.ofNat bits h ≠ BitVec.ofNat bits (start / bits + 4) :=
    (ofNat_injective_of_fit _ _
      ((hhlt.le.trans (Nat.le_add_left 4 (start / bits))).trans_lt hl) hl).not.mpr
      (Nat.ne_of_lt (hhlt.trans_le (Nat.le_add_left 4 (start / bits))))
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by have hpmax := Nat.two_pow_pos bits; omega
  simp +decide only [clear, List.take_succ_cons, List.take_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hh.width, hh.mask, hh.ones, hh.wordBits,
    arithmetic_and, arithmetic_shiftLeft,
    arithmetic_multiply, arithmetic_divide, complement_nat,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hmax,
    physicalClearLow, lowMask]

theorem directWrite_firstStore_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1)) :
    (executeOps rom (directWrite.take 21) state).heap =
      Function.update state.heap (BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits + 4))
        (writeLow (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q % bits)
          (state.register .value) (state.heap (BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits + 4)))) := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hp : start / bits * bits < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hs
  have hr : start % bits < bits := Nat.mod_lt _ hbits
  have hrf : start % bits < 2 ^ bits := hr.trans hb
  have hsub : start - start / bits * bits = start % bits := by
    have h := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at h
    omega
  have hc : bits - start % bits < 2 ^ bits := (Nat.sub_le _ _).trans_lt hb
  have hn : Fits bits (start / bits + 4 + 1) := hphysical
  have hl : Fits bits (start / bits + 4) := (show start / bits + 4 ≤ start / bits + 4 + 1 by omega).trans_lt hn
  have hne : BitVec.ofNat bits (start / bits + 4 + 1) ≠ BitVec.ofNat bits (start / bits + 4) :=
    (ofNat_injective_of_fit _ _ hn hl).not.mpr (by omega)
  have hhead (h : Nat) (hhlt : h < 4) : BitVec.ofNat bits h ≠ BitVec.ofNat bits (start / bits + 4) :=
    (ofNat_injective_of_fit _ _
      ((hhlt.le.trans (Nat.le_add_left 4 (start / bits))).trans_lt hl) hl).not.mpr
      (Nat.ne_of_lt (hhlt.trans_le (Nat.le_add_left 4 (start / bits))))
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by have hpmax := Nat.two_pow_pos bits; omega
  simp +decide only [directWrite, List.take_succ_cons, List.take_zero, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hh.width, hh.mask, hh.ones, hh.wordBits,
    arithmetic_and, arithmetic_or, arithmetic_shiftLeft,
    arithmetic_multiply, arithmetic_divide, complement_nat,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hmax,
    writeLow, lowMask]

theorem physicalClearLow_header (q width start : Nat) (heap : BitVec bits → BitVec bits)
    (hh : Header q heap) (hf : Fits bits (start / bits + 4 + 1)) :
    Header q (physicalClearLow width start heap) := by
  unfold physicalClearLow
  exact update_header q _ _ _ hh (Nat.le_add_left 4 (start / bits))
    ((Nat.le_succ (start / bits + 4)).trans_lt hf)

theorem physicalFillLow_header (q width start : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits)
    (hh : Header q heap) (hf : Fits bits (start / bits + 4 + 1)) :
    Header q (physicalFillLow width start value heap) := by
  unfold physicalFillLow
  exact update_header q _ _ _ (physicalClear_header q width start heap hh hf)
    (Nat.le_add_left 4 (start / bits)) ((Nat.le_succ (start / bits + 4)).trans_lt hf)

/-- These are the actual four stores, after 19/31/52/66 instructions.
All header loads and all arithmetic instructions between them are real
executed operations; only the heap projection is constant between stores. -/
theorem safeWrite_prefix_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (count : Nat) (hcount : count ≤ 66) :
    (executeOps rom (safeWrite.take count) state).heap =
      if count < 19 then state.heap
      else if count < 31 then physicalClearLow (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q) state.heap
      else if count < 52 then physicalClear (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q) state.heap
      else if count < 66 then physicalFillLow (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q) (state.register .value) state.heap
      else physicalWrite (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q) (state.register .value) state.heap := by
  by_cases h0 : count < 19
  · rw [ite_eq_left h0]
    rw [executeOps_prefix_heap_eq rom _ state 0 count 18 (by omega) (by omega) (by
      simp [safeWrite, clear, directWrite, HeapPreservingOp])]
    rfl
  · rw [ite_eq_right h0]
    by_cases h1 : count < 31
    · rw [ite_eq_left h1]
      rw [executeOps_prefix_heap_eq rom _ state 19 count 11 (by omega) (by omega) (by
        simp [safeWrite, clear, directWrite, HeapPreservingOp])]
      exact clear_firstStore_heap q rom state hh hbits hwidth hstart hphysical
    · rw [ite_eq_right h1]
      by_cases h2 : count < 52
      · rw [ite_eq_left h2]
        rw [executeOps_prefix_heap_eq rom _ state 31 count 20 (by omega) (by omega) (by
          simp [safeWrite, clear, directWrite, HeapPreservingOp])]
        exact clear_heap q rom state hh hbits hwidth hstart hphysical
      · rw [ite_eq_right h2]
        by_cases h3 : count < 66
        · rw [ite_eq_left h3]
          rw [executeOps_prefix_heap_eq rom _ state 52 count 13 (by omega) (by omega) (by
            simp [safeWrite, clear, directWrite, HeapPreservingOp])]
          change (executeOps rom (clear ++ directWrite.take 21) state).heap = _
          have hhdr := clear_header q rom state hh hbits hwidth hstart hphysical
          have hs : Fits bits (((executeOps rom clear state).register .address).toNat * CapacityBits.width q) := by
            rwa [clear_address]
          have hf : Fits bits (((executeOps rom clear state).register .address).toNat * CapacityBits.width q / bits + 4 + 1) := by
            rwa [clear_address]
          rw [executeOps_append, directWrite_firstStore_heap q rom _ hhdr hbits hwidth hs hf,
            clear_address, clear_value, clear_heap q rom state hh hbits hwidth hstart hphysical]
          have hl : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4) :=
            (show (state.register .address).toNat * CapacityBits.width q / bits + 4 ≤
              (state.register .address).toNat * CapacityBits.width q / bits + 4 + 1 by omega).trans_lt hphysical
          have hne : BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits + 4) ≠
              BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1) :=
            (ofNat_injective_of_fit _ _ hl hphysical).not.mpr (by omega)
          simp [physicalFillLow, physicalClear, physicalClearLow, writeLow, hne, BitVec.and_assoc]
        · rw [ite_eq_right h3]
          have heq : count = 66 := by omega
          subst count
          rw [show 66 = safeWrite.length from rfl, List.take_length]
          exact safeWrite_heap q rom state hh hbits hwidth hstart hphysical

theorem safeWrite_prefix_header (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (count : Nat) (hcount : count ≤ 66) :
    Header q (executeOps rom (safeWrite.take count) state).heap := by
  rw [safeWrite_prefix_heap q rom state hh hbits hwidth hstart hphysical count hcount]
  split_ifs
  · exact hh
  · exact physicalClearLow_header q _ _ _ hh hphysical
  · exact physicalClear_header q _ _ _ hh hphysical
  · exact physicalFillLow_header q _ _ _ _ hh hphysical
  · exact physicalWrite_header q _ _ _ _ hh hphysical

theorem safeWrite_prefix_capacityBounded (q capWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (haddress : (state.register .address).toNat < capWords) (hvalue : (state.register .value).toNat ≤ q)
    (hbounded : CapacityPrefixBounded q capWords (unpackHeap q capWords bits (dataHeap state.heap)))
    (count : Nat) (hcount : count ≤ 66) :
    CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (dataHeap (executeOps rom (safeWrite.take count) state).heap)) := by
  have hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1) :=
    (show (state.register .address).toNat * CapacityBits.width q / bits + 1 ≤
      (state.register .address).toNat * CapacityBits.width q / bits + 4 + 1 by omega).trans_lt hphysical
  let start := (state.register .address).toNat * CapacityBits.width q
  let value := state.register .value
  have hv : value.toNat < 2 ^ CapacityBits.width q := CapacityBits.value_lt_two_pow_width q _ hvalue
  have hn : Fits bits (start / bits + 1) := hnext
  have hfinal : CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (writeHeap (CapacityBits.width q) start value (dataHeap state.heap))) := by
    intro other ho
    by_cases heq : other = (state.register .address).toNat
    · subst other
      rw [unpackHeap_write_target q capWords _ _ (dataHeap state.heap) hbits hwidth haddress hnext hv]
      exact hvalue
    · rw [unpackHeap_write_other_capacity q capWords _ other _ (dataHeap state.heap) hbits hwidth hnext hregion hv ho heq]
      exact hbounded other ho
  have hclearLow : CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (clearLowHeap (CapacityBits.width q) start (dataHeap state.heap))) := by
    intro other ho
    exact (unpackHeap_mono_of_bits q capWords _ _ (clearLowHeap_bits_le _ _ _) other).trans (hbounded other ho)
  have hclear : CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (clearHeap (CapacityBits.width q) start (dataHeap state.heap))) := by
    intro other ho
    exact (unpackHeap_mono_of_bits q capWords _ _ (clearHeap_bits_le_clearLow _ _ _ hn) other).trans (hclearLow other ho)
  have hfill : CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (fillLowHeap (CapacityBits.width q) start value (dataHeap state.heap))) := by
    intro other ho
    exact (unpackHeap_mono_of_bits q capWords _ _ (fillLowHeap_bits_le_final _ _ _ _ hn) other).trans (hfinal other ho)
  rw [safeWrite_prefix_heap q rom state hh hbits hwidth hstart hphysical count hcount]
  split_ifs
  · exact hbounded
  · simpa only [dataHeap_physicalClearLow] using hclearLow
  · simpa only [dataHeap_physicalClear] using hclear
  · simpa only [dataHeap_physicalFillLow] using hfill
  · simpa only [dataHeap_physicalWrite] using hfinal

theorem safeWrite_prefix_frame (q capWords other : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (haddress : (state.register .address).toNat < capWords) (hvalue : (state.register .value).toNat ≤ q)
    (hwhere : (other < capWords ∧ other ≠ (state.register .address).toNat) ∨
      (capWords ≤ other ∧ Fits bits (packedCapacityWords q capWords bits + (other - capWords))))
    (count : Nat) (hcount : count ≤ 66) :
    unpackHeap q capWords bits (dataHeap (executeOps rom (safeWrite.take count) state).heap) other =
      unpackHeap q capWords bits (dataHeap state.heap) other := by
  have hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1) :=
    (show (state.register .address).toNat * CapacityBits.width q / bits + 1 ≤
      (state.register .address).toNat * CapacityBits.width q / bits + 4 + 1 by omega).trans_lt hphysical
  let start := (state.register .address).toNat * CapacityBits.width q
  let value := state.register .value
  have hv : value.toNat < 2 ^ CapacityBits.width q := CapacityBits.value_lt_two_pow_width q _ hvalue
  have hz : (BitVec.ofNat bits 0).toNat < 2 ^ CapacityBits.width q := by
    simpa only [BitVec.toNat_ofNat, Nat.zero_mod] using Nat.two_pow_pos (CapacityBits.width q)
  have hn : Fits bits (start / bits + 1) := hnext
  have hclear : unpackHeap q capWords bits (clearHeap (CapacityBits.width q) start (dataHeap state.heap)) other =
      unpackHeap q capWords bits (dataHeap state.heap) other := by
    rw [clearHeap_eq_write_zero]
    rcases hwhere with ⟨ho, hne⟩ | ⟨ho, hi⟩
    · exact unpackHeap_write_other_capacity q capWords _ other _ (dataHeap state.heap) hbits hwidth hnext hregion hz ho hne
    · exact unpackHeap_write_index q capWords _ other _ (dataHeap state.heap) hbits hwidth haddress ho hnext hi hz
  have hfinal : unpackHeap q capWords bits (writeHeap (CapacityBits.width q) start value (dataHeap state.heap)) other =
      unpackHeap q capWords bits (dataHeap state.heap) other := by
    rcases hwhere with ⟨ho, hne⟩ | ⟨ho, hi⟩
    · exact unpackHeap_write_other_capacity q capWords _ other _ (dataHeap state.heap) hbits hwidth hnext hregion hv ho hne
    · exact unpackHeap_write_index q capWords _ other _ (dataHeap state.heap) hbits hwidth haddress ho hnext hi hv
  have hclearLow : unpackHeap q capWords bits (clearLowHeap (CapacityBits.width q) start (dataHeap state.heap)) other =
      unpackHeap q capWords bits (dataHeap state.heap) other := by
    apply le_antisymm (unpackHeap_mono_of_bits q capWords _ _ (clearLowHeap_bits_le _ _ _) other)
    calc
      _ = unpackHeap q capWords bits (clearHeap (CapacityBits.width q) start (dataHeap state.heap)) other := hclear.symm
      _ ≤ _ := unpackHeap_mono_of_bits q capWords _ _ (clearHeap_bits_le_clearLow _ _ _ hn) other
  have hfill : unpackHeap q capWords bits (fillLowHeap (CapacityBits.width q) start value (dataHeap state.heap)) other =
      unpackHeap q capWords bits (dataHeap state.heap) other := by
    apply le_antisymm
    · exact (unpackHeap_mono_of_bits q capWords _ _ (fillLowHeap_bits_le_final _ _ _ _ hn) other).trans hfinal.le
    · exact hclear.symm.le.trans (unpackHeap_mono_of_bits q capWords _ _ (clearHeap_bits_le_fillLow _ _ _ _ hn) other)
  rw [safeWrite_prefix_heap q rom state hh hbits hwidth hstart hphysical count hcount]
  split_ifs
  · rfl
  · simpa only [dataHeap_physicalClearLow] using hclearLow
  · simpa only [dataHeap_physicalClear] using hclear
  · simpa only [dataHeap_physicalFillLow] using hfill
  · simpa only [dataHeap_physicalWrite] using hfinal

/-- Local actual access proof before fetched-code composition. Every
header load, low/high load, and store is included in this finite body. -/
theorem clear_accessFits_executeOps (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (hlookahead : (state.register .address).toNat * CapacityBits.width q / bits + 4 + 1 < heapWords)
    (count : Nat) (hcount : count < clear.length) :
    packingAccessFits rom heapWords (executeOps rom (clear.take count) state) clear[count] := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hn : start / bits + 4 + 1 < 2 ^ bits := hphysical
  have hl : start / bits + 4 + 1 < heapWords := hlookahead
  have hlo : start / bits + 4 < 2 ^ bits := by omega
  have hpow : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  have hone : 1 < 2 ^ bits := by omega
  have htwo : 2 < 2 ^ bits := by omega
  have hthree : 3 < 2 ^ bits := by omega
  have hheader_bound : 4 < heapWords :=
    (Nat.lt_succ_of_le (Nat.le_add_left 4 (start / bits))).trans hl
  have hcount' : count ≤ 30 := by rw [clear_length] at hcount; omega
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [clear, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingAccessFits, AccessFits,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    hh.width, hh.wordBits, arithmetic_multiply, arithmetic_divide,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt htwo, Nat.mod_eq_of_lt hthree,
    Nat.zero_mod]
  all_goals omega

/-- Local actual access proof before fetched-code composition. Every
header load, low/high load, and store is included in this finite body. -/
theorem directWrite_accessFits_executeOps (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (hlookahead : (state.register .address).toNat * CapacityBits.width q / bits + 4 + 1 < heapWords)
    (count : Nat) (hcount : count < directWrite.length) :
    packingAccessFits rom heapWords (executeOps rom (directWrite.take count) state) directWrite[count] := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hn : start / bits + 4 + 1 < 2 ^ bits := hphysical
  have hl : start / bits + 4 + 1 < heapWords := hlookahead
  have hlo : start / bits + 4 < 2 ^ bits := by omega
  have hpow : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  have hone : 1 < 2 ^ bits := by omega
  have htwo : 2 < 2 ^ bits := by omega
  have hthree : 3 < 2 ^ bits := by omega
  have hheader_bound : 4 < heapWords :=
    (Nat.lt_succ_of_le (Nat.le_add_left 4 (start / bits))).trans hl
  have hcount' : count ≤ 34 := by rw [directWrite_length] at hcount; omega
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [directWrite, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingAccessFits, AccessFits,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    hh.width, hh.wordBits, arithmetic_multiply, arithmetic_divide,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hn,
    Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt htwo, Nat.mod_eq_of_lt hthree,
    Nat.zero_mod]
  all_goals omega

/-- Actual fetched 66-op memory safety. Only internal header correctness
and concrete width/address/allocation facts are inputs; no preprocessor,
execution correctness, runtime cost or control-bank result is assumed. -/
theorem safeWrite_accessFits (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 9 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (hlookahead : (state.register .address).toNat * CapacityBits.width q / bits + 4 + 1 < heapWords)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hcount : count < safeWrite.length) :
    packingAccessFits rom heapWords (packingRun rom safeWrite count state) safeWrite[count] := by
  rw [packingRun_eq_executeOps_take rom safeWrite state safeWrite_straight (safeWrite_code_fit (by omega))
    (safeWrite_pc_fit hbits) hpc hactive count hcount.le]
  simp only [safeWrite] at hcount ⊢
  by_cases hc : count < clear.length
  · rw [List.take_append_of_le_length hc.le, List.getElem_append_left hc]
    exact clear_accessFits_executeOps q heapWords rom state hh (by omega) hwidth hstart hphysical hlookahead count hc
  · have hc' : clear.length ≤ count := by omega
    rw [List.take_append, List.take_of_length_le hc', executeOps_append, List.getElem_append_right hc']
    have hhdr := clear_header q rom state hh (by omega) hwidth hstart hphysical
    have hs : Fits bits (((executeOps rom clear state).register .address).toNat * CapacityBits.width q) := by
      rwa [clear_address]
    have hf : Fits bits (((executeOps rom clear state).register .address).toNat * CapacityBits.width q / bits + 4 + 1) := by
      rwa [clear_address]
    have hl : ((executeOps rom clear state).register .address).toNat * CapacityBits.width q / bits + 4 + 1 < heapWords := by
      rwa [clear_address]
    exact directWrite_accessFits_executeOps q heapWords rom _ hhdr (by omega) hwidth hs hf hl
      (count - clear.length) (by rw [List.length_append] at hcount; omega)

theorem safeWrite_run_prefix_header (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 9 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hc : count ≤ 66) :
    Header q (packingRun rom safeWrite count state).heap := by
  rw [packingRun_eq_executeOps_take rom safeWrite state safeWrite_straight (safeWrite_code_fit (by omega))
    (safeWrite_pc_fit hbits) hpc hactive count (by rwa [safeWrite_length])]
  exact safeWrite_prefix_header q rom state hh (by omega) hwidth hstart hphysical count hc

theorem safeWrite_run_prefix_capacityBounded (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 9 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (hregion : Fits bits (C * CapacityBits.width q))
    (haddress : (state.register .address).toNat < C) (hvalue : (state.register .value).toNat ≤ q)
    (hbounded : CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap state.heap)))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hc : count ≤ 66) :
    CapacityPrefixBounded q C (unpackHeap q C bits (dataHeap (packingRun rom safeWrite count state).heap)) := by
  rw [packingRun_eq_executeOps_take rom safeWrite state safeWrite_straight (safeWrite_code_fit (by omega))
    (safeWrite_pc_fit hbits) hpc hactive count (by rwa [safeWrite_length])]
  exact safeWrite_prefix_capacityBounded q C rom state hh (by omega) hwidth hstart hphysical
    hregion haddress hvalue hbounded count hc

theorem safeWrite_run_prefix_frame (q C other : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 9 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (hregion : Fits bits (C * CapacityBits.width q))
    (haddress : (state.register .address).toNat < C) (hvalue : (state.register .value).toNat ≤ q)
    (hwhere : (other < C ∧ other ≠ (state.register .address).toNat) ∨
      (C ≤ other ∧ Fits bits (packedCapacityWords q C bits + (other - C))))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hc : count ≤ 66) :
    unpackHeap q C bits (dataHeap (packingRun rom safeWrite count state).heap) other =
      unpackHeap q C bits (dataHeap state.heap) other := by
  rw [packingRun_eq_executeOps_take rom safeWrite state safeWrite_straight (safeWrite_code_fit (by omega))
    (safeWrite_pc_fit hbits) hpc hactive count (by rwa [safeWrite_length])]
  exact safeWrite_prefix_frame q C other rom state hh (by omega) hwidth hstart hphysical
    hregion haddress hvalue hwhere count hc

theorem safeWrite_run_target (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 9 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 4 + 1))
    (haddress : (state.register .address).toNat < C) (hvalue : (state.register .value).toNat ≤ q)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    unpackHeap q C bits (dataHeap (packingRun rom safeWrite 66 state).heap)
      (state.register .address).toNat = (state.register .value).toNat := by
  rw [safeWrite_run_body rom state hbits hpc hactive,
    safeWrite_dataHeap q rom state hh (by omega) hwidth hstart hphysical]
  exact unpackHeap_write_target q C _ _ (dataHeap state.heap) (by omega) hwidth haddress
    ((show (state.register .address).toNat * CapacityBits.width q / bits + 1 ≤
      (state.register .address).toNat * CapacityBits.width q / bits + 4 + 1 by omega).trans_lt hphysical)
    (CapacityBits.value_lt_two_pow_width q _ hvalue)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimePacked016
