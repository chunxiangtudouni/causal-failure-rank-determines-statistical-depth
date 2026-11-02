module

public import PaperProofs.Structure.AlgorithmClaims
public import PaperProofs.Structure.PackingMachine
public import PaperProofs.Structure.PackingExecutionCost
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.IntervalCases

/-! Constant-length packed scalar access using the existing physical ISA.
The scalar may straddle two words. The second word is an ordinary load,
so a caller must reserve the usual one-word lookahead padding. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.AlgorithmClaims.PackedCapacityRAM

open IndexedRAM IndexedClosureRAM PackingMachine

variable {bits : Nat}

def lowMask (bits width : Nat) : BitVec bits := BitVec.ofNat bits (2 ^ width - 1)

theorem lowMask_eq_setWidth (bits width : Nat) :
    lowMask bits width = (BitVec.allOnes width).setWidth bits := by
  rw [lowMask, ← BitVec.toNat_allOnes, BitVec.ofNat_toNat]

theorem getLsbD_lowMask (bits width i : Nat) :
    (lowMask bits width).getLsbD i = (decide (i < bits) && decide (i < width)) := by
  rw [lowMask_eq_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]

def readTwoWords (width shift : Nat) (low high : BitVec bits) : BitVec bits :=
  ((low >>> shift) ||| (high <<< (bits - shift))) &&& lowMask bits width

theorem getLsbD_readTwoWords (width shift : Nat) (low high : BitVec bits)
    (hwidth : width ≤ bits) (hshift : shift < bits) (i : Nat) (hi : i < width) :
    (readTwoWords width shift low high).getLsbD i =
      if shift + i < bits then low.getLsbD (shift + i)
      else high.getLsbD (shift + i - bits) := by
  have hib : i < bits := hi.trans_le hwidth
  simp only [readTwoWords, BitVec.getLsbD_and, BitVec.getLsbD_or,
    BitVec.getLsbD_ushiftRight, BitVec.getLsbD_shiftLeft, getLsbD_lowMask,
    hib, hi, decide_true, Bool.true_and, Bool.and_true]
  by_cases hlow : shift + i < bits
  · have hleft : i < bits - shift := by omega
    simp only [hlow, hleft, decide_true, Bool.not_true, Bool.false_and, Bool.or_false, ite_true]
  · have hleft : ¬ i < bits - shift := by omega
    have hzero : low.getLsbD (shift + i) = false := BitVec.getLsbD_of_ge _ _ (by omega)
    have heq : i - (bits - shift) = shift + i - bits := by omega
    simp only [hlow, hleft, decide_false, Bool.not_false, Bool.true_and, hzero,
      Bool.false_or, ite_false, heq]

theorem getLsbD_readTwoWords_above (width shift : Nat) (low high : BitVec bits)
    (i : Nat) (hi : width ≤ i) : (readTwoWords width shift low high).getLsbD i = false := by
  simp only [readTwoWords, BitVec.getLsbD_and, getLsbD_lowMask,
    show ¬ i < width by omega, decide_false, Bool.and_false]

theorem offset_div_mod_low (start i : Nat) (hbits : 0 < bits)
    (hlow : start % bits + i < bits) :
    (start + i) / bits = start / bits ∧ (start + i) % bits = start % bits + i := by
  have heq : start + i = (start % bits + i) + (start / bits) * bits := by
    have h := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at h
    omega
  rw [heq, Nat.add_mul_div_right _ _ hbits, Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt hlow, Nat.mod_eq_of_lt hlow, Nat.zero_add]
  exact ⟨rfl, rfl⟩

theorem offset_div_mod_high (start i : Nat) (hbits : 0 < bits)
    (hi : i < bits) (hhigh : bits ≤ start % bits + i) :
    (start + i) / bits = start / bits + 1 ∧
      (start + i) % bits = start % bits + i - bits := by
  have hr := Nat.mod_lt start hbits
  have hrest : start % bits + i - bits < bits := by omega
  have heq : start + i = (start % bits + i - bits) + (start / bits + 1) * bits := by
    have h := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at h
    rw [Nat.add_mul, Nat.one_mul]
    omega
  rw [heq, Nat.add_mul_div_right _ _ hbits, Nat.add_mul_mod_self_right,
    Nat.div_eq_of_lt hrest, Nat.mod_eq_of_lt hrest, Nat.zero_add]
  exact ⟨rfl, rfl⟩

theorem readTwoWords_eq_decode (width start : Nat) (heap : BitVec bits → BitVec bits)
    (hbits : 0 < bits) (hwidth : width ≤ bits) :
    (readTwoWords width (start % bits)
      (heap (BitVec.ofNat bits (start / bits)))
      (heap (BitVec.ofNat bits (start / bits + 1)))).toNat =
      CapacityBits.decodeScalar (List.ofFn (fun position : Fin width =>
        (heap (BitVec.ofNat bits ((start + position.val) / bits))).getLsbD
          ((start + position.val) % bits))) := by
  let stream := List.ofFn (fun position : Fin width =>
    (heap (BitVec.ofNat bits ((start + position.val) / bits))).getLsbD ((start + position.val) % bits))
  have hlen : stream.length = width := List.length_ofFn
  have heq : readTwoWords width (start % bits)
      (heap (BitVec.ofNat bits (start / bits)))
      (heap (BitVec.ofNat bits (start / bits + 1))) =
      (BitVec.ofBoolListLE stream).setWidth bits := by
    apply BitVec.eq_of_getLsbD_eq
    intro i hib
    simp only [BitVec.getLsbD_setWidth, hib, decide_true, Bool.true_and, BitVec.getLsbD_ofBoolListLE]
    by_cases hi : i < width
    · rw [getLsbD_readTwoWords width (start % bits) _ _ hwidth (Nat.mod_lt start hbits) i hi,
        List.getD_eq_getElem _ false (hlen.symm ▸ hi)]
      simp only [stream, List.getElem_ofFn]
      by_cases hlow : start % bits + i < bits
      · rw [ite_eq_left hlow, (offset_div_mod_low start i hbits hlow).1,
          (offset_div_mod_low start i hbits hlow).2]
      · rw [ite_eq_right hlow, (offset_div_mod_high start i hbits (hi.trans_le hwidth) (by omega)).1,
          (offset_div_mod_high start i hbits (hi.trans_le hwidth) (by omega)).2]
    · rw [getLsbD_readTwoWords_above _ _ _ _ i (by omega), List.getD_eq_default _ false (by omega)]
  rw [heq, BitVec.toNat_setWidth_of_le (hlen.trans_le hwidth)]
  rfl

theorem readTwoWords_eq_unpackHeap (q capWords address : Nat) (heap : BitVec bits → BitVec bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits) (haddress : address < capWords) :
    (readTwoWords (CapacityBits.width q) (address * CapacityBits.width q % bits)
      (heap (BitVec.ofNat bits (address * CapacityBits.width q / bits)))
      (heap (BitVec.ofNat bits (address * CapacityBits.width q / bits + 1)))).toNat =
      unpackHeap q capWords bits heap address := by
  rw [unpackHeap, ite_eq_left haddress]
  exact readTwoWords_eq_decode _ _ heap hbits hwidth

def readProgram (q bits : Nat) : List PackingOp :=
  [.base (.base (.constant .total (CapacityBits.width q))),
   .arithmetic .multiply .old .address .total,
   .base (.base (.constant .total bits)),
   .arithmetic .divide .index .old .total,
   .arithmetic .multiply .fresh .index .total,
   .base (.subtract .old .old .fresh),
   .base (.base (.loadHeap .value .index)),
   .arithmetic .shiftRight .value .value .old,
   .base (.base (.constant .fresh 1)),
   .base (.base (.add .index .index .fresh)),
   .base (.base (.loadHeap .fresh .index)),
   .base (.subtract .old .total .old),
   .arithmetic .shiftLeft .fresh .fresh .old,
   .arithmetic .bitOr .value .value .fresh,
   .base (.base (.constant .total (2 ^ CapacityBits.width q - 1))),
   .arithmetic .bitAnd .value .value .total]

theorem readProgram_length (q bits : Nat) : (readProgram q bits).length = 16 := rfl

set_option maxRecDepth 4000 in
theorem readProgram_trace_length (q bits : Nat) : (packingTrace (readProgram q bits)).length = 170 := rfl

theorem arithmetic_and (left right : BitVec bits) :
    packingArithmetic .bitAnd left right = left &&& right := by
  simp only [packingArithmetic, Nat.land_eq, BitVec.ofNat_and, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem arithmetic_or (left right : BitVec bits) :
    packingArithmetic .bitOr left right = left ||| right := by
  simp only [packingArithmetic, Nat.lor_eq, BitVec.ofNat_or, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem arithmetic_shiftLeft (left right : BitVec bits) :
    packingArithmetic .shiftLeft left right = left <<< right.toNat := rfl

theorem arithmetic_shiftRight (left right : BitVec bits) :
    packingArithmetic .shiftRight left right = left >>> right.toNat := by
  change BitVec.ofNat bits (left.toNat >>> right.toNat) = _
  rw [← BitVec.toNat_ushiftRight, BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem arithmetic_multiply (left right : BitVec bits) :
    packingArithmetic .multiply left right = BitVec.ofNat bits (left.toNat * right.toNat) := rfl

theorem arithmetic_divide (left right : BitVec bits) :
    packingArithmetic .divide left right = BitVec.ofNat bits (left.toNat / right.toNat) := rfl

set_option maxRecDepth 4000 in
theorem readProgram_value (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q)) :
    (executeOps rom (readProgram q bits) state).register .value =
      readTwoWords (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q % bits)
        (state.heap (BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits)))
        (state.heap (BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))) := by
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
  simp +decide only [readProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte,
    arithmetic_and, arithmetic_or, arithmetic_shiftLeft, arithmetic_shiftRight,
    arithmetic_multiply, arithmetic_divide,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hc,
    readTwoWords, lowMask]

theorem readProgram_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (readProgram q bits) state).heap = state.heap := rfl

theorem readProgram_straight (q bits : Nat) : StraightProgram (readProgram q bits) := by
  simp [StraightProgram, readProgram, StraightOp]

set_option maxRecDepth 4000 in
theorem readProgram_code_fit (q : Nat) (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits) :
    WordsFit bits (packingCode (readProgram q bits)) := by
  have hsmall : 80 < 2 ^ bits := by
    have hpow : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
    omega
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hm : 2 ^ CapacityBits.width q - 1 < 2 ^ bits := by
    have hp : 2 ^ CapacityBits.width q ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hwidth
    have hpositive : 0 < 2 ^ CapacityBits.width q := Nat.two_pow_pos _
    omega
  intro value hvalue
  simp [packingCode, readProgram, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, haltWords] at hvalue
  simp only [Fits]
  omega

theorem readProgram_pc_fit (q : Nat) (hbits : 7 ≤ bits) : Fits bits (5 * (readProgram q bits).length) := by
  have hpow : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  simp only [Fits, readProgram_length]
  omega

theorem readProgram_run_value (q capWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (haddress : (state.register .address).toNat < capWords)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    ((packingRun rom (readProgram q bits) 16 state).register .value).toNat =
      unpackHeap q capWords bits state.heap (state.register .address).toNat := by
  rw [show 16 = (readProgram q bits).length from rfl,
    packingRun_eq_executeOps_take rom _ state (readProgram_straight q bits)
      (readProgram_code_fit q hbits hwidth) (readProgram_pc_fit q hbits) hpc hactive _ le_rfl,
    List.take_length, readProgram_value q rom state (by omega) hwidth hstart]
  exact readTwoWords_eq_unpackHeap q capWords _ state.heap (by omega) hwidth haddress

theorem readProgram_run_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingRun rom (readProgram q bits) 16 state).heap = state.heap := by
  rw [show 16 = (readProgram q bits).length from rfl,
    packingRun_eq_executeOps_take rom _ state (readProgram_straight q bits)
      (readProgram_code_fit q hbits hwidth) (readProgram_pc_fit q hbits) hpc hactive _ le_rfl,
    List.take_length, readProgram_heap]

theorem readProgram_halts (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingRun rom (readProgram q bits) 17 state).halted = true := by
  rw [show 17 = (readProgram q bits).length + 1 from rfl,
    packingRun_executeOps_halt rom _ state (readProgram_straight q bits)
      (readProgram_code_fit q hbits hwidth) (readProgram_pc_fit q hbits) hpc hactive]

theorem readProgram_dynamicTrace_length (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingDynamicTrace rom (readProgram q bits) 17 state).length = 170 := by
  rw [show 17 = (readProgram q bits).length + 1 from rfl,
    packingDynamicTrace_eq_packingTrace rom _ state (readProgram_straight q bits)
      (readProgram_code_fit q hbits hwidth) (readProgram_pc_fit q hbits) hpc hactive,
    readProgram_trace_length]

theorem getLsbD_of_value_bound (value : BitVec bits) (width i : Nat)
    (hvalue : value.toNat < 2 ^ width) (hi : width ≤ i) : value.getLsbD i = false := by
  exact Nat.testBit_lt_two_pow (hvalue.trans_le (Nat.pow_le_pow_right (by decide) hi))

def writeLow (width shift : Nat) (value low : BitVec bits) : BitVec bits :=
  (low &&& ~~~(lowMask bits width <<< shift)) ||| (value <<< shift)

def writeHigh (width shift : Nat) (value high : BitVec bits) : BitVec bits :=
  (high &&& ~~~(lowMask bits width >>> (bits - shift))) ||| (value >>> (bits - shift))

theorem getLsbD_writeLow (width shift : Nat) (value low : BitVec bits)
    (hvalue : value.toNat < 2 ^ width) (i : Nat) (hi : i < bits) :
    (writeLow width shift value low).getLsbD i =
      if shift ≤ i ∧ i - shift < width then value.getLsbD (i - shift) else low.getLsbD i := by
  simp only [writeLow, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_shiftLeft, getLsbD_lowMask, hi, decide_true, Bool.true_and]
  by_cases hs : shift ≤ i
  · have hs' : ¬ i < shift := by omega
    have hib : i - shift < bits := (Nat.sub_le _ _).trans_lt hi
    by_cases hin : i - shift < width
    · simp only [hs, hin, and_self, ite_true, hs', decide_false, Bool.not_false,
        Bool.true_and, hib, decide_true, Bool.and_self, Bool.not_true, Bool.and_false, Bool.false_or]
    · simp only [hs, hin, and_false, ite_false, hs', decide_false, Bool.not_false,
        hib, decide_true, Bool.and_false, Bool.not_false, Bool.and_true,
        getLsbD_of_value_bound value width (i - shift) hvalue (by omega), Bool.or_false]
  · have hs' : i < shift := by omega
    simp only [hs, false_and, ite_false, hs', decide_true, Bool.not_true,
      Bool.false_and, Bool.not_false, Bool.and_true, Bool.or_false]

theorem getLsbD_writeHigh (width shift : Nat) (value high : BitVec bits)
    (hwidth : width ≤ bits) (hvalue : value.toNat < 2 ^ width) (i : Nat) (hi : i < bits) :
    (writeHigh width shift value high).getLsbD i =
      if bits - shift + i < width then value.getLsbD (bits - shift + i) else high.getLsbD i := by
  simp only [writeHigh, BitVec.getLsbD_or, BitVec.getLsbD_and, BitVec.getLsbD_not,
    BitVec.getLsbD_ushiftRight, getLsbD_lowMask, hi, decide_true, Bool.true_and]
  by_cases hin : bits - shift + i < width
  · have hib : bits - shift + i < bits := hin.trans_le hwidth
    simp only [hin, hib, decide_true, Bool.and_self, Bool.not_true, Bool.and_false, Bool.false_or, ite_true]
  · simp only [hin, decide_false, Bool.and_false, Bool.not_false, Bool.and_true,
      getLsbD_of_value_bound value width (bits - shift + i) hvalue (by omega), Bool.or_false, ite_false]

def writeHeap (width start : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) :
    BitVec bits → BitVec bits :=
  Function.update
    (Function.update heap (BitVec.ofNat bits (start / bits))
      (writeLow width (start % bits) value (heap (BitVec.ofNat bits (start / bits)))))
    (BitVec.ofNat bits (start / bits + 1))
    (writeHigh width (start % bits) value (heap (BitVec.ofNat bits (start / bits + 1))))

theorem ofNat_injective_of_fit (a b : Nat) (ha : Fits bits a) (hb : Fits bits b) :
    BitVec.ofNat bits a = BitVec.ofNat bits b ↔ a = b := by
  constructor
  · intro h
    have hn := congrArg BitVec.toNat h
    simpa only [BitVec.toNat_ofNat, Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb] using hn
  · rintro rfl
    rfl

theorem writeHeap_target_bit (width start : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits) (hwidth : width ≤ bits)
    (hnext : Fits bits (start / bits + 1)) (hvalue : value.toNat < 2 ^ width)
    (i : Nat) (hi : i < width) :
    (writeHeap width start value heap (BitVec.ofNat bits ((start + i) / bits))).getLsbD
      ((start + i) % bits) = value.getLsbD i := by
  have hr := Nat.mod_lt start hbits
  have hbase : Fits bits (start / bits) := (Nat.lt_succ_self _).trans hnext
  have hne : BitVec.ofNat bits (start / bits) ≠ BitVec.ofNat bits (start / bits + 1) := by
    exact (ofNat_injective_of_fit (bits := bits) _ _ hbase hnext).not.mpr (by omega)
  by_cases hlow : start % bits + i < bits
  · obtain ⟨hd, hm⟩ := offset_div_mod_low start i hbits hlow
    rw [hd, hm]
    simp only [writeHeap, Function.update_apply, hne, ite_false, ite_true]
    rw [getLsbD_writeLow _ _ _ _ hvalue _ hlow]
    have hsub : start % bits + i - start % bits = i := by omega
    simp only [show start % bits ≤ start % bits + i by omega, hsub, hi, and_self, ite_true]
  · obtain ⟨hd, hm⟩ := offset_div_mod_high start i hbits (hi.trans_le hwidth) (by omega)
    rw [hd, hm]
    simp only [writeHeap, Function.update_self]
    rw [getLsbD_writeHigh _ _ _ _ hwidth hvalue _ (by omega)]
    have heq : bits - start % bits + (start % bits + i - bits) = i := by omega
    simp only [heq, hi, ite_true]

theorem unpackHeap_write_target (q capWords address : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (haddress : address < capWords) (hnext : Fits bits (address * CapacityBits.width q / bits + 1))
    (hvalue : value.toNat < 2 ^ CapacityBits.width q) :
    unpackHeap q capWords bits (writeHeap (CapacityBits.width q) (address * CapacityBits.width q) value heap)
      address = value.toNat := by
  rw [unpackHeap, ite_eq_left haddress]
  have heq : (List.ofFn (fun position : Fin (CapacityBits.width q) =>
      (writeHeap (CapacityBits.width q) (address * CapacityBits.width q) value heap
        (BitVec.ofNat bits ((address * CapacityBits.width q + position.val) / bits))).getLsbD
        ((address * CapacityBits.width q + position.val) % bits))) =
      CapacityBits.encodeScalar (CapacityBits.width q) value.toNat := by
    apply congrArg List.ofFn
    funext position
    rw [writeHeap_target_bit _ _ _ _ hbits hwidth hnext hvalue _ position.isLt]
    simp only [BitVec.ofNat_toNat, BitVec.getLsbD_setWidth,
      position.isLt, decide_true, Bool.true_and]
  rw [heq, CapacityBits.decodeScalar_encodeScalar, Nat.mod_eq_of_lt hvalue]

theorem writeHeap_external_bit (width start offset : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits) (hwidth : width ≤ bits)
    (hnext : Fits bits (start / bits + 1)) (hword : Fits bits (offset / bits))
    (hvalue : value.toNat < 2 ^ width) (houtside : offset < start ∨ start + width ≤ offset) :
    (writeHeap width start value heap (BitVec.ofNat bits (offset / bits))).getLsbD (offset % bits) =
      (heap (BitVec.ofNat bits (offset / bits))).getLsbD (offset % bits) := by
  have hbase : Fits bits (start / bits) := (Nat.lt_succ_self _).trans hnext
  have hne : BitVec.ofNat bits (start / bits) ≠ BitVec.ofNat bits (start / bits + 1) :=
    (ofNat_injective_of_fit (bits := bits) _ _ hbase hnext).not.mpr (by omega)
  have hs := Nat.div_add_mod start bits
  have ho := Nat.div_add_mod offset bits
  have hr := Nat.mod_lt start hbits
  have hi := Nat.mod_lt offset hbits
  by_cases hl : offset / bits = start / bits
  · have hnot : ¬(start % bits ≤ offset % bits ∧ offset % bits - start % bits < width) := by
      rw [hl] at ho
      omega
    rw [hl]
    simp only [writeHeap, Function.update_apply, hne, ite_false, ite_true]
    rw [getLsbD_writeLow _ _ _ _ hvalue _ hi, ite_eq_right hnot]
  · by_cases hh : offset / bits = start / bits + 1
    · have hnot : ¬ bits - start % bits + offset % bits < width := by
        rw [hh, Nat.mul_add, Nat.mul_one] at ho
        omega
      rw [hh]
      simp only [writeHeap, Function.update_self]
      rw [getLsbD_writeHigh _ _ _ _ hwidth hvalue _ hi, ite_eq_right hnot]
    · have hln : BitVec.ofNat bits (offset / bits) ≠ BitVec.ofNat bits (start / bits) :=
        (ofNat_injective_of_fit (bits := bits) _ _ hword hbase).not.mpr hl
      have hhn : BitVec.ofNat bits (offset / bits) ≠ BitVec.ofNat bits (start / bits + 1) :=
        (ofNat_injective_of_fit (bits := bits) _ _ hword hnext).not.mpr hh
      simp only [writeHeap, Function.update_apply, hln, hhn, ite_false]

theorem unpackHeap_write_other_capacity (q capWords address other : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hnext : Fits bits (address * CapacityBits.width q / bits + 1))
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (hvalue : value.toNat < 2 ^ CapacityBits.width q)
    (hother : other < capWords) (hne : other ≠ address) :
    unpackHeap q capWords bits (writeHeap (CapacityBits.width q) (address * CapacityBits.width q) value heap)
      other = unpackHeap q capWords bits heap other := by
  rw [unpackHeap, unpackHeap, ite_eq_left hother, ite_eq_left hother]
  apply congrArg CapacityBits.decodeScalar
  apply congrArg List.ofFn
  funext position
  have hmul : (other + 1) * CapacityBits.width q ≤ capWords * CapacityBits.width q :=
    Nat.mul_le_mul_right _ (by omega)
  have hoffset : other * CapacityBits.width q + position.val < capWords * CapacityBits.width q := by
    rw [Nat.add_mul, Nat.one_mul] at hmul
    omega
  have hword : Fits bits ((other * CapacityBits.width q + position.val) / bits) :=
    (Nat.div_le_self _ _).trans_lt (hoffset.trans hregion)
  apply writeHeap_external_bit _ _ _ _ _ hbits hwidth hnext hword hvalue
  rcases Nat.lt_or_gt_of_ne hne with hlt | hgt
  · left
    have hm : (other + 1) * CapacityBits.width q ≤ address * CapacityBits.width q :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega
  · right
    have hm : (address + 1) * CapacityBits.width q ≤ other * CapacityBits.width q :=
      Nat.mul_le_mul_right _ (by omega)
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega

theorem packedCapacityWords_mul_bits (q capWords : Nat) (hbits : 0 < bits) :
    capWords * CapacityBits.width q ≤ packedCapacityWords q capWords bits * bits := by
  have hd := Nat.div_add_mod (capWords * CapacityBits.width q + bits - 1) bits
  have hm := Nat.mod_lt (capWords * CapacityBits.width q + bits - 1) hbits
  rw [Nat.mul_comm bits] at hd
  simp only [packedCapacityWords]
  omega

theorem unpackHeap_write_index (q capWords address other : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (haddress : address < capWords) (hother : capWords ≤ other)
    (hnext : Fits bits (address * CapacityBits.width q / bits + 1))
    (hindex : Fits bits (packedCapacityWords q capWords bits + (other - capWords)))
    (hvalue : value.toNat < 2 ^ CapacityBits.width q) :
    unpackHeap q capWords bits (writeHeap (CapacityBits.width q) (address * CapacityBits.width q) value heap)
      other = unpackHeap q capWords bits heap other := by
  rw [unpackHeap, unpackHeap, ite_eq_right (not_lt_of_ge hother), ite_eq_right (not_lt_of_ge hother)]
  apply congrArg BitVec.toNat
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  let word := packedCapacityWords q capWords bits + (other - capWords)
  have hm : (address + 1) * CapacityBits.width q ≤ capWords * CapacityBits.width q :=
    Nat.mul_le_mul_right _ (by omega)
  have hpack : capWords * CapacityBits.width q ≤ word * bits :=
    (packedCapacityWords_mul_bits q capWords hbits).trans
      (Nat.mul_le_mul_right bits (Nat.le_add_right _ _))
  have houtside : address * CapacityBits.width q + CapacityBits.width q ≤ word * bits + i := by
    rw [Nat.add_mul, Nat.one_mul] at hm
    omega
  have hoffdiv : (word * bits + i) / bits = word := by
    rw [Nat.add_comm, Nat.add_mul_div_right _ _ hbits, Nat.div_eq_of_lt hi, Nat.zero_add]
  have hoffmod : (word * bits + i) % bits = i := by
    rw [Nat.mul_add_mod_self_right, Nat.mod_eq_of_lt hi]
  have h := writeHeap_external_bit (CapacityBits.width q) (address * CapacityBits.width q)
    (word * bits + i) value heap hbits hwidth hnext (hoffdiv.symm ▸ hindex) hvalue (Or.inr houtside)
  simpa only [hoffdiv, hoffmod, word] using h

theorem complement_word (value : BitVec bits) :
    BitVec.ofNat bits ((BitVec.ofNat bits (2 ^ bits - 1)).toNat - value.toNat) = ~~~value := by
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by
    have hp := Nat.two_pow_pos bits
    omega
  rw [BitVec.toNat_ofNat, Nat.mod_eq_of_lt hmax, ← BitVec.toNat_not,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]

theorem complement_nat (value : BitVec bits) :
    BitVec.ofNat bits (2 ^ bits - 1 - value.toNat) = ~~~value := by
  rw [← BitVec.toNat_not, BitVec.ofNat_toNat, BitVec.setWidth_eq]

def directWriteProgram (q bits : Nat) : List PackingOp :=
  [.base (.base (.constant .total (CapacityBits.width q))),
   .arithmetic .multiply .old .address .total,
   .base (.base (.constant .total bits)),
   .arithmetic .divide .index .old .total,
   .arithmetic .multiply .fresh .index .total,
   .base (.subtract .old .old .fresh),
   .base (.base (.constant .fresh (2 ^ CapacityBits.width q - 1))),
   .arithmetic .shiftLeft .fresh .fresh .old,
   .base (.base (.constant .flag (2 ^ bits - 1))),
   .base (.subtract .fresh .flag .fresh),
   .base (.base (.loadHeap .flag .index)),
   .arithmetic .bitAnd .flag .flag .fresh,
   .arithmetic .shiftLeft .fresh .value .old,
   .arithmetic .bitOr .flag .flag .fresh,
   .base (.base (.storeHeap .index .flag)),
   .base (.subtract .old .total .old),
   .base (.base (.constant .fresh (2 ^ CapacityBits.width q - 1))),
   .arithmetic .shiftRight .fresh .fresh .old,
   .base (.base (.constant .flag (2 ^ bits - 1))),
   .base (.subtract .fresh .flag .fresh),
   .base (.base (.constant .flag 1)),
   .base (.base (.add .index .index .flag)),
   .base (.base (.loadHeap .flag .index)),
   .arithmetic .bitAnd .flag .flag .fresh,
   .arithmetic .shiftRight .fresh .value .old,
   .arithmetic .bitOr .flag .flag .fresh,
   .base (.base (.storeHeap .index .flag))]

theorem directWriteProgram_length (q bits : Nat) : (directWriteProgram q bits).length = 27 := rfl

set_option maxRecDepth 6000 in
theorem directWriteProgram_trace_length (q bits : Nat) : (packingTrace (directWriteProgram q bits)).length = 282 := rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem directWriteProgram_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1)) :
    (executeOps rom (directWriteProgram q bits) state).heap =
      writeHeap (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q)
        (state.register .value) state.heap := by
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
  have hn : Fits bits (start / bits + 1) := hnext
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by
    have hpmax := Nat.two_pow_pos bits
    omega
  have hne : BitVec.ofNat bits (start / bits + 1) ≠ BitVec.ofNat bits (start / bits) :=
    (ofNat_injective_of_fit (bits := bits) _ _ hn hd).not.mpr (by omega)
  simp +decide only [directWriteProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte,
    arithmetic_and, arithmetic_or, arithmetic_shiftLeft, arithmetic_shiftRight,
    arithmetic_multiply, arithmetic_divide, complement_nat,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hmax,
    hne, writeHeap, writeLow, writeHigh, lowMask]

theorem directWriteProgram_straight (q bits : Nat) : StraightProgram (directWriteProgram q bits) := by
  simp [StraightProgram, directWriteProgram, StraightOp]

set_option maxRecDepth 6000 in
theorem directWriteProgram_code_fit (q : Nat) (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits) :
    WordsFit bits (packingCode (directWriteProgram q bits)) := by
  have hsmall : 135 < 2 ^ bits := by
    have hpow : 2 ^ 8 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
    omega
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hm : 2 ^ CapacityBits.width q - 1 < 2 ^ bits := by
    have hp : 2 ^ CapacityBits.width q ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hwidth
    have hpositive : 0 < 2 ^ CapacityBits.width q := Nat.two_pow_pos _
    omega
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by
    have hpositive := Nat.two_pow_pos bits
    omega
  intro value hvalue
  simp [packingCode, directWriteProgram, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, haltWords] at hvalue
  simp only [Fits]
  omega

theorem directWriteProgram_pc_fit (q : Nat) (hbits : 8 ≤ bits) : Fits bits (5 * (directWriteProgram q bits).length) := by
  have hpow : 2 ^ 8 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  simp only [Fits, directWriteProgram_length]
  omega

theorem directWriteProgram_run_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingRun rom (directWriteProgram q bits) 27 state).heap =
      writeHeap (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q)
        (state.register .value) state.heap := by
  rw [show 27 = (directWriteProgram q bits).length from rfl,
    packingRun_eq_executeOps_take rom _ state (directWriteProgram_straight q bits)
      (directWriteProgram_code_fit q hbits hwidth) (directWriteProgram_pc_fit q hbits) hpc hactive _ le_rfl,
    List.take_length, directWriteProgram_heap q rom state (by omega) hwidth hstart hnext]

theorem directWriteProgram_run_target (q capWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (haddress : (state.register .address).toNat < capWords) (hvalue : (state.register .value).toNat ≤ q)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    unpackHeap q capWords bits (packingRun rom (directWriteProgram q bits) 27 state).heap
      (state.register .address).toNat = (state.register .value).toNat := by
  rw [directWriteProgram_run_heap q rom state hbits hwidth hstart hnext hpc hactive]
  exact unpackHeap_write_target q capWords _ _ state.heap (by omega) hwidth haddress hnext
    (CapacityBits.value_lt_two_pow_width q _ hvalue)

theorem directWriteProgram_run_other_capacity (q capWords other : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (hvalue : (state.register .value).toNat ≤ q) (hother : other < capWords)
    (hne : other ≠ (state.register .address).toNat)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    unpackHeap q capWords bits (packingRun rom (directWriteProgram q bits) 27 state).heap other =
      unpackHeap q capWords bits state.heap other := by
  rw [directWriteProgram_run_heap q rom state hbits hwidth hstart hnext hpc hactive]
  exact unpackHeap_write_other_capacity q capWords _ other _ state.heap (by omega) hwidth hnext hregion
    (CapacityBits.value_lt_two_pow_width q _ hvalue) hother hne

theorem directWriteProgram_run_index (q capWords other : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (haddress : (state.register .address).toNat < capWords) (hother : capWords ≤ other)
    (hindex : Fits bits (packedCapacityWords q capWords bits + (other - capWords)))
    (hvalue : (state.register .value).toNat ≤ q)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    unpackHeap q capWords bits (packingRun rom (directWriteProgram q bits) 27 state).heap other =
      unpackHeap q capWords bits state.heap other := by
  rw [directWriteProgram_run_heap q rom state hbits hwidth hstart hnext hpc hactive]
  exact unpackHeap_write_index q capWords _ other _ state.heap (by omega) hwidth haddress hother hnext hindex
    (CapacityBits.value_lt_two_pow_width q _ hvalue)

theorem directWriteProgram_halts (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingRun rom (directWriteProgram q bits) 28 state).halted = true := by
  rw [show 28 = (directWriteProgram q bits).length + 1 from rfl,
    packingRun_executeOps_halt rom _ state (directWriteProgram_straight q bits)
      (directWriteProgram_code_fit q hbits hwidth) (directWriteProgram_pc_fit q hbits) hpc hactive]

theorem directWriteProgram_dynamicTrace_length (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingDynamicTrace rom (directWriteProgram q bits) 28 state).length = 282 := by
  rw [show 28 = (directWriteProgram q bits).length + 1 from rfl,
    packingDynamicTrace_eq_packingTrace rom _ state (directWriteProgram_straight q bits)
      (directWriteProgram_code_fit q hbits hwidth) (directWriteProgram_pc_fit q hbits) hpc hactive,
    directWriteProgram_trace_length]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem readProgram_accessFits (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hlookahead : (state.register .address).toNat * CapacityBits.width q / bits + 1 < heapWords)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hcount : count < (readProgram q bits).length) :
    packingAccessFits rom heapWords (packingRun rom (readProgram q bits) count state)
      (readProgram q bits)[count] := by
  rw [packingRun_eq_executeOps_take rom _ state (readProgram_straight q bits)
    (readProgram_code_fit q hbits hwidth) (readProgram_pc_fit q hbits) hpc hactive count hcount.le]
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hn : start / bits + 1 < 2 ^ bits := hnext
  have hl : start / bits + 1 < heapWords := hlookahead
  have hcount' : count ≤ 15 := by rw [readProgram_length] at hcount; omega
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [readProgram, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingAccessFits, AccessFits,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte]
  · simp only [arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
      ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd]
    omega
  · simp only [arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
      ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]
    exact hl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem directWriteProgram_accessFits (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hlookahead : (state.register .address).toNat * CapacityBits.width q / bits + 1 < heapWords)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hcount : count < (directWriteProgram q bits).length) :
    packingAccessFits rom heapWords (packingRun rom (directWriteProgram q bits) count state)
      (directWriteProgram q bits)[count] := by
  rw [packingRun_eq_executeOps_take rom _ state (directWriteProgram_straight q bits)
    (directWriteProgram_code_fit q hbits hwidth) (directWriteProgram_pc_fit q hbits) hpc hactive count hcount.le]
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hn : start / bits + 1 < 2 ^ bits := hnext
  have hl : start / bits + 1 < heapWords := hlookahead
  have hcount' : count ≤ 26 := by rw [directWriteProgram_length] at hcount; omega
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [directWriteProgram, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingAccessFits, AccessFits,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte]
  · simp only [arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
      ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd]
    omega
  · simp only [arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
      ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd]
    omega
  · simp only [arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
      ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]
    exact hl

  · simp only [arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat,
      Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
      ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
      Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]
    exact hl

/-! A two-store direct replacement can temporarily exceed q (for example,
the crossed fragments of 4 and 3 can represent 7 when q=5). The final A17
writer first clears both fragments and then fills the new value. -/

def clearLowHeap (width start : Nat) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update heap (BitVec.ofNat bits (start / bits))
    (heap (BitVec.ofNat bits (start / bits)) &&& ~~~(lowMask bits width <<< (start % bits)))

def clearHeap (width start : Nat) (heap : BitVec bits → BitVec bits) : BitVec bits → BitVec bits :=
  Function.update (clearLowHeap width start heap) (BitVec.ofNat bits (start / bits + 1))
    (heap (BitVec.ofNat bits (start / bits + 1)) &&& ~~~(lowMask bits width >>> (bits - start % bits)))

def fillLowHeap (width start : Nat) (value : BitVec bits) (heap : BitVec bits → BitVec bits) :
    BitVec bits → BitVec bits :=
  Function.update (clearHeap width start heap) (BitVec.ofNat bits (start / bits))
    (writeLow width (start % bits) value (heap (BitVec.ofNat bits (start / bits))))

def HeapBitsLE (small large : BitVec bits → BitVec bits) : Prop :=
  ∀ word i, (small word).getLsbD i = true → (large word).getLsbD i = true

theorem decodeScalar_mono (small large : List Bool)
    (h : ∀ i, small.getD i false = true → large.getD i false = true) :
    CapacityBits.decodeScalar small ≤ CapacityBits.decodeScalar large := by
  apply Nat.le_of_testBit
  intro i hi
  change (BitVec.ofBoolListLE small).getLsbD i = true at hi
  change (BitVec.ofBoolListLE large).getLsbD i = true
  rw [BitVec.getLsbD_ofBoolListLE] at hi ⊢
  exact h i hi

theorem unpackHeap_mono_of_bits (q capWords : Nat) (small large : BitVec bits → BitVec bits)
    (h : HeapBitsLE small large) (address : Nat) :
    unpackHeap q capWords bits small address ≤ unpackHeap q capWords bits large address := by
  simp only [unpackHeap]
  split_ifs with hc
  · apply decodeScalar_mono
    intro i hi
    by_cases hw : i < CapacityBits.width q
    · rw [List.getD_eq_getElem _ false (by simpa only [List.length_ofFn] using hw)] at hi ⊢
      simp only [List.getElem_ofFn] at hi ⊢
      exact h _ _ hi
    · rw [List.getD_eq_default _ false (by simpa only [List.length_ofFn] using Nat.le_of_not_gt hw)] at hi
      cases hi
  · apply Nat.le_of_testBit
    exact fun i hi => h _ i hi

theorem clearLowHeap_bits_le (width start : Nat) (heap : BitVec bits → BitVec bits) :
    HeapBitsLE (clearLowHeap width start heap) heap := by
  intro word i hi
  by_cases hw : word = BitVec.ofNat bits (start / bits)
  · subst word
    simp only [clearLowHeap, Function.update_self, BitVec.getLsbD_and, Bool.and_eq_true] at hi
    exact hi.1
  · simpa only [clearLowHeap, Function.update_apply, hw, ite_false] using hi

theorem clearHeap_eq_write_zero (width start : Nat) (heap : BitVec bits → BitVec bits) :
    clearHeap width start heap = writeHeap width start (BitVec.ofNat bits 0) heap := by
  simp [clearHeap, clearLowHeap, writeHeap, writeLow, writeHigh]

theorem clearHeap_bits_le_clearLow (width start : Nat) (heap : BitVec bits → BitVec bits)
    (hnext : Fits bits (start / bits + 1)) :
    HeapBitsLE (clearHeap width start heap) (clearLowHeap width start heap) := by
  have hb : Fits bits (start / bits) := (Nat.lt_succ_self _).trans hnext
  have hne : BitVec.ofNat bits (start / bits + 1) ≠ BitVec.ofNat bits (start / bits) :=
    (ofNat_injective_of_fit (bits := bits) _ _ hnext hb).not.mpr (by omega)
  intro word i hi
  by_cases hw : word = BitVec.ofNat bits (start / bits + 1)
  · subst word
    simp only [clearHeap, Function.update_self, BitVec.getLsbD_and, Bool.and_eq_true] at hi
    simpa only [clearLowHeap, Function.update_apply, hne, ite_false] using hi.1
  · simpa only [clearHeap, Function.update_apply, hw, ite_false] using hi

theorem clearHeap_bits_le_fillLow (width start : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hnext : Fits bits (start / bits + 1)) :
    HeapBitsLE (clearHeap width start heap) (fillLowHeap width start value heap) := by
  have hb : Fits bits (start / bits) := (Nat.lt_succ_self _).trans hnext
  have hne : BitVec.ofNat bits (start / bits) ≠ BitVec.ofNat bits (start / bits + 1) :=
    (ofNat_injective_of_fit (bits := bits) _ _ hb hnext).not.mpr (by omega)
  intro word i hi
  by_cases hw : word = BitVec.ofNat bits (start / bits)
  · subst word
    simp only [clearHeap, clearLowHeap, Function.update_apply, hne, ite_false, ite_true] at hi
    simp only [fillLowHeap, Function.update_self, writeLow, BitVec.getLsbD_or, hi, Bool.true_or]
  · simpa only [fillLowHeap, Function.update_apply, hw, ite_false] using hi

theorem fillLowHeap_bits_le_final (width start : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hnext : Fits bits (start / bits + 1)) :
    HeapBitsLE (fillLowHeap width start value heap) (writeHeap width start value heap) := by
  have hb : Fits bits (start / bits) := (Nat.lt_succ_self _).trans hnext
  have hne : BitVec.ofNat bits (start / bits + 1) ≠ BitVec.ofNat bits (start / bits) :=
    (ofNat_injective_of_fit (bits := bits) _ _ hnext hb).not.mpr (by omega)
  intro word i hi
  by_cases hh : word = BitVec.ofNat bits (start / bits + 1)
  · subst word
    simp only [fillLowHeap, clearHeap, Function.update_apply, hne, ite_false, ite_true] at hi
    simp only [writeHeap, Function.update_self, writeHigh, BitVec.getLsbD_or, hi, Bool.true_or]
  · by_cases hl : word = BitVec.ofNat bits (start / bits)
    · subst word
      simpa only [fillLowHeap, writeHeap, Function.update_apply, hh, ite_false, ite_true] using hi
    · simpa only [fillLowHeap, clearHeap, clearLowHeap, writeHeap, Function.update_apply,
        hh, hl, ite_false] using hi

def clearProgram (q bits : Nat) : List PackingOp :=
  [.base (.base (.constant .total (CapacityBits.width q))),
   .arithmetic .multiply .old .address .total,
   .base (.base (.constant .total bits)),
   .arithmetic .divide .index .old .total,
   .arithmetic .multiply .fresh .index .total,
   .base (.subtract .old .old .fresh),
   .base (.base (.constant .fresh (2 ^ CapacityBits.width q - 1))),
   .arithmetic .shiftLeft .fresh .fresh .old,
   .base (.base (.constant .flag (2 ^ bits - 1))),
   .base (.subtract .fresh .flag .fresh),
   .base (.base (.loadHeap .flag .index)),
   .arithmetic .bitAnd .flag .flag .fresh,
   .base (.base (.storeHeap .index .flag)),
   .base (.subtract .old .total .old),
   .base (.base (.constant .fresh (2 ^ CapacityBits.width q - 1))),
   .arithmetic .shiftRight .fresh .fresh .old,
   .base (.base (.constant .flag (2 ^ bits - 1))),
   .base (.subtract .fresh .flag .fresh),
   .base (.base (.constant .flag 1)),
   .base (.base (.add .index .index .flag)),
   .base (.base (.loadHeap .flag .index)),
   .arithmetic .bitAnd .flag .flag .fresh,
   .base (.base (.storeHeap .index .flag))]

def safeWriteProgram (q bits : Nat) : List PackingOp := clearProgram q bits ++ directWriteProgram q bits

theorem safeWriteProgram_length (q bits : Nat) : (safeWriteProgram q bits).length = 50 := rfl

set_option maxRecDepth 10000 in
theorem safeWriteProgram_trace_length (q bits : Nat) : (packingTrace (safeWriteProgram q bits)).length = 514 := rfl

theorem clearProgram_address (q : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (clearProgram q bits) state).register .address = state.register .address := rfl

theorem clearProgram_value (q : Nat) (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (clearProgram q bits) state).register .value = state.register .value := rfl

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1200000 in
theorem clearProgram_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1)) :
    (executeOps rom (clearProgram q bits) state).heap =
      clearHeap (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q) state.heap := by
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
  have hn : Fits bits (start / bits + 1) := hnext
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by
    have hpmax := Nat.two_pow_pos bits
    omega
  have hne : BitVec.ofNat bits (start / bits + 1) ≠ BitVec.ofNat bits (start / bits) :=
    (ofNat_injective_of_fit (bits := bits) _ _ hn hd).not.mpr (by omega)
  simp +decide only [clearProgram, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, arithmetic_and, arithmetic_shiftLeft, arithmetic_shiftRight,
    arithmetic_multiply, arithmetic_divide, complement_nat,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hc, Nat.mod_eq_of_lt hmax, hne, clearHeap, clearLowHeap, lowMask]

theorem writeHeap_clearHeap (width start : Nat) (value : BitVec bits)
    (heap : BitVec bits → BitVec bits) (hnext : Fits bits (start / bits + 1)) :
    writeHeap width start value (clearHeap width start heap) = writeHeap width start value heap := by
  have hb : Fits bits (start / bits) := (Nat.lt_succ_self _).trans hnext
  have hne : BitVec.ofNat bits (start / bits) ≠ BitVec.ofNat bits (start / bits + 1) :=
    (ofNat_injective_of_fit (bits := bits) _ _ hb hnext).not.mpr (by omega)
  funext word
  by_cases hh : word = BitVec.ofNat bits (start / bits + 1)
  · subst word
    simp [writeHeap, clearHeap, clearLowHeap, writeHigh, BitVec.and_assoc]
  · by_cases hl : word = BitVec.ofNat bits (start / bits)
    · subst word
      simp [writeHeap, clearHeap, clearLowHeap, writeLow, hne, BitVec.and_assoc]
    · simp [writeHeap, clearHeap, clearLowHeap, hh, hl]

theorem safeWriteProgram_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1)) :
    (executeOps rom (safeWriteProgram q bits) state).heap =
      writeHeap (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q)
        (state.register .value) state.heap := by
  have hs : Fits bits (((executeOps rom (clearProgram q bits) state).register .address).toNat * CapacityBits.width q) := by
    rwa [clearProgram_address]
  have hn : Fits bits (((executeOps rom (clearProgram q bits) state).register .address).toNat * CapacityBits.width q / bits + 1) := by
    rwa [clearProgram_address]
  rw [safeWriteProgram, executeOps_append, directWriteProgram_heap q rom _ hbits hwidth hs hn,
    clearProgram_address, clearProgram_value, clearProgram_heap q rom state hbits hwidth hstart hnext,
    writeHeap_clearHeap _ _ _ _ hnext]

def HeapPreservingOp : PackingOp → Prop
  | .base (.base (.storeHeap _ _)) => False
  | _ => True

theorem executeOps_heap_of_no_store (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (hno : ∀ op ∈ program, HeapPreservingOp op) :
    (executeOps rom program state).heap = state.heap := by
  induction program generalizing state with
  | nil => rfl
  | cons op later ih =>
    have ho := hno op List.mem_cons_self
    have hl := fun entry he => hno entry (List.mem_cons_of_mem op he)
    rw [executeOps, ih _ hl]
    cases op with
    | arithmetic operation target left right => rfl
    | jumpIfZero condition target => rfl
    | base op => cases op with
      | subtract target left right => rfl
      | base instruction => cases instruction <;> try rfl
                            cases ho

theorem executeOps_prefix_heap_eq (rom : PhysicalROM) (program : List PackingOp)
    (state : WordState bits) (first count gap : Nat) (hfirst : first ≤ count)
    (hgap : count - first ≤ gap)
    (hno : ∀ op ∈ (program.drop first).take gap, HeapPreservingOp op) :
    (executeOps rom (program.take count) state).heap =
      (executeOps rom (program.take first) state).heap := by
  have heq : count = first + (count - first) := by omega
  conv_lhs => rw [heq, List.take_add, executeOps_append]
  apply executeOps_heap_of_no_store
  intro op hop
  apply hno op
  have htake : (program.drop first).take (count - first) =
      ((program.drop first).take gap).take (count - first) := by
    rw [List.take_take, Nat.min_eq_left hgap]
  rw [htake] at hop
  exact List.mem_of_mem_take hop

set_option maxRecDepth 8000 in
theorem clearProgram_firstStore_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q)) :
    (executeOps rom ((clearProgram q bits).take 13) state).heap =
      clearLowHeap (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q) state.heap := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hp : start / bits * bits < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hs
  have hsub : start - start / bits * bits = start % bits := by
    have h := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at h
    omega
  have hrf : start % bits < 2 ^ bits := (Nat.mod_lt _ hbits).trans hb
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by
    have hpmax := Nat.two_pow_pos bits
    omega
  simp +decide only [clearProgram, List.take_succ_cons, List.take_zero, executeOps, packingExecuteOp,
    wordOp, wordInstruction, Function.update_apply, ↓reduceIte, arithmetic_and, arithmetic_shiftLeft,
    arithmetic_multiply, arithmetic_divide, complement_nat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hmax, clearLowHeap, lowMask]

set_option maxRecDepth 8000 in
theorem directWriteProgram_firstStore_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q)) :
    (executeOps rom ((directWriteProgram q bits).take 15) state).heap =
      Function.update state.heap (BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits))
        (writeLow (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q % bits)
          (state.register .value)
          (state.heap (BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits)))) := by
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hp : start / bits * bits < 2 ^ bits := (Nat.div_mul_le_self _ _).trans_lt hs
  have hrf : start % bits < 2 ^ bits := (Nat.mod_lt _ hbits).trans hb
  have hsub : start - start / bits * bits = start % bits := by
    have h := Nat.div_add_mod start bits
    rw [Nat.mul_comm bits (start / bits)] at h
    omega
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by
    have hpmax := Nat.two_pow_pos bits
    omega
  simp +decide only [directWriteProgram, List.take_succ_cons, List.take_zero, executeOps, packingExecuteOp,
    wordOp, wordInstruction, Function.update_apply, ↓reduceIte, arithmetic_and, arithmetic_or, arithmetic_shiftLeft,
    arithmetic_multiply, arithmetic_divide, complement_nat, BitVec.toNat_ofNat,
    Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hmax, writeLow, lowMask]

set_option maxRecDepth 8000 in
theorem safeWriteProgram_prefix_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (count : Nat) (hcount : count ≤ 50) :
    (executeOps rom ((safeWriteProgram q bits).take count) state).heap =
      if count < 13 then state.heap
      else if count < 23 then clearLowHeap (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q) state.heap
      else if count < 38 then clearHeap (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q) state.heap
      else if count < 50 then fillLowHeap (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q) (state.register .value) state.heap
      else writeHeap (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q) (state.register .value) state.heap := by
  by_cases h0 : count < 13
  · rw [ite_eq_left h0]
    rw [executeOps_prefix_heap_eq rom _ state 0 count 12 (by omega) (by omega) (by
      simp [safeWriteProgram, clearProgram, directWriteProgram, HeapPreservingOp])]
    rfl
  · rw [ite_eq_right h0]
    by_cases h1 : count < 23
    · rw [ite_eq_left h1]
      rw [executeOps_prefix_heap_eq rom _ state 13 count 9 (by omega) (by omega) (by
        simp [safeWriteProgram, clearProgram, directWriteProgram, HeapPreservingOp])]
      exact clearProgram_firstStore_heap q rom state hbits hwidth hstart
    · rw [ite_eq_right h1]
      by_cases h2 : count < 38
      · rw [ite_eq_left h2]
        rw [executeOps_prefix_heap_eq rom _ state 23 count 14 (by omega) (by omega) (by
          simp [safeWriteProgram, clearProgram, directWriteProgram, HeapPreservingOp])]
        exact clearProgram_heap q rom state hbits hwidth hstart hnext
      · rw [ite_eq_right h2]
        by_cases h3 : count < 50
        · rw [ite_eq_left h3]
          rw [executeOps_prefix_heap_eq rom _ state 38 count 11 (by omega) (by omega) (by
            simp [safeWriteProgram, clearProgram, directWriteProgram, HeapPreservingOp])]
          change (executeOps rom (clearProgram q bits ++ (directWriteProgram q bits).take 15) state).heap = _
          have hs : Fits bits (((executeOps rom (clearProgram q bits) state).register .address).toNat * CapacityBits.width q) := by
            rwa [clearProgram_address]
          rw [executeOps_append, directWriteProgram_firstStore_heap q rom _ hbits hwidth hs,
            clearProgram_address, clearProgram_value, clearProgram_heap q rom state hbits hwidth hstart hnext]
          have hb : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits) :=
            (Nat.lt_succ_self _).trans hnext
          have hne : BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits) ≠
              BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits + 1) :=
            (ofNat_injective_of_fit (bits := bits) _ _ hb hnext).not.mpr (by omega)
          simp [fillLowHeap, clearHeap, clearLowHeap, writeLow, hne, BitVec.and_assoc]
        · rw [ite_eq_right h3]
          have hc4 : count = 50 := by omega
          subst count
          rw [show 50 = (safeWriteProgram q bits).length from rfl, List.take_length]
          exact safeWriteProgram_heap q rom state hbits hwidth hstart hnext

theorem safeWriteProgram_prefix_capacityBounded (q capWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (haddress : (state.register .address).toNat < capWords) (hvalue : (state.register .value).toNat ≤ q)
    (hbounded : CapacityPrefixBounded q capWords (unpackHeap q capWords bits state.heap))
    (count : Nat) (hcount : count ≤ 50) :
    CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (executeOps rom ((safeWriteProgram q bits).take count) state).heap) := by
  let start := (state.register .address).toNat * CapacityBits.width q
  let value := state.register .value
  have hv : value.toNat < 2 ^ CapacityBits.width q := CapacityBits.value_lt_two_pow_width q _ hvalue
  have hn : Fits bits (start / bits + 1) := hnext
  have hfinal : CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (writeHeap (CapacityBits.width q) start value state.heap)) := by
    intro other ho
    by_cases heq : other = (state.register .address).toNat
    · subst other
      rw [unpackHeap_write_target q capWords _ _ state.heap hbits hwidth haddress hnext hv]
      exact hvalue
    · rw [unpackHeap_write_other_capacity q capWords _ other _ state.heap hbits hwidth hnext hregion hv ho heq]
      exact hbounded other ho
  have hclearLow : CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (clearLowHeap (CapacityBits.width q) start state.heap)) := by
    intro other ho
    exact (unpackHeap_mono_of_bits q capWords _ _ (clearLowHeap_bits_le _ _ _) other).trans (hbounded other ho)
  have hclear : CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (clearHeap (CapacityBits.width q) start state.heap)) := by
    intro other ho
    exact (unpackHeap_mono_of_bits q capWords _ _ (clearHeap_bits_le_clearLow _ _ _ hn) other).trans (hclearLow other ho)
  have hfill : CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (fillLowHeap (CapacityBits.width q) start value state.heap)) := by
    intro other ho
    exact (unpackHeap_mono_of_bits q capWords _ _ (fillLowHeap_bits_le_final _ _ _ _ hn) other).trans (hfinal other ho)
  rw [safeWriteProgram_prefix_heap q rom state hbits hwidth hstart hnext count hcount]
  split_ifs
  · exact hbounded
  · exact hclearLow
  · exact hclear
  · exact hfill
  · exact hfinal

theorem safeWriteProgram_prefix_frame (q capWords other : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (haddress : (state.register .address).toNat < capWords) (hvalue : (state.register .value).toNat ≤ q)
    (hwhere : (other < capWords ∧ other ≠ (state.register .address).toNat) ∨
      (capWords ≤ other ∧ Fits bits (packedCapacityWords q capWords bits + (other - capWords))))
    (count : Nat) (hcount : count ≤ 50) :
    unpackHeap q capWords bits (executeOps rom ((safeWriteProgram q bits).take count) state).heap other =
      unpackHeap q capWords bits state.heap other := by
  let start := (state.register .address).toNat * CapacityBits.width q
  let value := state.register .value
  have hv : value.toNat < 2 ^ CapacityBits.width q := CapacityBits.value_lt_two_pow_width q _ hvalue
  have hz : (BitVec.ofNat bits 0).toNat < 2 ^ CapacityBits.width q := by
    simpa only [BitVec.toNat_ofNat, Nat.zero_mod] using Nat.two_pow_pos (CapacityBits.width q)
  have hn : Fits bits (start / bits + 1) := hnext
  have hclear : unpackHeap q capWords bits (clearHeap (CapacityBits.width q) start state.heap) other =
      unpackHeap q capWords bits state.heap other := by
    rw [clearHeap_eq_write_zero]
    rcases hwhere with ⟨ho, hne⟩ | ⟨ho, hi⟩
    · exact unpackHeap_write_other_capacity q capWords _ other _ state.heap hbits hwidth hnext hregion hz ho hne
    · exact unpackHeap_write_index q capWords _ other _ state.heap hbits hwidth haddress ho hnext hi hz
  have hfinal : unpackHeap q capWords bits (writeHeap (CapacityBits.width q) start value state.heap) other =
      unpackHeap q capWords bits state.heap other := by
    rcases hwhere with ⟨ho, hne⟩ | ⟨ho, hi⟩
    · exact unpackHeap_write_other_capacity q capWords _ other _ state.heap hbits hwidth hnext hregion hv ho hne
    · exact unpackHeap_write_index q capWords _ other _ state.heap hbits hwidth haddress ho hnext hi hv
  have hclearLow : unpackHeap q capWords bits (clearLowHeap (CapacityBits.width q) start state.heap) other =
      unpackHeap q capWords bits state.heap other := by
    apply le_antisymm (unpackHeap_mono_of_bits q capWords _ _ (clearLowHeap_bits_le _ _ _) other)
    calc
      _ = unpackHeap q capWords bits (clearHeap (CapacityBits.width q) start state.heap) other := hclear.symm
      _ ≤ _ := unpackHeap_mono_of_bits q capWords _ _ (clearHeap_bits_le_clearLow _ _ _ hn) other
  have hfill : unpackHeap q capWords bits (fillLowHeap (CapacityBits.width q) start value state.heap) other =
      unpackHeap q capWords bits state.heap other := by
    apply le_antisymm
    · exact (unpackHeap_mono_of_bits q capWords _ _ (fillLowHeap_bits_le_final _ _ _ _ hn) other).trans hfinal.le
    · exact hclear.symm.le.trans (unpackHeap_mono_of_bits q capWords _ _ (clearHeap_bits_le_fillLow _ _ _ _ hn) other)
  rw [safeWriteProgram_prefix_heap q rom state hbits hwidth hstart hnext count hcount]
  split_ifs
  · rfl
  · exact hclearLow
  · exact hclear
  · exact hfill
  · exact hfinal

theorem safeWriteProgram_straight (q bits : Nat) : StraightProgram (safeWriteProgram q bits) := by
  simp [StraightProgram, safeWriteProgram, clearProgram, directWriteProgram, StraightOp]

set_option maxRecDepth 10000 in
theorem safeWriteProgram_code_fit (q : Nat) (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits) :
    WordsFit bits (packingCode (safeWriteProgram q bits)) := by
  have hsmall : 250 < 2 ^ bits := by
    have hpow : 2 ^ 8 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
    omega
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hm : 2 ^ CapacityBits.width q - 1 < 2 ^ bits := by
    have hp : 2 ^ CapacityBits.width q ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hwidth
    have hpositive : 0 < 2 ^ CapacityBits.width q := Nat.two_pow_pos _
    omega
  have hmax : 2 ^ bits - 1 < 2 ^ bits := by
    have hpositive := Nat.two_pow_pos bits
    omega
  intro value hvalue
  simp [packingCode, safeWriteProgram, clearProgram, directWriteProgram, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, haltWords] at hvalue
  simp only [Fits]
  omega

theorem safeWriteProgram_pc_fit (q : Nat) (hbits : 8 ≤ bits) : Fits bits (5 * (safeWriteProgram q bits).length) := by
  have hpow : 2 ^ 8 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  simp only [Fits, safeWriteProgram_length]
  omega

theorem safeWriteProgram_run_heap (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingRun rom (safeWriteProgram q bits) 50 state).heap =
      writeHeap (CapacityBits.width q) ((state.register .address).toNat * CapacityBits.width q)
        (state.register .value) state.heap := by
  rw [show 50 = (safeWriteProgram q bits).length from rfl,
    packingRun_eq_executeOps_take rom _ state (safeWriteProgram_straight q bits)
      (safeWriteProgram_code_fit q hbits hwidth) (safeWriteProgram_pc_fit q hbits) hpc hactive _ le_rfl,
    List.take_length, safeWriteProgram_heap q rom state (by omega) hwidth hstart hnext]

theorem safeWriteProgram_run_target (q capWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (haddress : (state.register .address).toNat < capWords) (hvalue : (state.register .value).toNat ≤ q)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    unpackHeap q capWords bits (packingRun rom (safeWriteProgram q bits) 50 state).heap
      (state.register .address).toNat = (state.register .value).toNat := by
  rw [safeWriteProgram_run_heap q rom state hbits hwidth hstart hnext hpc hactive]
  exact unpackHeap_write_target q capWords _ _ state.heap (by omega) hwidth haddress hnext
    (CapacityBits.value_lt_two_pow_width q _ hvalue)

theorem safeWriteProgram_run_prefix_capacityBounded (q capWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (haddress : (state.register .address).toNat < capWords) (hvalue : (state.register .value).toNat ≤ q)
    (hbounded : CapacityPrefixBounded q capWords (unpackHeap q capWords bits state.heap))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hcount : count ≤ 50) :
    CapacityPrefixBounded q capWords
      (unpackHeap q capWords bits (packingRun rom (safeWriteProgram q bits) count state).heap) := by
  rw [packingRun_eq_executeOps_take rom _ state (safeWriteProgram_straight q bits)
    (safeWriteProgram_code_fit q hbits hwidth) (safeWriteProgram_pc_fit q hbits) hpc hactive count
    (by simpa only [safeWriteProgram_length] using hcount)]
  exact safeWriteProgram_prefix_capacityBounded q capWords rom state (by omega) hwidth hstart hnext
    hregion haddress hvalue hbounded count hcount

theorem safeWriteProgram_run_prefix_frame (q capWords other : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hregion : Fits bits (capWords * CapacityBits.width q))
    (haddress : (state.register .address).toNat < capWords) (hvalue : (state.register .value).toNat ≤ q)
    (hwhere : (other < capWords ∧ other ≠ (state.register .address).toNat) ∨
      (capWords ≤ other ∧ Fits bits (packedCapacityWords q capWords bits + (other - capWords))))
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hcount : count ≤ 50) :
    unpackHeap q capWords bits (packingRun rom (safeWriteProgram q bits) count state).heap other =
      unpackHeap q capWords bits state.heap other := by
  rw [packingRun_eq_executeOps_take rom _ state (safeWriteProgram_straight q bits)
    (safeWriteProgram_code_fit q hbits hwidth) (safeWriteProgram_pc_fit q hbits) hpc hactive count
    (by simpa only [safeWriteProgram_length] using hcount)]
  exact safeWriteProgram_prefix_frame q capWords other rom state (by omega) hwidth hstart hnext
    hregion haddress hvalue hwhere count hcount

theorem safeWriteProgram_halts (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingRun rom (safeWriteProgram q bits) 51 state).halted = true := by
  rw [show 51 = (safeWriteProgram q bits).length + 1 from rfl,
    packingRun_executeOps_halt rom _ state (safeWriteProgram_straight q bits)
      (safeWriteProgram_code_fit q hbits hwidth) (safeWriteProgram_pc_fit q hbits) hpc hactive]

theorem safeWriteProgram_dynamicTrace_length (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingDynamicTrace rom (safeWriteProgram q bits) 51 state).length = 514 := by
  rw [show 51 = (safeWriteProgram q bits).length + 1 from rfl,
    packingDynamicTrace_eq_packingTrace rom _ state (safeWriteProgram_straight q bits)
      (safeWriteProgram_code_fit q hbits hwidth) (safeWriteProgram_pc_fit q hbits) hpc hactive,
    safeWriteProgram_trace_length]

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1600000 in
theorem safeWriteProgram_accessFits (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hbits : 8 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hnext : Fits bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))
    (hlookahead : (state.register .address).toNat * CapacityBits.width q / bits + 1 < heapWords)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hcount : count < (safeWriteProgram q bits).length) :
    packingAccessFits rom heapWords (packingRun rom (safeWriteProgram q bits) count state)
      (safeWriteProgram q bits)[count] := by
  rw [packingRun_eq_executeOps_take rom _ state (safeWriteProgram_straight q bits)
    (safeWriteProgram_code_fit q hbits hwidth) (safeWriteProgram_pc_fit q hbits) hpc hactive count hcount.le]
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hn : start / bits + 1 < 2 ^ bits := hnext
  have hl : start / bits + 1 < heapWords := hlookahead
  have hcount' : count ≤ 49 := by rw [safeWriteProgram_length] at hcount; omega
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [safeWriteProgram, clearProgram, directWriteProgram, List.cons_append,
    List.nil_append, List.take_succ_cons, List.take_zero, List.getElem_cons_succ, List.getElem_cons_zero,
    executeOps, packingAccessFits, AccessFits, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte]
  all_goals first
    | (simp only [arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat,
        Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
        ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
        Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd]; omega)
    | (simp only [arithmetic_multiply, arithmetic_divide, BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat,
        Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
        ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
        Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hn]; exact hl)
end PaperProofs.Structure.LaminarTree.AlgorithmClaims.PackedCapacityRAM
