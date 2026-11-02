module

public import PaperProofs.Structure.CompactControllerClaims
public import PaperProofs.Structure.PackedCapacityRAM
public import Mathlib.Tactic

set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 16000
set_option maxHeartbeats 2000000

/-! Fixed runtime packed reader. No dimension-dependent code literal is
present: width/mask/bits are loaded from actual physical headers 0/1/3.
The temporary prepare ABI is separate from the final live [t,C,P,bits] ABI.
Private candidate only; this task has not compiled the source. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimePacked016

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM
open CompactControllerClaims (dataHeap)

variable {bits : Nat}

/-- A normal internal representation obligation, discharged by the actual
prepare producer. It is not part of the raw controller input. -/
structure Header (q : Nat) (heap : BitVec bits → BitVec bits) : Prop where
  width : heap (BitVec.ofNat bits 0) = BitVec.ofNat bits (CapacityBits.width q)
  mask : heap (BitVec.ofNat bits 1) = lowMask bits (CapacityBits.width q)
  ones : heap (BitVec.ofNat bits 2) = BitVec.ofNat bits (2 ^ bits - 1)
  wordBits : heap (BitVec.ofNat bits 3) = BitVec.ofNat bits bits

/-- Fixed 21-op source, independent of q, bits and all dimension values.
After offset=old-index*bits, fresh is dead until its existing reassignment;
only at that point is it borrowed for the actual base-four pointer shift. -/
def read : List PackingOp :=
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
   .base (.base (.loadHeap .value .index)),
   .arithmetic .shiftRight .value .value .old,
   .base (.base (.constant .fresh 1)),
   .base (.base (.add .index .index .fresh)),
   .base (.base (.loadHeap .fresh .index)),
   .base (.subtract .old .total .old),
   .arithmetic .shiftLeft .fresh .fresh .old,
   .arithmetic .bitOr .value .value .fresh,
   .base (.base (.constant .total 1)),
   .base (.base (.loadHeap .total .total)),
   .arithmetic .bitAnd .value .value .total]

theorem read_length : read.length = 21 := rfl
theorem read_code_length : (packingCode read).length = 110 := rfl
theorem read_trace_length : (packingTrace read).length = 222 := rfl

theorem read_straight : StraightProgram read := by
  simp [StraightProgram, read, StraightOp]

theorem read_code_fit (hbits : 7 ≤ bits) : WordsFit bits (packingCode read) := by
  have hpow : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  intro value hvalue
  simp [packingCode, read, PackingOp.encode, Op.encodeWords,
    Instruction.encodeWords, PackingPrimitive.word, Register.word, haltWords] at hvalue
  simp only [Fits]
  omega

theorem read_pc_fit (hbits : 7 ≤ bits) : Fits bits (5 * read.length) := by
  have hpow : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  simp only [Fits, read_length]
  omega

theorem read_heap (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom read state).heap = state.heap := rfl

theorem read_address (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom read state).register .address = state.register .address := rfl

theorem read_flag (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom read state).register .flag = state.register .flag := rfl

theorem read_prefix_heap (rom : PhysicalROM) (state : WordState bits) (count : Nat) :
    (executeOps rom (read.take count) state).heap = state.heap := by
  apply executeOps_heap_of_no_store
  intro op ho
  have hno : ∀ instruction ∈ read, HeapPreservingOp instruction := by
    simp [read, HeapPreservingOp]
  exact hno op (List.mem_of_mem_take ho)

theorem read_prefix_header (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (count : Nat) :
    Header q (executeOps rom (read.take count) state).heap := by
  rw [read_prefix_heap]
  exact hh

theorem dataHeap_word (heap : BitVec bits → BitVec bits) (a : Nat) :
    dataHeap heap (BitVec.ofNat bits a) = heap (BitVec.ofNat bits (4 + a)) := by
  unfold dataHeap CompactControllerClaims.physicalHeaderWords
  apply congrArg heap
  rw [← BitVec.ofNat_add_ofNat, BitVec.ofNat_toNat, BitVec.setWidth_eq,
    BitVec.ofNat_add_ofNat]

set_option maxRecDepth 12000 in
theorem read_value (q : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q)) :
    (executeOps rom read state).register .value =
      readTwoWords (CapacityBits.width q)
        ((state.register .address).toNat * CapacityBits.width q % bits)
        (dataHeap state.heap (BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits)))
        (dataHeap state.heap (BitVec.ofNat bits ((state.register .address).toNat * CapacityBits.width q / bits + 1))) := by
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
  simp +decide only [read, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, hh.width, hh.mask, hh.wordBits,
    arithmetic_and, arithmetic_or, arithmetic_shiftLeft, arithmetic_shiftRight,
    arithmetic_multiply, arithmetic_divide,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hb, Nat.mod_eq_of_lt hw,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hp, hsub,
    Nat.mod_eq_of_lt hrf, Nat.mod_eq_of_lt hc,
    dataHeap_word, Nat.add_comm, Nat.add_left_comm, readTwoWords, lowMask]

theorem read_decodes (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 0 < bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (ha : (state.register .address).toNat < C) :
    ((executeOps rom read state).register .value).toNat =
      unpackHeap q C bits (dataHeap state.heap) (state.register .address).toNat := by
  rw [read_value q rom state hh hbits hwidth hstart]
  exact readTwoWords_eq_unpackHeap q C _ (dataHeap state.heap) hbits hwidth ha

theorem read_run_body (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    packingRun rom read 21 state = executeOps rom read state := by
  rw [show 21 = read.length from rfl,
    packingRun_eq_executeOps_take rom read state read_straight (read_code_fit hbits)
      (read_pc_fit hbits) hpc hactive _ le_rfl, List.take_length]

theorem read_run_decodes (q C : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (ha : (state.register .address).toNat < C)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    ((packingRun rom read 21 state).register .value).toNat =
      unpackHeap q C bits (dataHeap state.heap) (state.register .address).toNat := by
  rw [read_run_body rom state hbits hpc hactive]
  exact read_decodes q C rom state hh (by omega) hwidth hstart ha

theorem read_run_prefix_heap (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hc : count ≤ 21) :
    (packingRun rom read count state).heap = state.heap := by
  rw [packingRun_eq_executeOps_take rom read state read_straight (read_code_fit hbits)
    (read_pc_fit hbits) hpc hactive count (by rwa [read_length])]
  exact read_prefix_heap rom state count

theorem read_run_halt (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    packingRun rom read 22 state = { executeOps rom read state with halted := true } := by
  exact packingRun_executeOps_halt rom read state read_straight (read_code_fit hbits)
    (read_pc_fit hbits) hpc hactive

theorem read_dynamicTrace_length (rom : PhysicalROM) (state : WordState bits)
    (hbits : 7 ≤ bits) (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false) :
    (packingDynamicTrace rom read 22 state).length = 222 := by
  rw [show 22 = read.length + 1 from rfl,
    packingDynamicTrace_eq_packingTrace rom read state read_straight (read_code_fit hbits)
      (read_pc_fit hbits) hpc hactive, read_trace_length]

/-- Every actual fetched reader prefix accesses only the three header words
and physical low/high words. Absolute +4 high Fits and allocation bounds
are explicit; the same conditions serve later fixed-body composition. -/
theorem read_accessFits (q heapWords : Nat) (rom : PhysicalROM) (state : WordState bits)
    (hh : Header q state.heap) (hbits : 7 ≤ bits) (hwidth : CapacityBits.width q ≤ bits)
    (hstart : Fits bits ((state.register .address).toNat * CapacityBits.width q))
    (hphysical : Fits bits (4 + ((state.register .address).toNat * CapacityBits.width q / bits + 1)))
    (hlookahead : 4 + ((state.register .address).toNat * CapacityBits.width q / bits + 1) < heapWords)
    (hpc : state.pc = BitVec.ofNat bits 0) (hactive : state.halted = false)
    (count : Nat) (hcount : count < read.length) :
    packingAccessFits rom heapWords (packingRun rom read count state) read[count] := by
  rw [packingRun_eq_executeOps_take rom read state read_straight (read_code_fit hbits)
    (read_pc_fit hbits) hpc hactive count hcount.le]
  let start := (state.register .address).toNat * CapacityBits.width q
  have hb : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hw : CapacityBits.width q < 2 ^ bits := hwidth.trans_lt hb
  have hs : start < 2 ^ bits := hstart
  have hd : start / bits < 2 ^ bits := (Nat.div_le_self _ _).trans_lt hs
  have hn : 4 + (start / bits + 1) < 2 ^ bits := hphysical
  have hl : 4 + (start / bits + 1) < heapWords := hlookahead
  have hlo : start / bits + 4 < 2 ^ bits := by omega
  have hhi : start / bits + 4 + 1 < 2 ^ bits := by omega
  have hpow : 2 ^ 7 ≤ 2 ^ bits := Nat.pow_le_pow_right (by decide) hbits
  have hone : 1 < 2 ^ bits := by omega
  have hthree : 3 < 2 ^ bits := by omega
  have hheader_bound : 4 < heapWords := by
    have hm := Nat.add_lt_add_left (Nat.succ_pos (start / bits)) 4
    simp only [Nat.add_zero] at hm
    exact hm.trans hl
  have hcount' : count ≤ 20 := by rw [read_length] at hcount; omega
  interval_cases count <;> try exact True.intro
  all_goals simp +decide only [read, List.take_succ_cons, List.take_zero,
    List.getElem_cons_succ, List.getElem_cons_zero, executeOps, packingAccessFits, AccessFits,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    hh.width, hh.wordBits, arithmetic_multiply, arithmetic_divide,
    BitVec.toNat_ofNat, BitVec.ofNat_add_ofNat, Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hb,
    ← show start = (state.register .address).toNat * CapacityBits.width q from rfl,
    Nat.mod_eq_of_lt hs, Nat.mod_eq_of_lt hd, Nat.mod_eq_of_lt hlo, Nat.mod_eq_of_lt hhi,
    Nat.mod_eq_of_lt hone, Nat.mod_eq_of_lt hthree,
    Nat.zero_mod, Nat.add_assoc]
  all_goals omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareRuntimePacked016
