module

public import PaperProofs.Structure.PSTR_RuntimePackedRead_008
public import PaperProofs.Structure.PSTR_HD_WordSegments_014

/-! Fixed positive-tool leaf-used reader. It loads the cached leaf label
from the actual heap address, skips directly to HALT for label0, otherwise
computes the bitmap scalar address from real N/q/tree headers and executes
the existing physical packed reader. No node incidence bitmap is supplied. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRLeafUsed

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open AlgorithmClaims.PackedCapacityRAM CompactControllerClaims

def lead : List PackingOp :=
  [.base (.base (.loadHeap .value .address)), .base (.base (.constant .fresh 180))]

def branch : PackingOp := .jumpIfZero .value .fresh

def setup : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadROM .input .old .address)),
   .base (.base (.constant .fresh 1)),
   .base (.base (.add .old .old .fresh)),
   .base (.base (.constant .address 1)),
   .base (.base (.loadROM .input .fresh .address)),
   .base (.base (.constant .address 2)),
   .base (.base (.add .fresh .fresh .address)),
   .arithmetic .multiply .old .old .fresh,
   .base (.base (.constant .address 0)),
   .base (.base (.loadHeap .index .address)),
   .base (.base (.constant .fresh 1)),
   .base (.base (.add .index .index .fresh)),
   .arithmetic .multiply .old .old .index,
   .base (.subtract .value .value .fresh),
   .base (.base (.add .address .old .value))]

def body : List PackingOp := setup ++ PSTRRuntimePackedRead.program

def program : List PackingOp := lead ++ [branch] ++ body

theorem lead_length : lead.length = 2 := rfl
theorem setup_length : setup.length = 16 := rfl
theorem body_length : body.length = 33 := rfl
theorem program_length : program.length = 36 := rfl

theorem lead_straight : StraightProgram lead := by simp [StraightProgram, StraightOp, lead]
theorem setup_straight : StraightProgram setup := by simp [StraightProgram, StraightOp, setup]

theorem body_straight : StraightProgram body := by
  intro op ho
  rcases List.mem_append.mp ho with hs | hr
  · exact setup_straight op hs
  · exact PSTRRuntimePackedRead.program_straight op hr

theorem code_length : (packingCode program).length = 185 := by rw [packingCode_length, program_length]

set_option maxRecDepth 10000 in
theorem code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  simp [packingCode, program, lead, branch, body, setup, PSTRRuntimePackedRead.program,
    PackingOp.encode, Op.encodeWords, Instruction.encodeWords, PackingPrimitive.word,
    Register.word, Region.word, haltWords] at hv
  unfold Fits
  omega

theorem pc_fit {bits : Nat} (hb : 8 ≤ bits) : Fits bits (5 * program.length) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  change 180 < 2 ^ bits
  omega

theorem prefix_run {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hb : 8 ≤ bits) (hp : state.pc = BitVec.ofNat bits 0) (ha : state.halted = false) :
    packingRun rom program 3 state = executeOps rom (lead ++ [branch]) state := by
  rw [show 3 = lead.length + 1 from rfl,
    PSTRWordSegments.segment_last rom program lead branch 0 (by decide) ?_ (by rfl)
      lead_straight (code_fit hb) (pc_fit hb) state hp ha, executeOps_append]
  · rfl
  · intro i hi
    change i < 2 at hi
    interval_cases i <;> rfl

theorem prefix_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (lead ++ [branch]) state).heap = state.heap := rfl

theorem prefix_width {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (lead ++ [branch]) state).register .total = state.register .total := rfl

theorem prefix_mask {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (lead ++ [branch]) state).register .flag = state.register .flag := rfl

theorem prefix_value {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom (lead ++ [branch]) state).register .value = state.heap (state.register .address) := rfl

theorem prefix_pc {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits 0) :
    (executeOps rom (lead ++ [branch]) state).pc =
      if (state.heap (state.register .address)).toNat = 0 then BitVec.ofNat bits 180 else BitVec.ofNat bits 15 := by
  simp +decide only [lead, branch, executeOps, List.cons_append, List.nil_append,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    hp, BitVec.ofNat_add_ofNat]

theorem setup_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom setup state).heap = state.heap := rfl

theorem setup_width {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom setup state).register .total = state.register .total := rfl

theorem setup_mask {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom setup state).register .flag = state.register .flag := rfl

set_option maxRecDepth 10000 in
theorem setup_address {bits : Nat} (rom : PhysicalROM) (state : WordState bits)
    (N q t tool : Nat) (hb : 8 ≤ bits)
    (hN : (rom.words .input).getD 0 0 = N) (hq : (rom.words .input).getD 1 0 = q)
    (ht : (state.heap (BitVec.ofNat bits 0)).toNat = t)
    (hlabel : (state.register .value).toNat = tool + 1)
    (hN1 : Fits bits (N + 1)) (hq2 : Fits bits (q + 2))
    (ht1 : Fits bits (t + 1)) (hprod : Fits bits ((N + 1) * (q + 2))) :
    (executeOps rom setup state).register .address = BitVec.ofNat bits (tableWords N q t + tool) := by
  have hbits : bits < 2 ^ bits := Nat.lt_two_pow_self
  have hzero : 0 < 2 ^ bits := by omega
  have hone : 1 < 2 ^ bits := by omega
  have htword : state.heap (BitVec.ofNat bits 0) = BitVec.ofNat bits t := by
    have he := congrArg (BitVec.ofNat bits) ht
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  simp +decide only [setup, executeOps, packingExecuteOp, wordOp, wordInstruction,
    Function.update_apply, ↓reduceIte, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hzero,
    Nat.mod_eq_of_lt hone, hN, hq, htword, hlabel,
    BitVec.ofNat_add_ofNat, arithmetic_multiply, Nat.mod_eq_of_lt hN1,
    Nat.mod_eq_of_lt hq2, Nat.mod_eq_of_lt ht1, Nat.mod_eq_of_lt hprod,
    Nat.add_sub_cancel, tableWords, cells]

end PaperProofs.Structure.LaminarTree.PSTRLeafUsed
