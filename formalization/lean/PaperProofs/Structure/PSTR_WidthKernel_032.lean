module

public import PaperProofs.Structure.PSTR_WidthActive_031
public import PaperProofs.Structure.PSTR_HD_WordSegments_014

/-! The same twelve width-loop operations at a STATIC containing-code
position. Only its two literal jump targets are relocated. Real Word segment
execution is used; the runtime q and width answer are not code parameters. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRWidthKernel

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open PSTRRuntimeWidth

def testLeadAt (start : Nat) : List PackingOp :=
  [.base (.subtract .flag .old .value),
   .base (.base (.constant .address (5 * (start + 12))))]

def testAt (start : Nat) : List PackingOp := testLeadAt start ++ [.jumpIfZero .flag .address]

def bodyLeadAt (start : Nat) : List PackingOp :=
  [.base (.base (.add .value .value .value)),
   .base (.base (.add .total .total .index)),
   .base (.base (.constant .address (5 * (start + 4)))),
   .base (.base (.constant .flag 0))]

def bodyAt (start : Nat) : List PackingOp := bodyLeadAt start ++ [.jumpIfZero .flag .address]

def kernel (start : Nat) : List PackingOp := initCode ++ testAt start ++ bodyAt start

theorem kernel_length (start : Nat) : (kernel start).length = 12 := rfl
theorem testLead_length (start : Nat) : (testLeadAt start).length = 2 := rfl
theorem bodyLead_length (start : Nat) : (bodyLeadAt start).length = 4 := rfl
theorem kernel_zero : kernel 0 = program := rfl

theorem init_straight : StraightProgram initCode := by simp [StraightProgram, StraightOp, initCode]
theorem test_straight (start : Nat) : StraightProgram (testLeadAt start) := by
  simp [StraightProgram, StraightOp, testLeadAt]
theorem body_straight (start : Nat) : StraightProgram (bodyLeadAt start) := by
  simp [StraightProgram, StraightOp, bodyLeadAt]

structure Data {bits : Nat} (q k : Nat) (state : WordState bits) : Prop where
  fresh : state.register .fresh = BitVec.ofNat bits q
  old : state.register .old = BitVec.ofNat bits (q + 1)
  power : state.register .value = BitVec.ofNat bits (2 ^ k)
  counter : state.register .total = BitVec.ofNat bits k
  one : state.register .index = BitVec.ofNat bits 1

structure Ready {bits : Nat} (q k start : Nat) (state : WordState bits) : Prop extends Data q k state where
  pc : state.pc = BitVec.ofNat bits (5 * (start + 4))
  active : state.halted = false

theorem init_data {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : WordState bits)
    (hf : (state.register .fresh).toNat = q) : Data q 0 (executeOps rom initCode state) := by
  have hfword : state.register .fresh = BitVec.ofNat bits q := by
    have he := congrArg (BitVec.ofNat bits) hf
    simpa only [BitVec.ofNat_toNat, BitVec.setWidth_eq] using he
  constructor <;>
    simp +decide only [initCode, executeOps, packingExecuteOp, wordOp, wordInstruction,
      Function.update_apply, ↓reduceIte, hfword, BitVec.ofNat_add_ofNat, Nat.pow_zero]

theorem init_ready {bits : Nat} (rom : PhysicalROM) (q start : Nat) (state : WordState bits)
    (hf : (state.register .fresh).toNat = q)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    Ready q 0 start (executeOps rom initCode state) := by
  refine ⟨init_data rom q state hf, ?_, ?_⟩
  · rw [executeOps_pc rom initCode state init_straight, hp, BitVec.ofNat_add_ofNat]
    exact congrArg (BitVec.ofNat bits) (show 5 * start + 5 * 4 = 5 * (start + 4) by omega)
  · rw [executeOps_halted, ha]

theorem init_heap {bits : Nat} (rom : PhysicalROM) (state : WordState bits) :
    (executeOps rom initCode state).heap = state.heap := rfl

theorem test_data {bits : Nat} (rom : PhysicalROM) (q k start : Nat) (state : WordState bits)
    (hs : Data q k state) : Data q k (executeOps rom (testAt start) state) :=
  ⟨hs.fresh, hs.old, hs.power, hs.counter, hs.one⟩

theorem test_heap {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits) :
    (executeOps rom (testAt start) state).heap = state.heap := rfl

theorem test_pc {bits : Nat} (rom : PhysicalROM) (q k start : Nat) (state : WordState bits)
    (hs : Ready q k start state) (hq : Fits bits (q + 1)) (hw : Fits bits (2 ^ k)) :
    (executeOps rom (testAt start) state).pc =
      if q + 1 - 2 ^ k = 0 then BitVec.ofNat bits (5 * (start + 12))
      else BitVec.ofNat bits (5 * (start + 7)) := by
  have hd : Fits bits (q + 1 - 2 ^ k) := (Nat.sub_le _ _).trans_lt hq
  have hpc : 5 * (start + 4) + 5 + 5 + 5 = 5 * (start + 7) := by omega
  simp +decide only [testAt, testLeadAt, List.cons_append, List.nil_append, executeOps,
    packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
    hs.old, hs.power, hs.pc, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hq,
    Nat.mod_eq_of_lt hw, Nat.mod_eq_of_lt hd, BitVec.ofNat_add_ofNat, hpc]

theorem body_ready {bits : Nat} (rom : PhysicalROM) (q k start : Nat) (state : WordState bits)
    (hs : Data q k state) (ha : state.halted = false) :
    Ready q (k + 1) start (executeOps rom (bodyAt start) state) := by
  have hpow : 2 ^ k + 2 ^ k = 2 ^ (k + 1) := by rw [Nat.pow_succ, Nat.mul_two]
  refine ⟨?_, ?_, ?_⟩
  · constructor <;>
      simp +decide only [bodyAt, bodyLeadAt, List.cons_append, List.nil_append, executeOps,
        packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
        hs.fresh, hs.old, hs.power, hs.counter, hs.one, BitVec.ofNat_add_ofNat, hpow]
  · simp +decide only [bodyAt, bodyLeadAt, List.cons_append, List.nil_append, executeOps,
      packingExecuteOp, wordOp, wordInstruction, Function.update_apply, ↓reduceIte,
      BitVec.toNat_ofNat, Nat.zero_mod]
  · rw [executeOps_halted, ha]

theorem body_heap {bits : Nat} (rom : PhysicalROM) (start : Nat) (state : WordState bits) :
    (executeOps rom (bodyAt start) state).heap = state.heap := rfl

structure Contains (whole : List PackingOp) (start : Nat) : Prop where
  bound : start + (kernel start).length ≤ whole.length
  code : ∀ i (hi : i < (kernel start).length), whole[start + i]'(by omega) = (kernel start)[i]

theorem kernel_init (start i : Nat) (hi : i < initCode.length) :
    (kernel start)[i]'(by rw [kernel_length]; change i < 4 at hi; omega) = initCode[i] := by
  change i < 4 at hi
  interval_cases i <;> rfl

theorem kernel_test (start i : Nat) (hi : i < (testLeadAt start).length) :
    (kernel start)[4 + i]'(by rw [kernel_length]; rw [testLead_length] at hi; omega) =
      (testLeadAt start)[i] := by
  change i < 2 at hi
  interval_cases i <;> rfl

theorem kernel_body (start i : Nat) (hi : i < (bodyLeadAt start).length) :
    (kernel start)[7 + i]'(by rw [kernel_length]; rw [bodyLead_length] at hi; omega) =
      (bodyLeadAt start)[i] := by
  change i < 4 at hi
  interval_cases i <;> rfl

theorem init_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * start)) (ha : state.halted = false) :
    packingRun rom whole 4 state = executeOps rom initCode state := by
  apply PSTRWordSegments.straight_segment rom whole initCode start ?_ ?_ init_straight hw hpcfit state hp ha
  · have hb := hc.bound
    rw [kernel_length] at hb
    change start + 4 ≤ whole.length
    omega
  · intro i hi
    exact (hc.code i (by rw [kernel_length]; change i < 4 at hi; omega)).trans (kernel_init start i hi)

theorem test_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (start + 4))) (ha : state.halted = false) :
    packingRun rom whole 3 state = executeOps rom (testAt start) state := by
  rw [show 3 = (testLeadAt start).length + 1 from rfl,
    PSTRWordSegments.segment_last rom whole (testLeadAt start) (.jumpIfZero .flag .address) (start + 4)
      ?_ ?_ ?_ (test_straight start) hw hpcfit state hp ha, testAt, executeOps_append]
  · rfl
  · have hb := hc.bound
    rw [kernel_length] at hb
    change start + 4 + 2 + 1 ≤ whole.length
    omega
  · intro i hi
    have hh := hc.code (4 + i) (by rw [kernel_length]; rw [testLead_length] at hi; omega)
    simpa only [Nat.add_assoc] using hh.trans (kernel_test start i hi)
  · have hh := hc.code 6 (by rw [kernel_length]; decide)
    have he : (kernel start)[6]'(by rw [kernel_length]; decide) = .jumpIfZero .flag .address := rfl
    simpa only [testLead_length, Nat.add_assoc] using hh.trans he

theorem body_run {bits : Nat} (rom : PhysicalROM) (whole : List PackingOp) (start : Nat)
    (hc : Contains whole start) (hw : WordsFit bits (packingCode whole))
    (hpcfit : Fits bits (5 * whole.length)) (state : WordState bits)
    (hp : state.pc = BitVec.ofNat bits (5 * (start + 7))) (ha : state.halted = false) :
    packingRun rom whole 5 state = executeOps rom (bodyAt start) state := by
  rw [show 5 = (bodyLeadAt start).length + 1 from rfl,
    PSTRWordSegments.segment_last rom whole (bodyLeadAt start) (.jumpIfZero .flag .address) (start + 7)
      ?_ ?_ ?_ (body_straight start) hw hpcfit state hp ha, bodyAt, executeOps_append]
  · rfl
  · have hb := hc.bound
    rw [kernel_length] at hb
    change start + 7 + 4 + 1 ≤ whole.length
    omega
  · intro i hi
    have hh := hc.code (7 + i) (by rw [kernel_length]; rw [bodyLead_length] at hi; omega)
    simpa only [Nat.add_assoc] using hh.trans (kernel_body start i hi)
  · have hh := hc.code 11 (by rw [kernel_length]; decide)
    have he : (kernel start)[11]'(by rw [kernel_length]; decide) = .jumpIfZero .flag .address := rfl
    simpa only [bodyLead_length, Nat.add_assoc] using hh.trans he

end PaperProofs.Structure.LaminarTree.PSTRWidthKernel
