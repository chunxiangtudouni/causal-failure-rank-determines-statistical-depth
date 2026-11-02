module

public import PaperProofs.Structure.PSTR_RuntimeWidth_005
public import PaperProofs.Structure.RawIncidenceScanSafety
public import PaperProofs.Structure.PackingWordRefinement
public import PaperProofs.Structure.PackingExecutionCost
import Mathlib.Tactic.IntervalCases

/-! Prefix numeric safety for the actual runtime-width loop. Bounds refer
to the runtime dimension and registers, never a precomputed answer input. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimeWidthWord

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open RawIncidenceLaminarRAM (runOps NoJump natRun_of_straight_segment)
open RawIncidenceScanSafety (natRun_segment_prefix)
open PSTRRuntimeWidth

theorem width_le (q : Nat) : CapacityBits.width q ≤ q + 1 :=
  Nat.clog_le_of_le_pow (show q + 1 ≤ 2 ^ (q + 1) from Nat.lt_two_pow_self.le)

theorem power_le (q : Nat) : 2 ^ CapacityBits.width q ≤ 2 * (q + 1) := by
  by_cases hq : q = 0
  · subst q
    simp [CapacityBits.width_zero]
  · have hp : 0 < CapacityBits.width q := Nat.pos_of_ne_zero (by
      intro hz
      exact hq ((CapacityBits.width_eq_zero_iff q).mp hz))
    have hm : 2 ^ (CapacityBits.width q - 1) < q + 1 :=
      Nat.pow_pred_clog_lt_self (by decide) (show 1 < q + 1 by omega)
    have he : CapacityBits.width q = (CapacityBits.width q - 1) + 1 := by omega
    rw [he, Nat.pow_succ]
    omega

def Point (bits : Nat) (state : NatState) : Prop :=
  RegistersFit bits state ∧ state.pc ≤ 60 ∧ state.pc % 5 = 0

theorem code_fit {bits : Nat} (hb : 8 ≤ bits) : WordsFit bits (packingCode program) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  intro value hv
  simp [packingCode, program, initCode, testCode, testLead, bodyCode, bodyLead,
    PackingOp.encode, Op.encodeWords, Instruction.encodeWords,
    Register.word, Region.word, haltWords] at hv
  unfold Fits
  omega

theorem init_prefix {bits : Nat} (rom : PhysicalROM) (q : Nat) (state : NatState)
    (hb : 8 ≤ bits) (hf : state.register .fresh = q) (hp : state.pc = 0)
    (ha : state.halted = false) (hr : RegistersFit bits state)
    (hq : Fits bits (q + 1)) (count : Nat) (hc : count ≤ 4) :
    Point bits (natRun rom program count state) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have hlen : (initCode.take count).length = count := List.length_take_of_le hc
  have hcode : ∀ position (hposition : position < (initCode.take count).length),
      program[0 + position]'(by
        rw [program_length]
        rw [hlen] at hposition
        omega) = (initCode.take count)[position] := by
    intro position hposition
    have hl : position < 4 := by
      rw [hlen] at hposition
      omega
    rw [List.getElem_take]
    interval_cases position <;> rfl
  have hrun : natRun rom program count state = runOps rom (initCode.take count) state := by
    have hl : (initCode.take count).length = count := List.length_take_of_le hc
    simpa only [hl] using natRun_of_straight_segment rom program _ 0 (by rw [hl, program_length]; omega)
      hcode (by
        intro op ho
        exact (show ∀ op ∈ initCode, NoJump op by simp [initCode, NoJump]) op (List.mem_of_mem_take ho)) state hp ha
  rw [hrun]
  constructor
  · intro reg
    have hreg := hr reg
    cases reg <;> interval_cases count <;>
      simp_all +decide [RegistersFit, Fits, runOps, initCode, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · interval_cases count <;>
      simp_all +decide [runOps, initCode, natExecuteOp, Op.execute, Instruction.execute]

theorem test_prefix {bits : Nat} (rom : PhysicalROM) (q k : Nat) (state : NatState)
    (hb : 8 ≤ bits) (hs : Ready q k state) (hr : RegistersFit bits state)
    (hq : Fits bits (q + 1)) (count : Nat) (hc : count ≤ 3) :
    Point bits (natRun rom program count state) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have hcode : ∀ position (hposition : position < testLead.length),
      program[4 + position]'(by rw [program_length]; change position < 2 at hposition; omega) =
        testLead[position] := by
    intro position hposition
    change position < 2 at hposition
    interval_cases position <;> rfl
  rw [natRun_segment_prefix rom program testLead (.jumpIfZero .flag .address) 4
    (by decide) hcode (by rfl) (by simp [testLead, NoJump]) state hs.pc hs.active count hc]
  constructor
  · intro reg
    have hreg := hr reg
    cases reg <;> interval_cases count <;>
      simp_all +decide [RegistersFit, Fits, runOps, testLead, natExecuteOp, Op.execute, Instruction.execute, hs.old]
    all_goals omega
  · interval_cases count <;>
      simp_all +decide [runOps, testLead, natExecuteOp, Op.execute, Instruction.execute, hs.pc]
    all_goals split <;> decide

theorem body_prefix {bits : Nat} (rom : PhysicalROM) (state : NatState)
    (hb : 8 ≤ bits) (hp : state.pc = 35) (ha : state.halted = false)
    (hr : RegistersFit bits state)
    (hv : Fits bits (state.register .value + state.register .value))
    (ht : Fits bits (state.register .total + state.register .index))
    (count : Nat) (hc : count ≤ 5) :
    Point bits (natRun rom program count state) := by
  have hpow : 256 ≤ 2 ^ bits :=
    (show 2 ^ 8 ≤ 2 ^ bits from Nat.pow_le_pow_right (by decide) hb)
  have hcode : ∀ position (hposition : position < bodyLead.length),
      program[7 + position]'(by rw [program_length]; change position < 4 at hposition; omega) =
        bodyLead[position] := by
    intro position hposition
    change position < 4 at hposition
    interval_cases position <;> rfl
  rw [natRun_segment_prefix rom program bodyLead (.jumpIfZero .flag .address) 7
    (by decide) hcode (by rfl) (by simp [bodyLead, NoJump]) state hp ha count hc]
  constructor
  · intro reg
    have hreg := hr reg
    cases reg <;> interval_cases count <;>
      simp_all +decide [RegistersFit, Fits, runOps, bodyLead, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · interval_cases count <;>
      simp_all +decide [runOps, bodyLead, natExecuteOp, Op.execute, Instruction.execute]

theorem loop_prefix {bits : Nat} (rom : PhysicalROM) (q k : Nat) (state : NatState)
    (hb : 8 ≤ bits) (hs : Ready q k state) (hr : RegistersFit bits state)
    (hq : Fits bits (q + 1)) (hpower : Fits bits (2 ^ CapacityBits.width q))
    (hk : k < CapacityBits.width q) (count : Nat) (hc : count ≤ 8) :
    Point bits (natRun rom program count state) := by
  by_cases ht : count ≤ 3
  · exact test_prefix rom q k state hb hs hr hq count ht
  · have he : count = 3 + (count - 3) := by omega
    rw [he, natRun_add]
    let tested := natRun rom program 3 state
    have htest := test_prefix rom q k state hb hs hr hq 3 le_rfl
    have hlt : 2 ^ k < q + 1 := Nat.pow_lt_of_lt_clog hk
    have hne : q + 1 - 2 ^ k ≠ 0 := by omega
    have hpc : tested.pc = 35 := by
      rw [show tested = runOps rom testCode state from test_run rom state hs.pc hs.active]
      simp +decide [testCode, testLead, runOps, natExecuteOp, Op.execute,
        Instruction.execute, hs.old, hs.power, hs.pc, hne]
    have ha : tested.halted = false := by
      rw [show tested = runOps rom testCode state from test_run rom state hs.pc hs.active,
        RawIncidenceLaminarRAM.runOps_halted, hs.active]
    have hvalue : tested.register .value = 2 ^ k := by
      rw [show tested = runOps rom testCode state from test_run rom state hs.pc hs.active]
      simpa +decide [testCode, testLead, runOps, natExecuteOp, Op.execute, Instruction.execute] using hs.power
    have htotal : tested.register .total = k := by
      rw [show tested = runOps rom testCode state from test_run rom state hs.pc hs.active]
      simpa +decide [testCode, testLead, runOps, natExecuteOp, Op.execute, Instruction.execute] using hs.counter
    have hone : tested.register .index = 1 := by
      rw [show tested = runOps rom testCode state from test_run rom state hs.pc hs.active]
      simpa +decide [testCode, testLead, runOps, natExecuteOp, Op.execute, Instruction.execute] using hs.one
    apply body_prefix rom tested hb hpc ha htest.1 ?_ ?_ (count - 3) (by omega)
    · rw [hvalue]
      have hm : 2 ^ (k + 1) ≤ 2 ^ CapacityBits.width q := Nat.pow_le_pow_right (by decide) hk
      have heq : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by rw [Nat.pow_succ, Nat.mul_two]
      rw [heq] at hm
      exact hm.trans_lt hpower
    · rw [htotal, hone]
      exact (show k + 1 ≤ q + 1 from (Nat.succ_le_of_lt hk).trans (width_le q)).trans_lt hq

theorem loop_all_prefixes {bits : Nat} (rom : PhysicalROM) (q k count : Nat) (state : NatState)
    (hb : 8 ≤ bits) (hs : Ready q k state) (hr : RegistersFit bits state)
    (hq : Fits bits (q + 1)) (hpower : Fits bits (2 ^ CapacityBits.width q))
    (hk : k + count ≤ CapacityBits.width q) :
    ∀ clock ≤ 8 * count, Point bits (natRun rom program clock state) := by
  induction count generalizing k state with
  | zero =>
    intro clock hc
    have he : clock = 0 := by omega
    subst clock
    exact ⟨hr, by change state.pc ≤ 60; rw [hs.pc]; decide,
      by change state.pc % 5 = 0; rw [hs.pc]⟩
  | succ count ih =>
    intro clock hc
    by_cases hfirst : clock ≤ 8
    · exact loop_prefix rom q k state hb hs hr hq hpower (by omega) clock hfirst
    · have he : clock = 8 + (clock - 8) := by omega
      rw [he, natRun_add]
      have hn := (loop_step rom q k state hs (by omega)).1
      have hreg := (loop_prefix rom q k state hb hs hr hq hpower (by omega) 8 le_rfl).1
      exact ih (k + 1) (natRun rom program 8 state) hn hreg (by omega) (clock - 8) (by omega)

end PaperProofs.Structure.LaminarTree.PSTRRuntimeWidthWord
