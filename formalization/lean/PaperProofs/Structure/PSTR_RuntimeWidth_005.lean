module

public import PaperProofs.Structure.RawIncidenceLaminarRAM
public import PaperProofs.Structure.CapacityBits
import Mathlib.Tactic.IntervalCases

/-! One fixed ISA loop computes the packed scalar width from the runtime q.
The invariant is a proof predicate, not input data. No logarithm instruction,
generated code, precomputed width or execution trace is supplied to the RAM. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRRuntimeWidth

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
open RawIncidenceLaminarRAM (runOps NoJump natRun_of_straight_segment natRun_of_segment_last)

def initCode : List PackingOp :=
  [.base (.base (.constant .total 0)),
   .base (.base (.constant .value 1)),
   .base (.base (.constant .index 1)),
   .base (.base (.add .old .fresh .index))]

def testLead : List PackingOp :=
  [.base (.subtract .flag .old .value),
   .base (.base (.constant .address 60))]

def testCode : List PackingOp := testLead ++ [.jumpIfZero .flag .address]

def bodyLead : List PackingOp :=
  [.base (.base (.add .value .value .value)),
   .base (.base (.add .total .total .index)),
   .base (.base (.constant .address 20)),
   .base (.base (.constant .flag 0))]

def bodyCode : List PackingOp := bodyLead ++ [.jumpIfZero .flag .address]

def program : List PackingOp := initCode ++ testCode ++ bodyCode

theorem program_length : program.length = 12 := rfl

structure Ready (q k : Nat) (state : NatState) : Prop where
  fresh : state.register .fresh = q
  old : state.register .old = q + 1
  power : state.register .value = 2 ^ k
  counter : state.register .total = k
  one : state.register .index = 1
  pc : state.pc = 20
  active : state.halted = false

theorem init_run (rom : PhysicalROM) (state : NatState)
    (hp : state.pc = 0) (ha : state.halted = false) :
    natRun rom program 4 state = runOps rom initCode state := by
  apply natRun_of_straight_segment rom program initCode 0 (by decide) ?_ ?_ state hp ha
  · intro position hposition
    change position < 4 at hposition
    interval_cases position <;> rfl
  · simp [initCode, NoJump]

theorem test_run (rom : PhysicalROM) (state : NatState)
    (hp : state.pc = 20) (ha : state.halted = false) :
    natRun rom program 3 state = runOps rom testCode state := by
  exact natRun_of_segment_last rom program testLead (.jumpIfZero .flag .address) 4
    (by decide) (by
      intro position hposition
      change position < 2 at hposition
      interval_cases position <;> rfl) (by rfl)
    (by simp [testLead, NoJump]) state hp ha

theorem body_run (rom : PhysicalROM) (state : NatState)
    (hp : state.pc = 35) (ha : state.halted = false) :
    natRun rom program 5 state = runOps rom bodyCode state := by
  exact natRun_of_segment_last rom program bodyLead (.jumpIfZero .flag .address) 7
    (by decide) (by
      intro position hposition
      change position < 4 at hposition
      interval_cases position <;> rfl) (by rfl)
    (by simp [bodyLead, NoJump]) state hp ha

theorem init_ready (rom : PhysicalROM) (q : Nat) (state : NatState)
    (hf : state.register .fresh = q) (hp : state.pc = 0) (ha : state.halted = false) :
    Ready q 0 (natRun rom program 4 state) ∧
      (natRun rom program 4 state).heap = state.heap := by
  rw [init_run rom state hp ha]
  constructor
  · constructor <;>
      simp +decide [runOps, initCode, natExecuteOp, Op.execute, Instruction.execute, hf, hp, ha]
  · rfl

theorem loop_step (rom : PhysicalROM) (q k : Nat) (state : NatState)
    (hs : Ready q k state) (hk : k < CapacityBits.width q) :
    Ready q (k + 1) (natRun rom program 8 state) ∧
      (natRun rom program 8 state).heap = state.heap := by
  have hlt : 2 ^ k < q + 1 := Nat.pow_lt_of_lt_clog hk
  have hne : q + 1 - 2 ^ k ≠ 0 := by omega
  let tested := runOps rom testCode state
  have hpc : tested.pc = 35 := by
    simp +decide [tested, testCode, testLead, runOps, natExecuteOp, Op.execute,
      Instruction.execute, hs.old, hs.power, hs.pc, hne]
  have ha : tested.halted = false := by
    simp only [tested, RawIncidenceLaminarRAM.runOps_halted, hs.active]
  rw [show 8 = 3 + 5 from rfl, natRun_add, test_run rom state hs.pc hs.active,
    body_run rom tested hpc ha]
  constructor
  · constructor <;>
      simp +decide [tested, bodyCode, bodyLead, testCode, testLead, runOps,
        natExecuteOp, Op.execute, Instruction.execute, hs.fresh, hs.old,
        hs.power, hs.counter, hs.one, hs.pc, hs.active, hne, Nat.pow_succ, Nat.mul_two]
  · rfl

theorem loop_iterations (rom : PhysicalROM) (q k count : Nat) (state : NatState)
    (hs : Ready q k state) (hk : k + count ≤ CapacityBits.width q) :
    Ready q (k + count) (natRun rom program (8 * count) state) ∧
      (natRun rom program (8 * count) state).heap = state.heap := by
  induction count generalizing k state with
  | zero => simpa only [Nat.add_zero, Nat.mul_zero, natRun] using And.intro hs (rfl : state.heap = state.heap)
  | succ count ih =>
    obtain ⟨hnext, hframe⟩ := loop_step rom q k state hs (by omega)
    obtain ⟨hfinal, hlast⟩ := ih (k + 1) (natRun rom program 8 state) hnext (by omega)
    rw [show 8 * (count + 1) = 8 + 8 * count by omega, natRun_add]
    refine ⟨?_, hlast.trans hframe⟩
    simpa only [Nat.add_assoc, Nat.add_comm 1 count] using hfinal

theorem loop_finish (rom : PhysicalROM) (q : Nat) (state : NatState)
    (hs : Ready q (CapacityBits.width q) state) :
    let after := natRun rom program 4 state
    after.halted = true ∧ after.register .total = CapacityBits.width q ∧
      after.register .value = 2 ^ CapacityBits.width q ∧
      after.register .fresh = q ∧ after.heap = state.heap := by
  have hle : q + 1 ≤ 2 ^ CapacityBits.width q := Nat.le_pow_clog (by decide) (q + 1)
  have hz : q + 1 - 2 ^ CapacityBits.width q = 0 := Nat.sub_eq_zero_of_le hle
  let tested := runOps rom testCode state
  have hp : tested.pc = 5 * program.length := by
    simp +decide [tested, testCode, testLead, runOps, natExecuteOp, Op.execute,
      Instruction.execute, hs.old, hs.power, hz, program_length]
  have ha : tested.halted = false := by
    simp only [tested, RawIncidenceLaminarRAM.runOps_halted, hs.active]
  have hhalt : natRun rom program 1 tested = { tested with halted := true } :=
    natStep_halt rom program tested hp ha
  dsimp only
  rw [show 4 = 3 + 1 from rfl, natRun_add, test_run rom state hs.pc hs.active]
  rw [hhalt]
  simp +decide [tested, testCode, testLead, runOps, natExecuteOp, Op.execute,
    Instruction.execute, hs.counter, hs.power, hs.fresh]

theorem actual_nat_width (rom : PhysicalROM) (q : Nat) (state : NatState)
    (hf : state.register .fresh = q) (hp : state.pc = 0) (ha : state.halted = false) :
    let after := natRun rom program (8 * CapacityBits.width q + 8) state
    after.halted = true ∧ after.register .total = CapacityBits.width q ∧
      after.register .value = 2 ^ CapacityBits.width q ∧
      after.register .fresh = q ∧ after.heap = state.heap := by
  obtain ⟨hinit, hframe⟩ := init_ready rom q state hf hp ha
  obtain ⟨hloop, hloopFrame⟩ := loop_iterations rom q 0 (CapacityBits.width q)
    (natRun rom program 4 state) hinit (by omega)
  simp only [Nat.zero_add] at hloop
  have hfinal := loop_finish rom q _ hloop
  dsimp only at hfinal ⊢
  rw [show 8 * CapacityBits.width q + 8 = 4 + (8 * CapacityBits.width q + 4) by omega,
    natRun_add, natRun_add]
  exact ⟨hfinal.1, hfinal.2.1, hfinal.2.2.1, hfinal.2.2.2.1,
    hfinal.2.2.2.2.trans (hloopFrame.trans hframe)⟩

end PaperProofs.Structure.LaminarTree.PSTRRuntimeWidth
