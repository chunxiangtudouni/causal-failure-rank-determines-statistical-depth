module

public import Common.PSTR_HD_TableHeads_002
public import PaperProofs.Structure.RawIncidenceScanSafety
public import PaperProofs.Structure.PackingWordRefinement
public import PaperProofs.Structure.PackingExecutionCost
import Mathlib.Tactic.IntervalCases

/-! Fixed zero-tool head extractor. It reads only original query ROM and
writes the original output format in one actual looping program. -/

@[expose] public section

namespace PaperProofs.Structure.LaminarTree.PSTRZeroHeads

open IndexedRAM IndexedClosureRAM AlgorithmClaims CompactControllerClaims
open PackingMachine RawIncidenceLaminarRAM
open PaperProofs.Common.Native.CompactPrice

/-- q=0 has depth one on a nonempty schedule and infinite terminal depth. -/
def depthWord (N : Nat) : Nat := if N = 0 then 2 else 1

def startBlock : List PackingOp :=
  [.base (.base (.constant .address 0)),
   .base (.base (.loadROM .input .old .address)),
   .base (.base (.constant .index 6)),
   .base (.base (.constant .fresh 1)),
   .base (.base (.constant .value 2)),
   .base (.base (.select .value .old .fresh .value)),
   .base (.base (.storeHeap .index .value)),
   .base (.base (.constant .address 7)),
   .base (.base (.storeHeap .address .old)),
   .base (.base (.constant .value 0)),
   .base (.base (.constant .address 8)),
   .base (.base (.constant .total 60))]

def testLead : List PackingOp :=
  [.base (.subtract .flag .old .value), .base (.base (.constant .total 105))]

def bodyLead : List PackingOp :=
  [.base (.base (.storeHeap .address .value)),
   .base (.base (.add .address .address .fresh)),
   .base (.base (.add .value .value .fresh)),
   .base (.base (.constant .flag 0)),
   .base (.base (.constant .total 60))]

def finishBlock : List PackingOp :=
  [.base (.base (.constant .address 4)), .base (.base (.storeHeap .address .old))]

def program : List PackingOp := startBlock ++ testLead ++ [.jumpIfZero .flag .total] ++
  bodyLead ++ [.jumpIfZero .flag .total] ++ finishBlock

theorem program_length : program.length = 23 := rfl

def initialNat (heap : Nat → Nat) : NatState := ⟨fun _ => 0, heap, 0, false⟩

def outputHeap (heap : Nat → Nat) (N k : Nat) (address : Nat) : Nat :=
  if address - 8 < k ∧ 8 ≤ address then address - 8
  else Function.update (Function.update heap 6 (depthWord N)) 7 N address

def stateAt (heap : Nat → Nat) (N k flag total pc : Nat) : NatState :=
  { register := fun reg => match reg with
      | .address => 8 + k | .index => 6 | .value => k | .total => total
      | .old => N | .fresh => 1 | .flag => flag
    heap := outputHeap heap N k
    pc := pc
    halted := false }

def loopState (heap : Nat → Nat) (N k : Nat) : NatState := stateAt heap N k 0 60 60

theorem state_ext {left right : NatState}
    (hr : ∀ reg, left.register reg = right.register reg)
    (hh : ∀ address, left.heap address = right.heap address)
    (hp : left.pc = right.pc) (ha : left.halted = right.halted) : left = right := by
  have hr' : left.register = right.register := funext hr
  have hh' : left.heap = right.heap := funext hh
  cases left
  cases right
  simp only at hr' hh' hp ha
  subst_vars
  rfl

theorem outputHeap_succ (heap : Nat → Nat) (N k : Nat) :
    Function.update (outputHeap heap N k) (8 + k) k = outputHeap heap N (k + 1) := by
  funext address
  by_cases he : address = 8 + k
  · subst address
    simp [outputHeap]
  · rw [Function.update_of_ne he]
    unfold outputHeap
    have heq : (address - 8 < k ∧ 8 ≤ address) ↔ (address - 8 < k + 1 ∧ 8 ≤ address) := by omega
    simp only [heq]

theorem run_start (rom : PhysicalROM) (heap : Nat → Nat) (N : Nat)
    (hN : rom.semantic.read .input 0 = N) :
    natRun rom program 12 (initialNat heap) = loopState heap N 0 := by
  have hr := natRun_of_straight_segment rom program startBlock 0 (by decide)
    (by intro i hi; change i < 12 at hi; interval_cases i <;> rfl)
    (by simp [startBlock, NoJump]) (initialNat heap) rfl rfl
  change natRun rom program startBlock.length (initialNat heap) = _
  rw [hr]
  apply state_ext
  · intro reg
    cases reg <;> simp +decide [runOps, startBlock, initialNat, loopState, stateAt,
      natExecuteOp, Op.execute, Instruction.execute, hN]
  · intro address
    simp +decide [runOps, startBlock, initialNat, loopState, stateAt, outputHeap,
      depthWord, natExecuteOp, Op.execute, Instruction.execute, hN]
  · rfl
  · rfl

theorem run_test (rom : PhysicalROM) (heap : Nat → Nat) (N k : Nat) :
    natRun rom program 3 (loopState heap N k) =
      stateAt heap N k (N - k) 105 (if N - k = 0 then 105 else 75) := by
  have hr := natRun_of_segment_last rom program testLead (.jumpIfZero .flag .total) 12
    (by decide) (by intro i hi; change i < 2 at hi; interval_cases i <;> rfl) rfl
    (by simp [testLead, NoJump]) (loopState heap N k) rfl rfl
  change natRun rom program (testLead.length + 1) (loopState heap N k) = _
  rw [hr]
  apply state_ext
  · intro reg
    cases reg <;> simp +decide [runOps, testLead, loopState, stateAt,
      natExecuteOp, Op.execute, Instruction.execute]
  · intro address
    rfl
  · simp +decide [runOps, testLead, loopState, stateAt, natExecuteOp, Op.execute, Instruction.execute]
  · rfl

theorem run_body (rom : PhysicalROM) (heap : Nat → Nat) (N k : Nat) :
    natRun rom program 6 (stateAt heap N k (N - k) 105 75) = loopState heap N (k + 1) := by
  have hr := natRun_of_segment_last rom program bodyLead (.jumpIfZero .flag .total) 15
    (by decide) (by intro i hi; change i < 5 at hi; interval_cases i <;> rfl) rfl
    (by simp [bodyLead, NoJump]) (stateAt heap N k (N - k) 105 75) rfl rfl
  change natRun rom program (bodyLead.length + 1) (stateAt heap N k (N - k) 105 75) = _
  rw [hr]
  apply state_ext
  · intro reg
    cases reg <;> simp +decide [runOps, bodyLead, loopState, stateAt,
      natExecuteOp, Op.execute, Instruction.execute, Nat.add_assoc]
  · intro address
    change Function.update (outputHeap heap N k) (8 + k) k address = _
    rw [outputHeap_succ]
    rfl
  · rfl
  · rfl

theorem run_iteration (rom : PhysicalROM) (heap : Nat → Nat) (N k : Nat) (hk : k < N) :
    natRun rom program 9 (loopState heap N k) = loopState heap N (k + 1) := by
  rw [show 9 = 3 + 6 from rfl, natRun_add, run_test]
  have hn : N - k ≠ 0 := by omega
  rw [ite_eq_right hn]
  exact run_body rom heap N k

theorem run_iterations (rom : PhysicalROM) (heap : Nat → Nat) (N k : Nat) (hk : k ≤ N) :
    natRun rom program (9 * k) (loopState heap N 0) = loopState heap N k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Nat.mul_succ, natRun_add, ih (by omega)]
    exact run_iteration rom heap N k (by omega)

def finalState (heap : Nat → Nat) (N : Nat) : NatState :=
  { register := fun reg => match reg with
      | .address => 4 | .index => 6 | .value => N | .total => 105
      | .old => N | .fresh => 1 | .flag => 0
    heap := Function.update (outputHeap heap N N) 4 N
    pc := 115
    halted := true }

theorem run_exit (rom : PhysicalROM) (heap : Nat → Nat) (N : Nat) :
    natRun rom program 6 (loopState heap N N) = finalState heap N := by
  rw [show 6 = 3 + (2 + 1) from rfl, natRun_add, run_test]
  simp only [Nat.sub_self, ↓reduceIte]
  have hr := natRun_of_straight_segment rom program finishBlock 21 (by decide)
    (by intro i hi; change i < 2 at hi; interval_cases i <;> rfl)
    (by simp [finishBlock, NoJump]) (stateAt heap N N 0 105 105) rfl rfl
  rw [natRun_add, show 2 = finishBlock.length from rfl, hr]
  rw [show 1 = 0 + 1 from rfl, natRun_succ, natRun]
  rw [natStep_halt rom program _ rfl rfl]
  apply state_ext
  · intro reg
    cases reg <;> simp +decide [runOps, finishBlock, stateAt, finalState,
      natExecuteOp, Op.execute, Instruction.execute]
  · intro address
    rfl
  · rfl
  · rfl

theorem run_complete (rom : PhysicalROM) (heap : Nat → Nat) (N : Nat)
    (hN : rom.semantic.read .input 0 = N) :
    natRun rom program (9 * N + 18) (initialNat heap) = finalState heap N := by
  rw [show 9 * N + 18 = 12 + (9 * N + 6) by omega, natRun_add, run_start rom heap N hN,
    natRun_add, run_iterations rom heap N N le_rfl, run_exit]

end PaperProofs.Structure.LaminarTree.PSTRZeroHeads

