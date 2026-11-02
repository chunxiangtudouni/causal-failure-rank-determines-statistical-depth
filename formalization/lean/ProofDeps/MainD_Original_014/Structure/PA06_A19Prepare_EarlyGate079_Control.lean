module

public import Structure.PA06_A19Prepare_EarlyGate079_NatEntry

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED finite control certificate for the ORIGINAL checker after
its first outer test. It makes the actual no-return-to-first10 property a
proved internal obligation, rather than inferring it from Fetched alone.
The fixed126-op checker is the only program inspected by this module. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims RawIncidenceLaminarRAM

def jumpTarget : Nat → Option (Register × Nat)
  | 16 => some (.flag, 126)
  | 26 => some (.flag, 117)
  | 45 => some (.flag, 92)
  | 91 => some (.flag, 39)
  | 95 => some (.total, 108)
  | 99 => some (.total, 108)
  | 103 => some (.total, 108)
  | 107 => some (.flag, 126)
  | 116 => some (.flag, 20)
  | 125 => some (.flag, 10)
  | _ => none

def Control (index : Nat) (state : NatState) : Prop :=
  state.pc = 5 * index ∧
    match jumpTarget index with
    | none => True
    | some (_, target) => state.register .index = 5 * target

def AboveHead (state : NatState) : Prop :=
  ∃ index, 10 ≤ index ∧ index ≤ 126 ∧ Control index state

private theorem noJump_of_none (index : Nat) (lo : 10 ≤ index) (hi : index < 126)
    (absent : jumpTarget index = none) :
    NoJump (checker[index]'(by rw [checker_length]; exact hi)) := by
  interval_cases index <;> simp [jumpTarget] at absent
  all_goals
    change True
    exact True.intro

private theorem branch_shape (index : Nat) (lo : 10 ≤ index) (hi : index < 126)
    (condition : Register) (target : Nat) (found : jumpTarget index = some (condition, target)) :
    checker[index]'(by rw [checker_length]; exact hi) = .jumpIfZero condition .index ∧
      10 ≤ target ∧ target ≤ 126 ∧ jumpTarget target = none ∧ jumpTarget (index + 1) = none := by
  interval_cases index <;> simp [jumpTarget] at found
  all_goals rcases found with ⟨rfl, rfl⟩
  all_goals exact ⟨rfl, by decide, by decide, rfl, rfl⟩

private theorem straight_control (rom : PhysicalROM) (index : Nat) (lo : 10 ≤ index) (hi : index < 126)
    (state : NatState) (control : Control index state)
    (straight : NoJump (checker[index]'(by rw [checker_length]; exact hi))) :
    Control (index + 1) (natExecuteOp rom (checker[index]'(by rw [checker_length]; exact hi)) state) := by
  constructor
  · rw [natExecuteOp_pc_noJump rom _ state straight, control.1]
    omega
  · interval_cases index <;> simp only [jumpTarget]
    all_goals rfl

private theorem branch_control (rom : PhysicalROM) (index : Nat) (lo : 10 ≤ index) (hi : index < 126)
    (state : NatState) (control : Control index state)
    (condition : Register) (target : Nat) (found : jumpTarget index = some (condition, target)) :
    AboveHead (natExecuteOp rom (checker[index]'(by rw [checker_length]; exact hi)) state) := by
  obtain ⟨code, targetLo, targetHi, targetPlain, nextPlain⟩ := branch_shape index lo hi condition target found
  have stored : state.register .index = 5 * target := by
    simpa only [Control, found] using control.2
  rw [code]
  by_cases zero : state.register condition = 0
  · refine ⟨target, targetLo, targetHi, ?_, ?_⟩
    · simp only [natExecuteOp, zero, ite_true, stored]
    · simp only [targetPlain]
  · refine ⟨index + 1, by omega, by omega, ?_, ?_⟩
    · simp only [natExecuteOp, zero, ite_false, control.1]
      omega
    · simp only [nextPlain]

theorem above_head_step (rom : PhysicalROM) (state : NatState) (point : AboveHead state) :
    AboveHead (natStep rom checker state) := by
  by_cases stopped : state.halted = true
  · simpa only [natStep, stopped, ite_true] using point
  have active : state.halted = false := by cases flag : state.halted <;> simp_all
  obtain ⟨index, lo, hi, control⟩ := point
  by_cases last : index = 126
  · subst index
    have pc : state.pc = 5 * checker.length := by simpa only [checker_length] using control.1
    rw [natStep_halt rom checker state pc active]
    exact ⟨126, by decide, by decide, control⟩
  have strict : index < 126 := by omega
  rw [natStep_of_index rom checker state index (by rw [checker_length]; exact strict) control.1 active]
  cases found : jumpTarget index with
  | none =>
      exact ⟨index + 1, by omega, by omega,
        straight_control rom index lo strict state control (noJump_of_none index lo strict found)⟩
  | some pair =>
      exact branch_control rom index lo strict state control pair.1 pair.2 found

theorem above_head_run (rom : PhysicalROM) (state : NatState) (point : AboveHead state) (count : Nat) :
    AboveHead (natRun rom checker count state) := by
  induction count with
  | zero => exact point
  | succ count ih =>
      rw [natRun_succ]
      exact above_head_step rom _ ih

theorem above_head_pc (state : NatState) (point : AboveHead state) : 50 ≤ state.pc := by
  obtain ⟨index, lo, _hi, pc, _target⟩ := point
  omega

theorem above_head_of_seventeen_pc (N : Nat) (state : NatState)
    (pc : state.pc = if N = 0 then 630 else 85) : AboveHead state := by
  by_cases zero : N = 0
  · refine ⟨126, by decide, by decide, ?_, by trivial⟩
    simpa only [zero, ite_true] using pc
  · refine ⟨17, by decide, by decide, ?_, by trivial⟩
    simpa only [zero, ite_false] using pc

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079
