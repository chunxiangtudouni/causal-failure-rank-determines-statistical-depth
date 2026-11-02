module

public import Structure.PA06_A19Prepare_EarlyGate079_NatEntry
public import PaperProofs.Structure.PA17_UniformGenerator_035p

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED same actual first8 Nat prefixes, including the real q0
jump. All numerical/code/ROM parameters here are INTERNAL lower-level
facts, to be supplied from the fixed program and original input. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m

theorem prefix_registers_le (rom : PhysicalROM) (N q handlerPC B : Nat) (old : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (nBound : N ≤ B) (qBound : q ≤ B) (handlerBound : handlerPC ≤ B) (small : 8 ≤ B)
    (count : Nat) (bound : count ≤ 8) :
    RegistersLE B (natRun rom (program handlerPC old) count natInitial) := by
  rw [first_eight_prefix rom handlerPC old count bound]
  interval_cases count <;> intro register <;> cases register <;>
    simp [lead, branch, runOps, natInitial, natExecuteOp, Op.execute,
      Instruction.execute, headerN, headerQ]
  all_goals omega

theorem prefix_active (rom : PhysicalROM) (handlerPC : Nat) (old : List PackingOp)
    (count : Nat) (bound : count ≤ 8) :
    (natRun rom (program handlerPC old) count natInitial).halted = false := by
  rw [first_eight_prefix rom handlerPC old count bound]
  exact (runOps_halted rom _ natInitial).trans rfl

theorem prefix_pc (rom : PhysicalROM) (handlerPC : Nat) (old : List PackingOp)
    (count : Nat) (bound : count < 8) :
    (natRun rom (program handlerPC old) count natInitial).pc = 5 * count := by
  have within : count ≤ (lead handlerPC).length := by rw [lead_length]; omega
  rw [first_eight_prefix rom handlerPC old count bound.le,
    List.take_append_of_le_length within]
  have straight : ∀ op ∈ (lead handlerPC).take count, NoJump op := by
    intro op member
    exact lead_noJump handlerPC op (List.mem_of_mem_take member)
  have pc := runOps_pc rom ((lead handlerPC).take count) natInitial straight
  rw [List.length_take_of_le within] at pc
  simpa only [natInitial, Nat.zero_add] using pc

theorem gate_pc (rom : PhysicalROM) (N q handlerPC : Nat) (old : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q) :
    (natRun rom (program handlerPC old) 8 natInitial).pc =
      if q = 0 then handlerPC else 40 := by
  rw [first_eight_run]
  simp [lead, branch, runOps, natInitial, natExecuteOp, Op.execute,
    Instruction.execute, headerN, headerQ]

theorem gate_safe (rom : PhysicalROM) (N q handlerIndex B H : Nat) (old : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (nBound : N ≤ B) (qBound : q ≤ B) (handlerBound : 5 * handlerIndex ≤ B) (small : 8 ≤ B)
    (inputBound : 2 ≤ (rom.words .input).length) (heapBound : 2 ≤ H)
    (handlerLabel : handlerIndex ≤ (program (5 * handlerIndex) old).length) :
    RunSafe B H rom (program (5 * handlerIndex) old) 8 natInitial := by
  have length : 10 ≤ (program (5 * handlerIndex) old).length := by
    simp only [program, List.length_append, head_length]
    omega
  constructor
  · intro count bound
    refine ⟨prefix_registers_le rom N q (5 * handlerIndex) B old headerN headerQ
      nBound qBound handlerBound small count bound,
      prefix_active rom (5 * handlerIndex) old count bound, ?_⟩
    by_cases early : count < 8
    · exact ⟨count, by omega, prefix_pc rom (5 * handlerIndex) old count early⟩
    · have last : count = 8 := by omega
      subst count
      by_cases zero : q = 0
      · refine ⟨handlerIndex, handlerLabel, ?_⟩
        exact (gate_pc rom N q (5 * handlerIndex) old headerN headerQ).trans (ite_eq_left zero)
      · refine ⟨8, by omega, ?_⟩
        exact (gate_pc rom N q (5 * handlerIndex) old headerN headerQ).trans (ite_eq_right zero)
  · intro count bound
    have indexBound : count < (program (5 * handlerIndex) old).length := by omega
    refine ⟨count, indexBound, prefix_pc rom (5 * handlerIndex) old count bound, ?_⟩
    rw [first_eight_prefix rom (5 * handlerIndex) old count bound.le]
    interval_cases count <;>
      simp [program, head, lead, branch, restore, runOps, natInitial, natExecuteOp,
        Op.execute, Instruction.execute, headerN, headerQ, NatAccessFits, AccessFits]
    all_goals omega

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079
