module

public import Structure.PA06_A19Prepare_EarlyGate079_Positive
public import PaperProofs.Structure.PA17_UniformGenerator_035m

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED numeric/access safety of exactly the actual positive-q
first17 instructions. All values are read from the two original headers
or are literal constants. No later different-code run is transported. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePositiveFront084

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims RawIncidenceLaminarRAM RawIncidenceScanSafety
  PA17UniformGenerator035j PA17UniformGenerator035m PA06A19PrepareEarlyGate079

def code (handlerPC : Nat) (rest : List PackingOp) : List PackingOp :=
  PA06A19PrepareEarlyGate079.program handlerPC (checker ++ rest)

theorem code_length (handlerPC : Nat) (rest : List PackingOp) :
    (code handlerPC rest).length = 126 + rest.length := by
  rw [code, PA06A19PrepareEarlyGate079.program_length]
  · rw [List.length_append, checker_length]
  · simp only [List.length_append, checker_length]
    omega

private theorem room (handlerPC : Nat) (rest : List PackingOp) :
    126 ≤ (code handlerPC rest).length := by
  rw [code_length]
  omega

theorem first_numeric (rom : PhysicalROM) (N q handlerPC B H : Nat)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (small : 640 ≤ B) (boundN : N ≤ B) (boundQ : q ≤ B) (handler : handlerPC ≤ B)
    (input : 2 ≤ rom.input.length) (heap : 3 ≤ H) :
    NumericSafe B H rom (lead handlerPC ++ [branch]) natInitial := by
  constructor
  · intro count hc register
    change count ≤ 8 at hc
    interval_cases count <;> cases register <;>
      simp [lead, branch, runOps, natInitial, natExecuteOp, Op.execute, Instruction.execute,
        headerN, headerQ]
    all_goals omega
  · have inputWords : 2 ≤ (rom.words .input).length := by
      change 2 ≤ rom.input.length
      exact input
    intro count hc
    change count < 8 at hc
    interval_cases count <;>
      simp [lead, branch, runOps, natInitial, natExecuteOp, Op.execute, Instruction.execute,
        NatAccessFits, AccessFits]
    all_goals omega

theorem middle_numeric (rom : PhysicalROM) (N q handlerPC B H : Nat)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (hq : 0 < q) (small : 640 ≤ B) (boundN : N ≤ B) (boundQ : q ≤ B)
    (handler : handlerPC ≤ B) (heap : 3 ≤ H) :
    NumericSafe B H rom (positiveMiddle ++ [outerBranch])
      (natExecuteOp rom branch (runOps rom (lead handlerPC) natInitial)) := by
  rw [positive_eight_state rom q handlerPC headerQ hq]
  constructor
  · intro count hc register
    change count ≤ 9 at hc
    interval_cases count <;> cases register <;>
      simp [positiveMiddle, restore, testCell, loadCell, outerBranch, lead, runOps,
        natInitial, natExecuteOp, Op.execute, Instruction.execute, headerN, headerQ]
    all_goals omega
  · intro count hc
    change count < 9 at hc
    interval_cases count <;>
      simp [positiveMiddle, restore, testCell, loadCell, outerBranch, lead, runOps,
        natInitial, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem prefix_registers (rom : PhysicalROM) (N q handlerPC B H : Nat) (rest : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (hq : 0 < q) (small : 640 ≤ B) (boundN : N ≤ B) (boundQ : q ≤ B)
    (handler : handlerPC ≤ B) (input : 2 ≤ rom.input.length) (heap : 3 ≤ H)
    (count : Nat) (bound : count ≤ 17) :
    RegistersLE B (natRun rom (code handlerPC rest) count natInitial) := by
  have first := first_numeric rom N q handlerPC B H headerN headerQ small boundN boundQ handler input heap
  have middle := middle_numeric rom N q handlerPC B H headerN headerQ hq small boundN boundQ handler heap
  change RegistersLE B (natRun rom (PA06A19PrepareEarlyGate079.program handlerPC (checker ++ rest)) count natInitial)
  rw [positive_prefix_formula rom q handlerPC rest headerQ hq count bound]
  by_cases early : count ≤ 8
  · rw [ite_eq_left early]
    exact first.1 count (by change count ≤ 8; exact early)
  · rw [ite_eq_right early]
    exact middle.1 (count - 8) (by change count - 8 ≤ 9; omega)

/-- Every proper prefix is active at its actual sequential instruction.
The nonsequential N=0 branch is executed only at the seventeenth step. -/
theorem prefix_control (rom : PhysicalROM) (q handlerPC : Nat) (rest : List PackingOp)
    (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q)
    (count : Nat) (bound : count < 17) :
    let fresh := natRun rom (code handlerPC rest) count natInitial
    fresh.pc = 5 * count ∧ fresh.halted = false := by
  dsimp only
  change (natRun rom (PA06A19PrepareEarlyGate079.program handlerPC (checker ++ rest)) count natInitial).pc =
      5 * count ∧
    (natRun rom (PA06A19PrepareEarlyGate079.program handlerPC (checker ++ rest)) count natInitial).halted = false
  by_cases early : count < 8
  · rw [first_eight_prefix rom handlerPC (checker ++ rest) count (by omega)]
    have hn : count ≤ (lead handlerPC).length := by rw [lead_length]; omega
    rw [List.take_append_of_le_length hn]
    constructor
    · rw [runOps_pc rom _ natInitial (fun op member => lead_noJump handlerPC op (List.mem_of_mem_take member)),
        List.length_take_of_le hn]
      change 0 + 5 * count = 5 * count
      exact Nat.zero_add (5 * count)
    · exact runOps_halted rom _ natInitial
  · have hn : count - 8 ≤ positiveMiddle.length := by rw [positiveMiddle_length]; omega
    have actual := positive_tail_prefix rom q handlerPC rest headerQ hq (count - 8) (by omega)
    have sameCount : 8 + (count - 8) = count := by omega
    rw [sameCount] at actual
    rw [actual, List.take_append_of_le_length hn]
    have entry := positive_eight_control rom q handlerPC headerQ hq
    dsimp only at entry
    constructor
    · rw [runOps_pc rom _ _ (fun op member => positiveMiddle_noJump op (List.mem_of_mem_take member)),
        List.length_take_of_le hn, entry.1]
      omega
    · exact (runOps_halted rom _ _).trans entry.2

private theorem first_slice (handlerPC : Nat) (rest : List PackingOp) (count : Nat) (bound : count < 8) :
    (code handlerPC rest)[count]'(by have h := room handlerPC rest; omega) =
      (lead handlerPC ++ [branch])[count]'(by
        simp only [List.length_append, lead_length, List.length_singleton]; omega) := by
  interval_cases count <;> rfl

private theorem middle_slice (handlerPC : Nat) (rest : List PackingOp) (offset : Nat) (bound : offset < 9) :
    (code handlerPC rest)[8 + offset]'(by have h := room handlerPC rest; omega) =
      (positiveMiddle ++ [outerBranch])[offset]'(by
        simp only [List.length_append, positiveMiddle_length, List.length_singleton]; omega) := by
  interval_cases offset <;> rfl

theorem run_safe (rom : PhysicalROM) (N q handlerPC B H : Nat) (rest : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q)
    (hq : 0 < q) (small : 640 ≤ B) (boundN : N ≤ B) (boundQ : q ≤ B)
    (handler : handlerPC ≤ B) (input : 2 ≤ rom.input.length) (heap : 3 ≤ H) :
    RunSafe B H rom (code handlerPC rest) 17 natInitial := by
  have length := room handlerPC rest
  have first := first_numeric rom N q handlerPC B H headerN headerQ small boundN boundQ handler input heap
  have middle := middle_numeric rom N q handlerPC B H headerN headerQ hq small boundN boundQ handler heap
  constructor
  · intro count hc
    have registers := prefix_registers rom N q handlerPC B H rest headerN headerQ hq small
      boundN boundQ handler input heap count hc
    by_cases last : count = 17
    · subst count
      have control := positive_seventeen_control rom N q handlerPC rest headerN headerQ hq
      dsimp only at control
      refine ⟨registers, control.2, ?_⟩
      by_cases zero : N = 0
      · refine ⟨126, length, ?_⟩
        simpa only [code, ite_eq_left zero] using control.1
      · refine ⟨17, by omega, ?_⟩
        simpa only [code, ite_eq_right zero] using control.1
    · have control := prefix_control rom q handlerPC rest headerQ hq count (by omega)
      exact ⟨registers, control.2, count, by omega, control.1⟩
  · intro count hc
    have control := prefix_control rom q handlerPC rest headerQ hq count hc
    refine ⟨count, by omega, control.1, ?_⟩
    change NatAccessFits rom H
      (natRun rom (PA06A19PrepareEarlyGate079.program handlerPC (checker ++ rest)) count natInitial)
      (code handlerPC rest)[count]
    by_cases early : count < 8
    · rw [first_eight_prefix rom handlerPC (checker ++ rest) count (by omega),
        first_slice handlerPC rest count early]
      exact first.2 count (by change count < 8; exact early)
    · have actual := positive_tail_prefix rom q handlerPC rest headerQ hq (count - 8) (by omega)
      have sameCount : 8 + (count - 8) = count := by omega
      rw [sameCount] at actual
      have codeBound : count < (code handlerPC rest).length := by omega
      have middleBound : count - 8 < (positiveMiddle ++ [outerBranch]).length := by
        change count - 8 < 9
        omega
      have lookup : (code handlerPC rest)[count]'codeBound =
          (positiveMiddle ++ [outerBranch])[count - 8]'middleBound := by
        simpa only [sameCount] using
          (middle_slice handlerPC rest (count - 8) (by omega))
      rw [actual, lookup]
      exact middle.2 (count - 8) (by change count - 8 < 9; omega)

/-- No prefix writes any heap cell other than the two real headers. -/
theorem prefix_heap_frame (rom : PhysicalROM) (q handlerPC : Nat) (rest : List PackingOp)
    (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q)
    (count : Nat) (bound : count ≤ 17) (address : Nat) (zero : address ≠ 0) (one : address ≠ 1) :
    (natRun rom (code handlerPC rest) count natInitial).heap address = 0 := by
  change (natRun rom (PA06A19PrepareEarlyGate079.program handlerPC (checker ++ rest)) count natInitial).heap address = 0
  rw [positive_prefix_formula rom q handlerPC rest headerQ hq count bound]
  by_cases early : count ≤ 8
  · rw [ite_eq_left early]
    interval_cases count <;>
      simp [lead, branch, runOps, natInitial, natExecuteOp, Op.execute, Instruction.execute,
        zero, one]
  · rw [ite_eq_right early, positive_eight_state rom q handlerPC headerQ hq]
    interval_cases count <;>
      simp [positiveMiddle, restore, testCell, loadCell, outerBranch, lead, runOps,
        natInitial, natExecuteOp, Op.execute, Instruction.execute, zero, one]

theorem seventeen_heap (rom : PhysicalROM) (N q handlerPC : Nat) (rest : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N) (headerQ : rom.semantic.read .input 1 = q) (hq : 0 < q) :
    (natRun rom (code handlerPC rest) 17 natInitial).heap =
      Function.update (Function.update (fun _ => 0) 0 N) 1 q := by
  change (natRun rom (PA06A19PrepareEarlyGate079.program handlerPC (checker ++ rest)) 17 natInitial).heap = _
  rw [positive_seventeen_run rom q handlerPC rest headerQ hq, positive_eight_state rom q handlerPC headerQ hq]
  funext address
  simp [positiveMiddle, restore, testCell, loadCell, outerBranch, lead, runOps, natInitial,
    natExecuteOp, Op.execute, Instruction.execute, headerN, headerQ]

end PaperProofs.Structure.LaminarTree.PA06A19PreparePositiveFront084
