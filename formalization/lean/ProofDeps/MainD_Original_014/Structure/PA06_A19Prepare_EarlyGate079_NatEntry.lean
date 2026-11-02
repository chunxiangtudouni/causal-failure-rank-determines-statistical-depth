module

public import Structure.PA06_A19Prepare_EarlyGate079_Program
public import PaperProofs.Structure.RawIncidenceLaminarFullRAM
public import PaperProofs.Structure.RawIncidenceScanSafety
public import PaperProofs.Structure.CompactControllerClaims

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual first8 fetched instructions of the early gate.
Atq0 they jump before the old pair checker. The real two input headers are
read and stored; no initialized header/width/tree is supplied by a caller.
These Nat facts still require Word refinement and the real handler. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawTreePreprocessingClaims RawIncidenceLaminarRAM RawIncidenceScanSafety
  CompactControllerClaims

theorem first_eight_run (rom : PhysicalROM) (handlerPC : Nat) (old : List PackingOp) :
    natRun rom (program handlerPC old) 8 natInitial =
      natExecuteOp rom branch (runOps rom (lead handlerPC) natInitial) := by
  have slice := program_lead_slice handlerPC old
  simpa only [lead_length] using
    natRun_of_segment_last rom (program handlerPC old) (lead handlerPC) branch 0
      slice.1 slice.2.1 slice.2.2 (lead_noJump handlerPC) natInitial rfl rfl

theorem first_eight_prefix (rom : PhysicalROM) (handlerPC : Nat) (old : List PackingOp)
    (count : Nat) (bound : count ≤ 8) :
    natRun rom (program handlerPC old) count natInitial =
      runOps rom (((lead handlerPC) ++ [branch]).take count) natInitial := by
  have slice := program_lead_slice handlerPC old
  exact natRun_segment_prefix rom (program handlerPC old) (lead handlerPC) branch 0
    slice.1 slice.2.1 slice.2.2 (lead_noJump handlerPC) natInitial rfl rfl count bound

theorem zero_entry (rom : PhysicalROM) (N handlerPC : Nat) (old : List PackingOp)
    (headerN : rom.semantic.read .input 0 = N)
    (headerQ : rom.semantic.read .input 1 = 0) :
    let after := natRun rom (program handlerPC old) 8 natInitial
    after.pc = handlerPC ∧ after.halted = false ∧
      after.heap = Function.update (Function.update (fun _ => 0) 0 N) 1 0 ∧
      after.register .total = 0 ∧ after.register .index = handlerPC := by
  dsimp only
  simp only [first_eight_run]
  simp [lead, branch, runOps, natInitial, natExecuteOp, Op.execute,
    Instruction.execute, headerN, headerQ]

theorem original_rom_zero (full : List (Finset (Fin 0))) (used : Finset (Fin 0)) :
    controllerInput 0 full used = rawIncidenceROM 0 full := by
  have range : List.finRange 0 = [] := by decide
  simp only [controllerInput, range, List.map_nil, List.append_nil]

theorem zero_original_entry (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (handlerPC : Nat) (old : List PackingOp) :
    let after := natRun (controllerInput 0 full used) (program handlerPC old) 8 natInitial
    after.pc = handlerPC ∧ after.halted = false ∧
      after.heap = Function.update (Function.update (fun _ => 0) 0 full.length) 1 0 ∧
      after.register .total = 0 ∧ after.register .index = handlerPC := by
  rw [original_rom_zero]
  exact zero_entry (rawIncidenceROM 0 full) full.length handlerPC old
    (raw_header_N 0 full) (raw_header_q 0 full)

end PaperProofs.Structure.LaminarTree.PA06A19PrepareEarlyGate079
