module

public import Structure.PA06_A19Prepare_ZeroHeader080_Program

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED all-prefix safety of the actual fixed q0 handler.
The prelude's existing ALL-q certificate needs only actual ROM headers,
numeric/PC room and the incoming registers. No tree or heap answer enters. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety CompactControllerClaims PA17UniformGenerator035a
  PA17UniformGenerator035i PA17UniformGenerator035j PA17UniformGenerator035m

theorem finish_numeric (rom : PhysicalROM) (B H : Nat) (state : NatState)
    (hr : RegistersLE B state) (hsmall : 5 ≤ B) (hheap : 6 ≤ H) (hwidth : state.heap 2 ≤ B) :
    NumericSafe B H rom finish state := by
  constructor
  · intro count hc register
    have incoming := hr register
    change count ≤ 15 at hc
    interval_cases count <;> cases register <;>
      simp [finish, runOps, natExecuteOp, Op.execute, Instruction.execute]
    all_goals omega
  · intro count hc
    change count < 15 at hc
    interval_cases count <;>
      simp [finish, runOps, natExecuteOp, Op.execute, Instruction.execute, NatAccessFits, AccessFits]
    all_goals omega

theorem program_safe (full : List (Finset (Fin 0))) (used : Finset (Fin 0))
    (B H : Nat) (left right : List PackingOp) (before : NatState)
    (hsmall : 69 ≤ B) (hheap : 69 ≤ H) (hinput : full.length + 0 + 1 ≤ B)
    (hbits : indexWidth 32 full.length 0 ≤ B)
    (hpc : before.pc = 5 * left.length) (ha : before.halted = false)
    (hr : RegistersLE B before) (hpcB : 5 * (left ++ programAt left.length ++ right).length ≤ B) :
    RunSafe B H (controllerInput 0 full used) (left ++ programAt left.length ++ right)
      (clock full.length) before := by
  let rom := controllerInput 0 full used
  let code := left ++ programAt left.length ++ right
  let lead := left ++ dimensionPrelude left.length
  let middle := natRun rom code (dimensionClock full.length 0) before
  have preSafe : RunSafe B H rom code (dimensionClock full.length 0) before := by
    have actual := PA06A19PrepareRuntimeHeader019.prelude_safe 0 full used B H left (finish ++ right)
      before hsmall hheap hinput hbits hpc ha hr
      (by simpa only [programAt, List.append_assoc] using hpcB)
    simpa only [rom, code, programAt, List.append_assoc] using actual
  have pre : middle.pc = 5 * (left.length + 45) ∧ middle.halted = false ∧
      middle.heap 2 = indexWidth 32 full.length 0 := by
    have actual := PA06A19PrepareRuntimeHeader019.prelude_run 0 full used left (finish ++ right) before hpc ha
    simpa only [middle, code, rom, programAt, List.append_assoc] using
      (And.intro actual.1 (And.intro actual.2.1 actual.2.2.2.1))
  have middleRegs : RegistersLE B middle := (preSafe.final _ _ _ _ _).1
  have numeric := finish_numeric rom B H middle middleRegs (by omega) (by omega)
    (by rw [pre.2.2]; exact hbits)
  have lastSafe : RunSafe B H rom code 15 middle := by
    have actual := straight_segment_safe rom B H lead finish right finish_noJump middle
      (by simpa only [lead, List.length_append, dimensionPrelude_length] using pre.1) pre.2.1 numeric
    simpa only [rom, code, programAt, lead, List.append_assoc, finish_length] using actual
  change RunSafe B H rom code (dimensionClock full.length 0 + 15) before
  exact RunSafe.add B H rom code (dimensionClock full.length 0) 15 before preSafe lastSafe

end PaperProofs.Structure.LaminarTree.PA06A19PrepareZeroHeader080
