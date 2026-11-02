module

public import Structure.PA06_A19Prepare_InitializedFront086_Common

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual two-op dispatcher and sixteen-op006 initializer in
ONE082.program. All short calculations stay on abstract incoming states. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine RawIncidenceLaminarRAM
  RawIncidenceScanSafety RawTreePreprocessingClaims CompactControllerClaims

theorem gate_prefix_run (rom : PhysicalROM) (state : NatState)
    (pc : state.pc = 630) (active : state.halted = false) (count : Nat) (bound : count ≤ 2) :
    natRun rom program count state = runOps rom (gate.take count) state := by
  simpa only [gate, List.cons_append, List.nil_append] using
    natRun_segment_prefix rom program
      [.base (.base (.constant .index (5 * PA06A19PrepareAllQCode082.finalEnd)))]
      (.jumpIfZero .value .index) 126
      (by have room := program_room; change 126 + 1 + 1 ≤ program.length; omega)
      (by
        intro position hp
        change position < 1 at hp
        interval_cases position
        exact gate_slot 0 (by decide))
      (gate_slot 1 (by decide)) (by simp [NoJump]) state pc active count bound

private theorem gate_registers_local (rom : PhysicalROM) (width target : Nat) (state : NatState)
    (registers : RegistersFit width state) (endpoint : Fits width (5 * target))
    (count : Nat) (bound : count ≤ 2) :
    RegistersFit width (runOps rom
      ([.base (.base (.constant .index (5 * target))), .jumpIfZero .value .index].take count) state) := by
  interval_cases count <;> intro reg <;> cases reg <;>
    simp [runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact registers _ | exact endpoint

private theorem pc_fit_local (width index endpoint pc : Nat)
    (upper : index ≤ endpoint) (room : Fits width (5 * endpoint)) (position : pc = 5 * index) :
    Fits width pc := by
  rw [position]
  exact (Nat.mul_le_mul_left 5 upper).trans_lt room

theorem gate_registers (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (registers : RegistersFit (bits q full) state) (count : Nat) (bound : count ≤ 2) :
    RegistersFit (bits q full) (runOps (rawIncidenceROM q full) (gate.take count) state) := by
  have endpoint := PA06A19PrepareAllQCode082.selected_pc_room full.length q
  rw [PA06A19PrepareAllQCode082.program_length] at endpoint
  simpa only [gate] using
    (gate_registers_local (rawIncidenceROM q full) (bits q full)
      PA06A19PrepareAllQCode082.finalEnd state registers endpoint count bound)

theorem gate_run (rom : PhysicalROM) (state : NatState) (pc : state.pc = 630)
    (active : state.halted = false) (accepted : state.register .value = 1) :
    natRun rom program 2 state =
      { state with register := Function.update state.register .index (5 * PA06A19PrepareAllQCode082.finalEnd), pc := 640 } := by
  rw [gate_prefix_run rom state pc active 2 le_rfl]
  simp [gate, runOps, natExecuteOp, Op.execute, Instruction.execute, accepted, pc]

theorem gate_point (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (pc : state.pc = 630) (active : state.halted = false) (registers : RegistersFit (bits q full) state)
    (count : Nat) (bound : count < 2) :
    Point q full (natRun (rawIncidenceROM q full) program count state) := by
  rw [gate_prefix_run (rawIncidenceROM q full) state pc active count bound.le]
  have rf := gate_registers q full state registers count bound.le
  have live := (runOps_halted (rawIncidenceROM q full) (gate.take count) state).trans active
  have position : (runOps (rawIncidenceROM q full) (gate.take count) state).pc = 5 * (126 + count) := by
    interval_cases count <;> simp [gate, runOps, natExecuteOp, Op.execute, Instruction.execute, pc]
  have hi : 126 + count < program.length := by have room := program_room; omega
  refine ⟨rf, ?_, live, 126 + count, hi, position, ?_⟩
  · exact pc_fit_local (bits q full) _ PA06A19PrepareAllQCode082.program.length _
      hi.le (PA06A19PrepareAllQCode082.selected_pc_room full.length q) position
  · rw [gate_slot count bound]
    interval_cases count <;> trivial

theorem init_point (q : Nat) (full : List (Finset (Fin q))) (state : NatState)
    (pc : state.pc = 640) (active : state.halted = false) (registers : RegistersFit (bits q full) state)
    (count : Nat) (bound : count < 16) :
    Point q full (natRun (rawIncidenceROM q full) program count state) := by
  have run := PA06A19PrepareCompactInit006.natRun_prefix_eq q full program 128 init_slice.1 init_slice.2
    state pc active count bound.le
  have position := PA06A19PrepareCompactInit006.natRun_prefix_pc q full program 128 init_slice.1 init_slice.2
    state pc active count bound.le
  have live : (natRun (rawIncidenceROM q full) program count state).halted = false := by
    rw [run, runOps_halted, active]
  have hi : 128 + count < program.length := by have room := program_room; omega
  refine ⟨?_, ?_, live, 128 + count, hi, position, ?_⟩
  · rw [run]
    exact PA06A19PrepareCompactRetention030InitBounds.init_prefix_registersFit q full state registers count bound.le
  · exact pc_fit_local (bits q full) _ PA06A19PrepareAllQCode082.program.length _
      hi.le (PA06A19PrepareAllQCode082.selected_pc_room full.length q) position
  · have access := PA06A19PrepareCompactInit006.runOps_prefix_accessFits q full state count bound
    have wide := access_mono (rawIncidenceROM q full) 17 (allocation q full)
      (runOps (rawIncidenceROM q full) (PA06A19PrepareCompactInit006.initProgram.take count) state)
      (PA06A19PrepareCompactInit006.initProgram.getD count PA06A19PrepareCompactInit006.paddingOp)
      (allocation_room q full) access
    rw [run]
    have slot := init_slice.2 count bound
    rw [List.getD_eq_getElem _ _ hi] at slot
    rw [slot]
    exact wide

end PaperProofs.Structure.LaminarTree.PA06A19PrepareInitializedFront086
