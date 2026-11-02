module

public import Structure.PA06_A19Prepare_AllQCode082
public import PaperProofs.Structure.PA17_UniformGenerator_035m

set_option autoImplicit false
set_option warningAsError true

/-! UNVALIDATED actual three fetched skip instructions in the fixed082
program.  The whole-code slice is read from082.skip_slice; no implicit
HALT or equality with a different containing program is used. -/

@[expose] public section
namespace PaperProofs.Structure.LaminarTree.PA06A19PreparePositiveSkip088

open IndexedRAM IndexedClosureRAM AlgorithmClaims PackingMachine
  RawIncidenceLaminarRAM RawIncidenceScanSafety RawTreePreprocessingClaims
  PA17UniformGenerator035j PA17UniformGenerator035m
open PA06A19PrepareAllQCode082 (program bodyEnd finalEnd)

def lead : List PackingOp :=
  [.base (.base (.constant .flag 0)), .base (.base (.constant .index (5 * finalEnd)))]
def last : PackingOp := .jumpIfZero .flag .index
def padding : PackingOp := .base (.base (.constant .flag 0))

theorem lead_length : lead.length = 2 := rfl
theorem skip_split : jumpTo finalEnd = lead ++ [last] := rfl
theorem lead_noJump : ∀ op ∈ lead, NoJump op := by simp [lead, NoJump]

theorem skip_room : bodyEnd + 3 ≤ program.length := by
  rw [PA06A19PrepareAllQCode082.program_length]
  unfold PA06A19PrepareAllQCode082.finalEnd PA06A19PrepareAllQCode082.handlerStart
  omega

theorem skip_code (position : Nat) (bound : position < 3) :
    program[bodyEnd + position]'(by have room := skip_room; omega) =
      (jumpTo finalEnd)[position]'(by change position < 3; exact bound) := by
  have sliced := PA06A19PrepareAllQCode082.skip_slice
  change (program.drop bodyEnd).take 3 = jumpTo finalEnd at sliced
  have value := congrArg (fun block : List PackingOp => block.getD position padding) sliced
  have takeBound : position < ((program.drop bodyEnd).take 3).length := by
    rw [sliced]
    exact bound
  rw [List.getD_eq_getElem _ _ takeBound,
    List.getD_eq_getElem _ _ (show position < (jumpTo finalEnd).length from bound)] at value
  simpa only [List.getElem_take, List.getElem_drop] using value

private theorem jumpTo_last (target : Nat) :
    (jumpTo target)[2]'(by change 2 < 3; decide) = .jumpIfZero .flag .index := rfl

theorem native_prefix (rom : PhysicalROM) (before : NatState)
    (pc : before.pc = 5 * bodyEnd) (active : before.halted = false)
    (count : Nat) (bound : count ≤ 3) :
    natRun rom program count before = runOps rom ((jumpTo finalEnd).take count) before := by
  rw [skip_split]
  apply natRun_segment_prefix rom program lead last bodyEnd
    (by rw [lead_length]; exact skip_room) ?_ ?_ lead_noJump before pc active count bound
  · intro position hp
    have short : position < 2 := hp
    interval_cases position <;> exact skip_code _ (by decide)
  · simpa only [lead_length, last] using
      (skip_code 2 (by decide)).trans (jumpTo_last finalEnd)

theorem native_finish (rom : PhysicalROM) (before : NatState)
    (pc : before.pc = 5 * bodyEnd) (active : before.halted = false) :
    let after := natRun rom program 3 before
    after.pc = 5 * finalEnd ∧ after.halted = false ∧ after.heap = before.heap := by
  rw [native_prefix rom before pc active 3 le_rfl]
  simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute, active]

theorem native_pc (rom : PhysicalROM) (before : NatState)
    (pc : before.pc = 5 * bodyEnd) (active : before.halted = false)
    (count : Nat) (bound : count < 3) :
    (natRun rom program count before).pc = 5 * (bodyEnd + count) := by
  rw [native_prefix rom before pc active count bound.le]
  interval_cases count <;>
    simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute, pc]
  all_goals omega

private theorem jumpTo_prefix_registers (rom : PhysicalROM) (target B : Nat) (before : NatState)
    (registers : RegistersLE B before) (targetBound : 5 * target ≤ B)
    (count : Nat) (bound : count ≤ 3) :
    RegistersLE B (runOps rom ((jumpTo target).take count) before) := by
  interval_cases count <;> intro register <;> cases register <;>
    simp [jumpTo, runOps, natExecuteOp, Op.execute, Instruction.execute]
  all_goals first | exact registers _ | exact targetBound

theorem native_registers (rom : PhysicalROM) (B : Nat) (before : NatState)
    (pc : before.pc = 5 * bodyEnd) (active : before.halted = false)
    (registers : RegistersLE B before) (targetBound : 5 * finalEnd ≤ B)
    (count : Nat) (bound : count ≤ 3) :
    RegistersLE B (natRun rom program count before) := by
  rw [native_prefix rom before pc active count bound]
  exact jumpTo_prefix_registers rom finalEnd B before registers targetBound count bound

theorem native_safe (rom : PhysicalROM) (B H : Nat) (before : NatState)
    (pc : before.pc = 5 * bodyEnd) (active : before.halted = false)
    (registers : RegistersLE B before) (targetBound : 5 * finalEnd ≤ B) :
    RunSafe B H rom program 3 before := by
  constructor
  · intro count bound
    refine ⟨native_registers rom B before pc active registers targetBound count bound, ?_, ?_⟩
    · rw [native_prefix rom before pc active count bound, runOps_halted]
      exact active
    · by_cases early : count < 3
      · exact ⟨bodyEnd + count, by have room := skip_room; omega,
          native_pc rom before pc active count early⟩
      · have endCount : count = 3 := by omega
        subst count
        exact ⟨finalEnd, by rw [PA06A19PrepareAllQCode082.program_length],
          (native_finish rom before pc active).1⟩
  · intro count bound
    have hi : bodyEnd + count < program.length := by have room := skip_room; omega
    refine ⟨bodyEnd + count, hi, native_pc rom before pc active count bound, ?_⟩
    rw [skip_code count bound]
    interval_cases count <;> trivial

end PaperProofs.Structure.LaminarTree.PA06A19PreparePositiveSkip088
