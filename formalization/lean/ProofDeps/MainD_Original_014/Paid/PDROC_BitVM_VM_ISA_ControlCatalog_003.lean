module

public import Paid.PDROC_BitVM_VM_ISA_ControlCatalog_002
public import Paid.PDROC_BitVM_VM_Source_Representation_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2200000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.ControlCatalog

open Turing PaperProofs.Paid.Computation PaperProofs.Paid.Parameters

/-! SOURCE ONLY; parent's coherent check is still required. This block
does not modify the stable001/002 code or any runtime dispatcher. The
logical RAM execute expression appears ONLY as a refinement premise. -/

def before (code : Program) (instruction : ControlInstruction) (contents : Stack → List Bool) : State code instruction :=
  ⟨some (start code instruction), initial code instruction, contents⟩

def ActualRun (code : Program) (instruction : ControlInstruction) (contents : Stack → List Bool)
    (run : List (State code instruction)) (final : State code instruction) : Prop :=
  run.head? = some (before code instruction contents) ∧
  run.IsChain (fun first last => TM2.step (program code instruction) first = some last) ∧
  run.getLast? = some final ∧ TM2.step (program code instruction) final = none

theorem unchanged_fields (input : List Cell) (instruction : ControlInstruction)
    (logical next : PaperProofs.Paid.Computation.State)
    (success : Instruction.execute input instruction.val logical = some next) :
    next.register = logical.register ∧ next.heap = logical.heap ∧ next.live = logical.live ∧ next.output = logical.output := by
  rcases instruction with ⟨instruction, control⟩
  cases instruction with
  | branchZero condition whenZero whenNonzero =>
    cases parsed : (logical.register condition).nat? with
    | none => simp [Instruction.execute, parsed] at success
    | some value =>
      have actual : Instruction.execute input (.branchZero condition whenZero whenNonzero) logical =
          some {logical with pc := if value = 0 then whenZero else whenNonzero} := by simp [Instruction.execute, parsed]
      have same := Option.some.inj (success.symm.trans actual)
      subst next
      exact ⟨rfl, rfl, rfl, rfl⟩
  | jump target =>
    have actual : Instruction.execute input (.jump target) logical = some {logical with pc := target} := rfl
    have same := Option.some.inj (success.symm.trans actual)
    subst next
    exact ⟨rfl, rfl, rfl, rfl⟩
  | jumpIndirect source =>
    cases parsed : (logical.register source).nat? with
    | none => simp [Instruction.execute, parsed] at success
    | some value =>
      have actual : Instruction.execute input (.jumpIndirect source) logical = some {logical with pc := value} := by
        simp [Instruction.execute, parsed]
      have same := Option.some.inj (success.symm.trans actual)
      subst next
      exact ⟨rfl, rfl, rfl, rfl⟩
  | halt => cases success
  | _ => cases control

theorem no_event (instruction : ControlInstruction) (logical : PaperProofs.Paid.Computation.State) :
    Log.eventOf instruction.val logical = none := by
  rcases instruction with ⟨instruction, control⟩
  cases instruction <;> first | rfl | cases control

/-- Transport only AFTER an actual path supplied the physical frame.
No state/readonly/heap/output replacement is a machine transition. -/
theorem observables_after_control (input : List Cell) (instruction : ControlInstruction)
    (logical next : PaperProofs.Paid.Computation.State) (events : List Log.HeapEvent)
    (contents data : Stack → List Bool) (ready : Source.Ready input logical events contents)
    (success : Instruction.execute input instruction.val logical = some next)
    (frame : ∀ role : Stack, 1 ≤ role.val ∧ role.val < 24 → data role = contents role) :
    Source.Observables input next (events ++ (Log.eventOf instruction.val logical).toList) data := by
  rw [no_event, Option.toList_none, List.append_nil]
  obtain ⟨registers, heap, live, output⟩ := unchanged_fields input instruction logical next success
  apply Source.observables_register_step input logical next events contents data ready.toObservables
  · intro reg
    have bounds := Kernel.RegisterGlobal.registerSlot_bounds reg
    rw [frame (Kernel.RegisterGlobal.registerSlot reg) (by omega), registers]
    exact ready.registers reg
  · exact heap
  · exact live
  · exact output
  · intro field
    apply frame
    change 1 ≤ field.val + 1 ∧ field.val + 1 < 24
    omega
  · exact frame 21 (by decide)
  · exact frame 22 (by decide)
  · exact frame 23 (by decide)

/-- Uniform CONTROL source contract for the parent CFG single-step
proof. All meaning/frame facts concern the SAME selected actual run.
The parent's derived original next-fetch bound removes NextMatches.none;
there is deliberately no new original input or target qualification. -/
theorem execute_runs (code : Program) (instruction : ControlInstruction)
    (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
    (events : List Log.HeapEvent) (contents : Stack → List Bool)
    (ready : Source.Ready input logical events contents)
    (success : Instruction.execute input instruction.val logical = some next) :
    ∃ (run : List (State code instruction)) (final : State code instruction),
      ActualRun code instruction contents run final ∧
      Source.Observables input next (events ++ (Log.eventOf instruction.val logical).toList) final.stk ∧
      NextMatches code (observedNext code instruction final.var) next.pc := by
  rcases instruction with ⟨instruction, control⟩
  cases instruction with
  | branchZero condition whenZero whenNonzero =>
    let current : ControlInstruction := ⟨.branchZero condition whenZero whenNonzero, rfl⟩
    obtain ⟨run, head, chain, last, halt, _⟩ := branch_read_runs condition contents (initial code current)
    let final : State code current :=
      ⟨none, Kernel.Branch.captured (contents (Kernel.RegisterGlobal.registerSlot condition)), contents⟩
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_, ?_⟩
    · exact observables_after_control input current logical next events contents contents ready success (fun _ _ => rfl)
    · have correct := execute_branch_matches code input logical next condition whenZero whenNonzero success
      simpa only [observedNext, current, final, ready.registers condition] using correct
  | jump target =>
    let current : ControlInstruction := ⟨.jump target, rfl⟩
    obtain ⟨run, head, chain, last, halt, _⟩ := nop_runs contents
    let final : State code current := ⟨none, (), contents⟩
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_, ?_⟩
    · exact observables_after_control input current logical next events contents contents ready success (fun _ _ => rfl)
    · exact execute_jump_matches code input logical next target success
  | jumpIndirect source =>
    let current : ControlInstruction := ⟨.jumpIndirect source, rfl⟩
    obtain ⟨run, final, head, chain, last, halt, _, data, meaning, _⟩ :=
      indirect_runs code source (logical.register source) contents (ready.registers source)
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_, ?_⟩
    · apply observables_after_control input current logical next events contents final.stk ready success
      intro role safeRole
      rw [data]
      apply Control.Indirect.cleared_other
      intro index
      fin_cases index <;>
        (intro same; have values := congrArg Fin.val same; simp [Control.Indirect.clearSlot] at values; omega)
    · exact execute_indirect_matches code input logical next source final.var meaning success
  | halt => cases success
  | _ => cases control

end PDROC.BitVM.VM.ISA.ControlCatalog
