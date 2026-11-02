module

public import Paid.PDROC_BitVM_VM_ISA_ControlCatalog_003
public import Paid.PDROC_BitVM_Kernel_Trace_038

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

namespace PDROC.BitVM.VM.ISA.ControlResources

open Turing PaperProofs.Paid.Computation
open ControlCatalog

/-! SOURCE ONLY; no child compiler. Constants refer to FIXED source
syntax/code and precede ALL input/state/caller words. No logical state is
fed to delta. WorkspaceAny is handled by the actual clear/pop paths. -/

def ResourceRefinement (code : Program) (instruction : ControlInstruction) : Prop :=
  ∃ C D : Nat, 0 < C ∧ 0 < D ∧
    ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
      (events : List Log.HeapEvent) (contents : Stack → List Bool),
      Source.Ready input logical events contents →
      Instruction.execute input instruction.val logical = some next →
      ∃ (run : List (ControlCatalog.State code instruction)) (final : ControlCatalog.State code instruction),
        ControlCatalog.ActualRun code instruction contents run final ∧
        run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D

/-- Stronger than the caller Ready contract: no empty-workspace premise
is used here. The old4 scratch sums are charged by the total indirect
callee; branch/Nop really take their old2-state physical source paths. -/
theorem any_workspace (code : Program) (instruction : ControlInstruction) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (input : List Cell) (logical : PaperProofs.Paid.Computation.State) (contents : Stack → List Bool),
        (∀ reg, contents (Kernel.RegisterGlobal.registerSlot reg) = encodeCellBits (logical.register reg)) →
        ∃ (run : List (ControlCatalog.State code instruction)) (final : ControlCatalog.State code instruction),
          ControlCatalog.ActualRun code instruction contents run final ∧
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  rcases instruction with ⟨instruction, control⟩
  cases instruction with
  | branchZero condition whenZero whenNonzero =>
    let current : ControlInstruction := ⟨.branchZero condition whenZero whenNonzero, rfl⟩
    refine ⟨2, 1, by decide, by decide, ?_⟩
    intro input logical contents _represented
    obtain ⟨run, head, chain, last, halt, length⟩ :=
      branch_read_runs condition contents (ControlCatalog.initial code current)
    let final : ControlCatalog.State code current :=
      ⟨none, Kernel.Branch.captured (contents (Kernel.RegisterGlobal.registerSlot condition)), contents⟩
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    have small : 2 ≤ 2 * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^1 := by
      simp only [pow_one]
      omega
    exact length.le.trans small
  | jump target =>
    let current : ControlInstruction := ⟨.jump target, rfl⟩
    refine ⟨2, 1, by decide, by decide, ?_⟩
    intro input logical contents _represented
    obtain ⟨run, head, chain, last, halt, length⟩ := nop_runs contents
    let final : ControlCatalog.State code current := ⟨none, (), contents⟩
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    have small : 2 ≤ 2 * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^1 := by
      simp only [pow_one]
      omega
    exact length.le.trans small
  | halt =>
    let current : ControlInstruction := ⟨.halt, rfl⟩
    refine ⟨2, 1, by decide, by decide, ?_⟩
    intro input logical contents _represented
    obtain ⟨run, head, chain, last, halt, length⟩ := nop_runs contents
    let final : ControlCatalog.State code current := ⟨none, (), contents⟩
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    have small : 2 ≤ 2 * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^1 := by
      simp only [pow_one]
      omega
    exact length.le.trans small
  | jumpIndirect source =>
    let current : ControlInstruction := ⟨.jumpIndirect source, rfl⟩
    obtain ⟨C, positive, bounded⟩ := indirect_resource code source
    refine ⟨C, 1, positive, by decide, ?_⟩
    intro input logical contents represented
    obtain ⟨run, final, head, chain, last, halt, time⟩ :=
      bounded (logical.register source) contents (represented source)
    refine ⟨run, final, ⟨head, chain, last, halt⟩, ?_⟩
    rw [pow_one]
    exact time.trans (Nat.mul_le_mul_left C (by omega))
  | _ => cases control

theorem resource (code : Program) (instruction : ControlInstruction) : ResourceRefinement code instruction := by
  obtain ⟨C, D, positiveC, positiveD, bounded⟩ := any_workspace code instruction
  refine ⟨C, D, positiveC, positiveD, ?_⟩
  intro input logical next events contents ready _success
  exact bounded input logical contents ready.registers

/-- Resource and observable theorems may originate from old proof blocks,
but halting-run determinism identifies the ENTIRE selected source trace.
The returned run is exactly execute_runs' semantic witness, never a new
unrelated path carrying only a time certificate. -/
theorem complete (code : Program) (instruction : ControlInstruction) :
    ∃ C D : Nat, 0 < C ∧ 0 < D ∧
      ∀ (input : List Cell) (logical next : PaperProofs.Paid.Computation.State)
        (events : List Log.HeapEvent) (contents : Stack → List Bool),
        Source.Ready input logical events contents →
        Instruction.execute input instruction.val logical = some next →
        ∃ (run : List (ControlCatalog.State code instruction)) (final : ControlCatalog.State code instruction),
          ControlCatalog.ActualRun code instruction contents run final ∧
          Source.Observables input next (events ++ (Log.eventOf instruction.val logical).toList) final.stk ∧
          NextMatches code (ControlCatalog.observedNext code instruction final.var) next.pc ∧
          run.length ≤ C * (Kernel.NatInstruction.dataSize contents + (encodeBits input).length + 1)^D := by
  obtain ⟨C, D, positiveC, positiveD, bounded⟩ := resource code instruction
  refine ⟨C, D, positiveC, positiveD, ?_⟩
  intro input logical next events contents ready success
  obtain ⟨run, final, actual, observed, selected⟩ :=
    execute_runs code instruction input logical next events contents ready success
  obtain ⟨known, knownFinal, knownActual, time⟩ := bounded input logical next events contents ready success
  obtain ⟨same, _sameFinal⟩ := Kernel.Trace.final_unique (TM2.step (ControlCatalog.program code instruction))
    (ControlCatalog.before code instruction contents) final knownFinal run known
    actual.1 actual.2.1 actual.2.2.1 actual.2.2.2
    knownActual.1 knownActual.2.1 knownActual.2.2.1 knownActual.2.2.2
  refine ⟨run, final, actual, observed, selected, ?_⟩
  rw [same]
  exact time

end PDROC.BitVM.VM.ISA.ControlResources
