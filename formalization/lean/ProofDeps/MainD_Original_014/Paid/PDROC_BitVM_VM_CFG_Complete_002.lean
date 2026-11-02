module

public import Paid.PDROC_BitVM_VM_CFG_Complete_001

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2400000

@[expose] public section

namespace PDROC.BitVM.VM.CFG.Complete

open Turing PDROC.BitVM.Common.IO PaperProofs.Paid.Computation

noncomputable def envelope (code : Program) (input : List Cell) (states : List PaperProofs.Paid.Computation.State) :=
  BoundaryBudget.boundaryBudget (encodeBits input).length (time code states) (peakOperandBits states)

noncomputable def totalBudget (C d : ℕ) (code : Program) (input : List Cell) (states : List PaperProofs.Paid.Computation.State) :=
  (time code states + 1) * C * (2 * envelope code input states + 1)^d

/-- Actual fixed compiled-CFG simulation. There are NO local/terminal/
startup callback premises in this theorem: all are instantiated by the
actual FullCFG theorems. C,d precede ALL original inputs/Runs/olddata.
The only size6/13 premise is the existing real phase input shape. -/
theorem complete_path (backend : ISA.RatBackend) (core : Bool) (code : Program) :
    ∃ C d : ℕ, 0 < C ∧ 0 < d ∧
      ∀ (input : List Cell) (states : List PaperProofs.Paid.Computation.State)
        (logicalFinal : PaperProofs.Paid.Computation.State) (contents : ISA.Stack → List Bool),
        input.length = Log.BankMount.fieldCount core → Runs code input states logicalFinal →
        Source.Ready input PaperProofs.Paid.Computation.initial [] contents →
        ∃ terminal : Program.State backend code,
          TM2.step (Program.program backend core code) terminal = none ∧
          Source.Ready input logicalFinal (BoundaryBudget.actualHistory code states) terminal.stk ∧
          ∃ path : ActualPath (TM2.step (Program.program backend core code))
            (Program.before backend code contents) terminal,
            path.posts.length ≤ totalBudget C d code input states := by
  obtain ⟨C, d, positiveC, positiveD, localRuns⟩ := local_callbacks backend core code
  refine ⟨C, d, positiveC, positiveD, ?_⟩
  intro input states logicalFinal contents size actual readyInitial
  obtain ⟨localStep, localHalt⟩ := localRuns input size
  let native := Program.program backend core code
  let Q := C * (2 * envelope code input states + 1)^d
  have simulate : Run.StepQ native code input states (Entry backend code) Q := by
    intro current next instruction events physical boundary fetched success valid ready related
    obtain ⟨after, nextRelated, nextReady, path, localTime⟩ :=
      localStep current next instruction events physical fetched success valid ready related
    have base := Run.local_base_bound code input states logicalFinal actual
      (encodeBits input).length (time code states) (peakOperandBits states) (le_refl _) (le_refl _) (le_refl _)
      current events physical.stk boundary ready
    refine ⟨after, nextRelated, nextReady, path, ?_⟩
    exact localTime.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left base d))
  have finish : Run.HaltQ native code input states (Entry backend code) Q := by
    intro current events physical boundary fetched ready related
    obtain ⟨after, halted, finalReady, path, localTime⟩ := localHalt current events physical fetched ready related
    have base := Run.local_base_bound code input states logicalFinal actual
      (encodeBits input).length (time code states) (peakOperandBits states) (le_refl _) (le_refl _) (le_refl _)
      current events physical.stk boundary ready
    refine ⟨after, halted, finalReady, path, ?_⟩
    exact localTime.trans (Nat.mul_le_mul_left C (Nat.pow_le_pow_left base d))
  have positiveCode := Source.runs_code_nonempty code input states logicalFinal actual
  have startup : ∃ first : Program.State backend code,
      Entry backend code PaperProofs.Paid.Computation.initial first ∧
      Source.Ready input PaperProofs.Paid.Computation.initial [] first.stk ∧
      ∃ path : ActualPath (TM2.step native) (Program.before backend code contents) first,
        path.posts.length ≤ Q := by
    refine ⟨Program.before backend code contents, before_related backend code contents positiveCode,
      readyInitial, ActualPath.refl _, ?_⟩
    exact Nat.zero_le _
  obtain ⟨terminal, halted, represented, path, pathTime⟩ :=
    Run.runs_path_Q native code input states logicalFinal actual (Entry backend code)
      (Program.before backend code contents) Q simulate finish startup
  have sourceLength := Run.runs_length_le_actual_time code input states logicalFinal actual
  have clock : path.posts.length ≤ (time code states + 1) * Q :=
    pathTime.trans (Nat.mul_le_mul_right Q (Nat.add_le_add_right sourceLength 1))
  refine ⟨terminal, halted, represented, path, ?_⟩
  simpa only [totalBudget, Q, Nat.mul_assoc] using clock

end PDROC.BitVM.VM.CFG.Complete
