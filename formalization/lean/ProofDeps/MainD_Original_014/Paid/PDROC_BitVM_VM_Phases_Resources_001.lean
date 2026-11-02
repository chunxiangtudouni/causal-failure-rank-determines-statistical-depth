module

public import Paid.PDROC_BitVM_Log_BankMount_055
public import Paid.PDROC_BitVM_Kernel_Reset_008
public import Paid.PDROC_BitVM_Codec_Finalize_002
public import Paid.PDROC_BitVM_Kernel_NatInstruction_013

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.VM.Phases.Resources

open Turing PaperProofs.Paid.Computation
open scoped BigOperators

/-! SOURCE ONLY. Pure bounds for the already selected physical phase
callee. No second run, empty workspace, P-only scratch bound or relation
between the raw6 and prepared13 input lengths is introduced. -/

abbrev Stack := Kernel.RegisterGlobal.Stack
abbrev dataSize (contents : Stack → List Bool) := Kernel.NatInstruction.dataSize contents

/-- The sixteen old words really cleared by mount occupy distinct slots
among the caller's32 physical stacks. Old bank data are included. -/
theorem preCap_le_dataSize (contents : Stack → List Bool) :
    Log.BankMount.preCap contents ≤ dataSize contents := by
  unfold Log.BankMount.preCap dataSize Kernel.NatInstruction.dataSize
  exact Finset.sum_le_sum_of_injOn Log.BankMount.preSlot
    (fun left _ right _ same => Log.BankMount.preSlot_injective same)
    (Finset.subset_univ _)
    (fun _ _ => Nat.le_refl _)
    (fun _ _ _ => Nat.zero_le _)

/-- The mount input length is paid by its ACTUAL entry stack0, including
the possibility of a carried suffix. This works separately for6/13 cells. -/
theorem encoded_input_le_dataSize (cells : List Cell) (suffix : List Bool)
    (contents : Stack → List Bool)
    (input : contents 0 = encodeBits cells ++ suffix) :
    (encodeBits cells).length ≤ dataSize contents := by
  have length := congrArg List.length input
  simp only [List.length_append] at length
  have slot := Kernel.NatInstruction.dataSize_each contents 0
  change (contents 0).length ≤ dataSize contents at slot
  omega

/-- This is exactly the bound attached by BankMount055.runs_poly to its
ONE selected trace; both its old-word and encoded-input terms are real. -/
theorem mount_budget_le (cells : List Cell) (suffix : List Bool)
    (contents : Stack → List Bool)
    (input : contents 0 = encodeBits cells ++ suffix) :
    1000 * (Log.BankMount.preCap contents + (encodeBits cells).length + 1) ≤
      2000 * (dataSize contents + 1) := by
  have oldWords := preCap_le_dataSize contents
  have inputWord := encoded_input_le_dataSize cells suffix contents input
  omega

/-- Also available for callers retaining the original mountBudget
certificate rather than055's coarsened certificate. -/
theorem original_mount_budget_le (core : Bool) (cells : List Cell) (suffix : List Bool)
    (contents : Stack → List Bool) (size : cells.length = Log.BankMount.fieldCount core)
    (input : contents 0 = encodeBits cells ++ suffix) :
    Log.BankMount.mountBudget core cells contents ≤ 2000 * (dataSize contents + 1) :=
  (Log.BankMount.mountBudget_le core cells contents size).trans
    (mount_budget_le cells suffix contents input)

/-- Reset008's bound charges all old32 words. Registers are really
rewritten and readonly fields are really retained along that same run. -/
theorem reset_budget_le (contents : Stack → List Bool) :
    32 * ((∑ role : Stack, (contents role).length) + 7) + 2 ≤
      258 * (dataSize contents + 1) := by
  change 32 * (dataSize contents + 7) + 2 ≤ 258 * (dataSize contents + 1)
  omega

/-- Finalize002 already proves its four operated input lengths are at
most4D, with arbitrary other caller stacks charged separately. -/
theorem finalize_budget_le (contents : Stack → List Bool) :
    Codec.Finalize.timeBudget contents ≤
      Codec.Finalize.callerTimeCoefficient * (dataSize contents + 1)^3 := by
  simpa only [Codec.Finalize.callerSize, Codec.RatMarshal.globalSize,
    dataSize, Kernel.NatInstruction.dataSize] using Codec.Finalize.timeBudget_callerCubic contents

/-- This retains Finalize002's ALL-state physical-space bound as well;
it does not select a new path or discard untouched caller data. -/
theorem finalize_space_budget_le (contents : Stack → List Bool) :
    Codec.Finalize.spaceBudget contents ≤
      Codec.Finalize.callerSpaceCoefficient * (dataSize contents + 1)^3 := by
  simpa only [Codec.Finalize.callerSize, Codec.RatMarshal.globalSize,
    dataSize, Kernel.NatInstruction.dataSize] using Codec.Finalize.spaceBudget_callerCubic contents

end PDROC.BitVM.VM.Phases.Resources
