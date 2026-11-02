module

public import Paid.PDROC_BitVM_Kernel_RawAddSub_053

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1500000

@[expose] public section

namespace PDROC.BitVM.Kernel.RawInstruction

open PaperProofs.Paid.Computation
open PaperProofs.Common.Native.RationalControllerComputation

def resultFunction : RatOp → Rat → Rat → Rat
  | .add => fun x y=>x+y
  | .subtract => fun x y=>x-y
  | .multiply => fun x y=>x*y
  | .divide => fun x y=>x/y

theorem all_operations : ∀ operation : RatOp,∃ states c d : ℕ,∃ source : Machine states,
    0<c ∧ 0<d ∧ RawOp.NativeContract source (resultFunction operation) c d ∧
      Matches operation (resultFunction operation) := by
  intro operation
  cases operation with
  | add =>
    obtain ⟨states,c,d,source,positiveC,positiveD,contract⟩ := RawOp.actual_add_contract
    refine ⟨states,c,d,source,positiveC,positiveD,contract,?_⟩
    intro x y result success
    exact Option.some.inj success
  | subtract =>
    obtain ⟨states,c,d,source,positiveC,positiveD,contract⟩ := RawOp.actual_sub_contract
    refine ⟨states,c,d,source,positiveC,positiveD,contract,?_⟩
    intro x y result success
    exact Option.some.inj success
  | multiply => exact actual_multiply
  | divide => exact actual_divide

/-- All FOUR real fixed native machines, states and constants can be
selected before every original input. The source compiler selects one
only from its static opcode, never from an operand value or width. -/
theorem uniform_family : ∃ states c d : RatOp → ℕ,∃ source : ∀ operation,Machine (states operation),
    ∀ operation,0<c operation ∧ 0<d operation ∧
      RawOp.NativeContract (source operation) (resultFunction operation) (c operation) (d operation) ∧
      Matches operation (resultFunction operation) := by
  choose states c d source positiveC positiveD contract compatible using all_operations
  exact ⟨states,c,d,source,fun operation=>⟨positiveC operation,positiveD operation,contract operation,compatible operation⟩⟩

end PDROC.BitVM.Kernel.RawInstruction
