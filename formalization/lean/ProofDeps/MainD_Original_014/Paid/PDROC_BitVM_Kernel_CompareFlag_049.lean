module

public import Paid.PDROC_BitVM_Kernel_RationalProbe_043

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.BitVM.Kernel.CompareFlag

open PaperProofs.Paid.Computation

/-- A fixed three-way opcode choice over ACTUALLY observed finite flags.
No rational number or comparison operation is executed by this function. -/
def flag (comparison : Comparison) (observed : Branch.Store) : Bool :=
  match comparison with
  | .equal => RationalProbe.zeroFlag observed
  | .less => Branch.negativeFlag observed
  | .lessEqual => Branch.negativeFlag observed || RationalProbe.zeroFlag observed

theorem difference (comparison : Comparison) (x y : Rat) (suffix : List Bool) :
    flag comparison (Branch.captured (encodeCellBits (.rational (x-y))++suffix))=comparison.rat x y := by
  cases comparison <;>
    simp [flag,RationalProbe.rational_zero,RationalProbe.rational_sign,Comparison.rat,
      sub_eq_zero,le_iff_lt_or_eq]
  exact Bool.eq_iff_iff.mpr (by simp)

end PDROC.BitVM.Kernel.CompareFlag
