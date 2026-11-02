module

public import Paid.PDROC_CalibrationRow_ControlOperands_001
public import Paid.PDROC_CalibrationRow_ScatterOperands_002

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits ScatterOperands

/-- One fixed numerical envelope for NEW assigned values. The separate
caller SafeBits premise governs all old cells. Single products use10;
produced rows/partial/first-left keep the frozen5 bound and common D.
Neither bound is multiplied by the number of scattered cells. -/
structure RowBudget (P : Parameters) (origin base Lgamma budget : ℕ) : Prop where
  control : ControlBudget P origin base budget
  gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma
  rationalBits : 1+10*(P.certificate.Q+1)*(Lgamma+2)≤budget

theorem controlNaturalCap_eq_resultBase (P : Parameters) (base : ℕ) :
    controlNaturalCap P base=resultBase base P.certificate.M+P.certificate.Q+1 := rfl

/-- The actual FINITE assigned-value catalog is discharged from proved
intrinsic values, not passed as an oracle to the final row converter. -/
theorem RowBudget.catalog (P : Parameters) (origin base level clock Lgamma budget : ℕ)
    (bounds : RowBudget P origin base Lgamma budget) (clockBound : clock≤P.certificate.Q)
    (value : Cell) (member : Catalog P base level clock value) : value.bits≤budget := by
  have intrinsic := Catalog.bits P base level clock Lgamma bounds.gammaBits value member
  apply intrinsic.trans
  unfold catalogBudget
  apply max_le
  · apply ControlBudget.address P origin base budget (resultBase base P.certificate.M) bounds.control
    rw [controlNaturalCap_eq_resultBase]
    omega
  · exact (Nat.add_le_add_left
      (Nat.mul_le_mul_right (Lgamma+2) (Nat.mul_le_mul_left 10 (Nat.add_le_add_right clockBound 1))) 1).trans bounds.rationalBits

end PDROC.CalibrationRow.Operand
