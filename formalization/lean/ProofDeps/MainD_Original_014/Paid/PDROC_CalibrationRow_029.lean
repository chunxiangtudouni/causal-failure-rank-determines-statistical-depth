module

public import Paid.PDROC_CalibrationRow_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid.Computation PDLower.CalibrationCompute

/-- Exact post-levelInit scratch values. Before these real assignments
the corresponding scratch words may still carry arbitrary caller data.
Only .fresh carries its original value into this complete block result. -/
theorem levelInit_registers (before : State) (base level M : ℕ) :
    (levelInitResult before base level M).register = fun register => match register with
      | .fresh => before.register .fresh
      | .address => .natural (base+7)
      | .index => .natural (rowWidth M)
      | .value => .natural 0
      | .total => .natural (secondRow base M)
      | .old => .natural (firstRow base)
      | .flag => .natural 3 := by
  funext register
  cases register <;>
    simp [levelInitResult,constantSlotResult,secondPointerResult,firstPointerResult,widthResult,
      loadSlotResult,storeSlotResult,State.set,rowWidth,firstRow,secondRow,Nat.mul_comm,Nat.add_assoc]

end PDROC.CalibrationRow
