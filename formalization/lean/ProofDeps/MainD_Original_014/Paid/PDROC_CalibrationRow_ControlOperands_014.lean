module

public import Paid.PDROC_CalibrationRow_ControlOperands_011
public import Paid.PDROC_CalibrationRow_ControlOperands_012
public import Paid.PDROC_CalibrationRow_ControlOperands_013
public import Paid.PDROC_CalibrationRow_ScatterOperands_020

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- ANY canonical Q provenance is lifted constructor by constructor.
Each component uses its own concrete caller, whose SAME B comes from
the predecessor induction hypothesis. The real finite catalog theorem
discharges new scatter assignments; no catalog oracle is a premise. -/
theorem qProvenance_safe (input : List Cell) (P : Parameters) (origin base level Lgamma budget : ℕ)
    (caller state : State) (callerSafe : SafeBits caller budget)
    (bounds : RowBudget P origin base Lgamma budget) (levelBound : level≤P.certificate.M+1)
    (provenance : QProvenance P origin base level input caller state) : SafeBits state budget := by
  induction provenance with
  | initial => exact callerSafe
  | block label before middle after state previous entry position body control prefixRun ih =>
    exact qScaffold_safeBits_closed input P origin base level budget bounds.control label before middle after
      entry ih position body control state prefixRun
  | zero clock before state previous _inside _data _position phase ih =>
    exact zeroProvenance_safe input P origin base level clock
      (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2 budget
      (P.walkRow level true clock) before state ih bounds.control levelBound phase
  | scatter clock before state previous inside _data _position phase ih =>
    exact ScatterOperands.scatterProvenance_safe input P origin base level clock
      (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2 budget before
      levelBound ih (fun value member => RowBudget.catalog P origin base level clock Lgamma budget
        bounds inside.le value member) bounds.control.pcBits state phase

end PDROC.CalibrationRow.Operand
