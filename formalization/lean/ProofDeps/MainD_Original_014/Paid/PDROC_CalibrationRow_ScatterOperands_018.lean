module

public import Paid.PDROC_CalibrationRow_ScatterOperands_010
public import Paid.PDROC_CalibrationRow_ScatterOperands_012

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid PaperProofs.Paid.Computation PDLower.CalibrationCompute

theorem interior_prefix_catalog (input : List Cell) (P : Parameters)
    (base level clock cursor count : ℕ) (right : Bool) (before after : State)
    (index : before.register .index = .natural cursor) (inside : cursor < 2 * level + 1)
    (levelBound : level ≤ P.certificate.M + 1) (bound : count ≤ 2)
    (executed : linearExecute input ((interiorCode right).take count) before = some after) :
    Sources before after (Catalog P base level clock) := by
  apply interior_prefix_sources input before after right cursor count (Catalog P base level clock) index
    (offset_catalog P base level clock 1 (by decide)) ?_ bound executed
  apply small_natural_catalog
  have width := activeWidth_le P.certificate.M level levelBound
  cases right <;> simp only [Bool.false_eq_true, ite_false, ite_true] <;> omega

end PDROC.CalibrationRow.ScatterOperands
