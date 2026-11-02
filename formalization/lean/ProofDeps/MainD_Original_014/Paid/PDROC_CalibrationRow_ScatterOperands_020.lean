module

public import Paid.PDROC_CalibrationRow_ScatterOperands_019

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow.ScatterOperands

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- On the same canonical actual execution, one caller cap serves all
prefixes. Assigned-value bounds are independent of how many source cells
have been processed; arbitrary incoming scratch keeps its caller cap. -/
theorem scatterProvenance_safe (input : List Cell) (P : Parameters)
    (origin base level clock read write budget : ℕ) (caller : State)
    (levelBound : level ≤ P.certificate.M + 1) (initial : SafeBits caller budget)
    (assigned : ∀ value, Catalog P base level clock value → value.bits ≤ budget)
    (pc : ∀ label, natBits (labelAddress origin label + 32) ≤ budget) :
    ∀ state, ScatterProvenance P origin base level clock read write input caller state → SafeBits state budget := by
  intro state provenance
  induction provenance with
  | initial => exact initial
  | block cursor label before middle after state previous entry position body control prefixRun ih =>
      have literal := entry_prefix_safe input P origin base level clock cursor read write budget label before
        entry position levelBound ih assigned pc
      rcases prefixRun with ⟨count, _, run⟩ | same
      · exact literal count state run
      · subst state
        apply Operand.control_safe origin (basicBlock label).control input middle after budget
          (literal.final body) ?_ control
        intro target
        exact (PDROC.DataBits.natBits_mono (by omega : labelAddress origin target ≤ labelAddress origin target + 32)).trans (pc target)

end PDROC.CalibrationRow.ScatterOperands
