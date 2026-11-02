module

public import Paid.PDLower_CalibrationCompute_HeadTrace_026
public import Paid.PDLower_CalibrationCompute_HeaderOps_027

set_option autoImplicit false
set_option warningAsError true

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation

namespace PDLower.CalibrationCompute

/-- The complete initialization phase consumed by the real outer loop.
All sixteen typed header cells are PRODUCED from the original scalar
entry. Old live workspace contents are unrestricted. -/
theorem head_correct (origin : ℕ) (input : List Cell) (P : Parameters)
    (base endpoints returnPC : ℕ) (before : State)
    (arguments : CallArguments P base endpoints returnPC before)
    (position : before.pc=labelAddress origin .enter) :
    Segment origin input before (headResult origin P base before) 1600 ∧
    (Header.initial base endpoints returnPC P.certificate.M P.certificate.Q P.certificate.gamma).At
      (headResult origin P base before) base ∧
    (headResult origin P base before).pc=labelAddress origin .levelGate ∧
    (headResult origin P base before).register .fresh=.natural base ∧
    (headResult origin P base before).output=before.output++[.natural (P.certificate.M+1)] := by
  exact ⟨headSegment origin P input base before position arguments.fresh arguments.total arguments.value,
    headResult_header origin P base endpoints returnPC before arguments.old arguments.address arguments.total
      arguments.index arguments.value,
    headResult_pc ..,(headResult_fresh ..).trans arguments.fresh,headResult_output ..⟩

end PDLower.CalibrationCompute
