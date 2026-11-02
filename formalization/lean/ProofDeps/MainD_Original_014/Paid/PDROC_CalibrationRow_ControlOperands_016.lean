module

public import Paid.PDROC_CalibrationRow_ControlOperands_015

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1200000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Strengthens the ONE already proved original weak-Header execution
trace by pointwise provenance induction. The caller's real B is retained
at every state; assigned values use proved intrinsic envelopes only.
No second existential execution is selected or synchronized. -/
theorem row_complete_provenance_safeBits (input : List Cell) (P : Parameters)
    (origin base level Lgamma budget : ℕ) (before : State)
    (header : PDROC.CalibrationRow.Header P base level before)
    (position : before.pc=labelAddress origin .levelInit) (levelBound : level≤P.certificate.M+1)
    (callerSafe : SafeBits before budget) (bounds : RowBudget P origin base Lgamma budget) :
    ∃ after : State,SafeSegment origin base (region base P.certificate.M) input
      (fun state => RowProvenance P origin base level input before state ∧ SafeBits state budget)
      before after (10000*(P.certificate.Q+1)*(level+1)) ∧
      after.pc=labelAddress origin .sumStart ∧ StepData P base level P.certificate.Q after ∧
      after.heap (base+6)=.natural P.certificate.Q ∧ after.heap (base+7)=.natural (2*level+1) ∧
      after.heap (base+8)=.natural (2*level+1) ∧
      after.heap (base+9)=.natural (rowPointers base P.certificate.M P.certificate.Q).1 ∧
      after.heap (base+10)=.natural (rowPointers base P.certificate.M P.certificate.Q).2 ∧
      RowAt after (rowPointers base P.certificate.M P.certificate.Q).1 (P.walkRow level true P.certificate.Q) := by
  obtain ⟨after,run,finish,data,clock,cursor,width,read,write,row⟩ :=
    row_complete_provenance input P origin base level before header position levelBound
  refine ⟨after,run.weaken ?_,finish,data,clock,cursor,width,read,write,row⟩
  intro state provenance
  exact ⟨provenance,rowProvenance_safe input P origin base level Lgamma budget before state
    callerSafe bounds levelBound provenance⟩

end PDROC.CalibrationRow.Operand
