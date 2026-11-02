module

public import Paid.PDLower_CalibrationCompute_RowHeaderBridge_067
public import Paid.PDROC_CalibrationRow_044

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1800000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDMenu.ComputeFrame

namespace PDLower.CalibrationCompute

/-- Consume the actual original Q-row callee at the caller's complete
header. No initial clock, row, cursor, successful run or register-size
qualification is added. The returned sixteen-cell header is reconstructed
from its five actual mutable words and the proved strong frame. -/
theorem rowCall (P : Parameters) (origin base : ℕ) (input : List Cell) (before : State) (header : Header)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (M : header.M=P.certificate.M) (Q : header.Q=P.certificate.Q)
    (gamma : header.gamma=P.certificate.gamma)
    (position : before.pc=labelAddress origin .levelInit) (bounded : header.level≤P.certificate.M+1) :
    ∃ after : State,Segment origin input before after (10000*(P.certificate.Q+1)*(header.level+1)) ∧
      after.pc=labelAddress origin .sumStart ∧
      ({header with
        clock:=P.certificate.Q,cursor:=2*header.level+1,width:=2*header.level+1,
        readBase:=(PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1,
        writeBase:=(PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).2}).At after base ∧
      RowAt after (PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1
        (P.walkRow header.level true P.certificate.Q) ∧
      after.register .fresh=.natural base ∧ after.output=before.output ∧
      MemoryFrame (PDROC.CalibrationRow.region base P.certificate.M) before after := by
  have arguments := represented.rowArguments fresh M Q gamma
  obtain ⟨after,actual,pc,data,clock,cursor,width,read,write,row,frame,output,stableFresh⟩ :=
    PDROC.CalibrationRow.row_complete input P origin base header.level before arguments position bounded
  have callerFrame : MemoryFrame (PDROC.CalibrationRow.region base header.M) before after := by
    simpa only [M] using frame
  have callerHeader := represented.afterRow callerFrame data.control.header.live
    P.certificate.Q (2*header.level+1) (2*header.level+1)
    (PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1
    (PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).2 clock cursor width read write
  exact ⟨after,actual,pc,callerHeader,row,stableFresh.trans fresh,output,frame⟩

end PDLower.CalibrationCompute
