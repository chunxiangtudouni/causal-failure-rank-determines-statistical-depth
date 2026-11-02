module

public import Paid.PDLower_CalibrationCompute_RowBitBudget_102
public import Paid.PDLower_CalibrationCompute_BitSegment_086
public import Paid.PDLower_CalibrationCompute_RowHeaderBridge_067
public import Paid.PDROC_CalibrationRow_ControlOperands_016

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits PDMenu.ComputeFrame
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- Real full Q-row on the SAME closed canonical provenance trace, with
full caller-header reconstruction and every original operand at caller B.
The weak row ABI adds no preinitialized rows/clock/scratch assumptions. -/
theorem rowCall_bits (P : Parameters) (origin base Lgamma budget : ℕ) (input : List Cell)
    (before : State) (header : Header)
    (represented : header.At before base) (fresh : before.register .fresh=.natural base)
    (M : header.M=P.certificate.M) (Q : header.Q=P.certificate.Q) (gamma : header.gamma=P.certificate.gamma)
    (position : before.pc=labelAddress origin .levelInit) (bounded : header.level≤P.certificate.M+1)
    (safe : SafeBits before budget) (bounds : RowBudget P origin base Lgamma budget) :
    ∃ after : State,BitSegment origin input before after (10000*(P.certificate.Q+1)*(header.level+1)) budget ∧
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
  obtain ⟨after,actual,pc,data,clock,cursor,width,read,write,row⟩ :=
    row_complete_provenance_safeBits input P origin base header.level Lgamma budget before arguments position bounded safe bounds
  have final := actual.final
  have frame : MemoryFrame (PDROC.CalibrationRow.region base header.M) before after := by
    simpa only [M] using final.1
  have callerHeader := represented.afterRow frame final.2.2.2.1
    P.certificate.Q (2*header.level+1) (2*header.level+1)
    (PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).1
    (PDROC.CalibrationRow.rowPointers base P.certificate.M P.certificate.Q).2 clock cursor width read write
  have bits := BitSegment.ofRow actual (fun _ good => good.2)
  exact ⟨after,bits,pc,callerHeader,row,final.2.2.1.trans fresh,final.2.1,final.1⟩

end PDLower.CalibrationCompute
