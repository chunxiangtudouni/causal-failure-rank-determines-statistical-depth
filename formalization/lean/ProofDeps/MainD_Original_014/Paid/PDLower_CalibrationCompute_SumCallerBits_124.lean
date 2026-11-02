module

public import Paid.PDLower_CalibrationCompute_SumPhaseBits_123
public import Paid.PDLower_CalibrationCompute_SumBudgetBridge_100

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits
open PDROC.CalibrationRow.Operand

namespace PDLower.CalibrationCompute

/-- Original walk-row summation with all intrinsic inequalities proved
from the real initial caller and the original denominator/mass theorem.
Only current caller carry and the genuine physical row are supplied. -/
theorem sumPhase_caller_bits (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma : ℕ)
    (input : List Cell) (initialCaller before : State) (header : Header)
    (arguments : CallArguments P base endpoints returnPC initialCaller) (initialSafe : SafeBits initialCaller callerBudget)
    (gammaBits : ratEncodingBits P.certificate.gamma≤Lgamma)
    (position : before.pc=labelAddress origin .sumStart)
    (represented : header.At before base)
    (rowAt : RowAt before header.readBase (P.walkRow header.level true P.certificate.Q))
    (fresh : before.register .fresh=.natural base)
    (safe : SafeBits before (calleeOperandBudget P origin callerBudget Lgamma))
    (buffers : PDROC.CalibrationRow.Buffers base P.certificate.M header.readBase header.writeBase)
    (levelBound : header.level≤P.certificate.M+1) :
    ∃ after : State,BitSegment origin input before after (1000*(header.level+1)) (calleeOperandBudget P origin callerBudget Lgamma) ∧
      after.pc=labelAddress origin .weight ∧
      ({header with
        cursor:=header.level,q:=rowPrefixSum (P.walkRow header.level true P.certificate.Q) header.level+
          (P.walkRow header.level true P.certificate.Q).getD header.level 0*(1/2)}).At after base ∧
      after.register .fresh=.natural base ∧ after.output=before.output ∧
      PDMenu.ComputeFrame.MemoryFrame (sumRegion base) before after := by
  let budget := calleeOperandBudget P origin callerBudget Lgamma
  let row := P.walkRow header.level true P.certificate.Q
  have control := calleeOperandBudget_control P origin base endpoints returnPC callerBudget Lgamma initialCaller arguments initialSafe
  have bounds : SumOperandBounds origin base header.readBase header.level budget row :=
    calleeOperandBudget_sum P origin base endpoints returnPC callerBudget Lgamma header.level header.readBase header.writeBase
      initialCaller arguments initialSafe gammaBits buffers levelBound
  have outside : base+16≤header.readBase := by
    rcases buffers with ⟨read,_write⟩|⟨read,_write⟩
    · rw [read]
      exact le_refl _
    · rw [read]
      unfold secondRow
      omega
  have rowSize : header.level<row.size := by
    dsimp only [row]
    rw [PDROC.endpointWalkRow_size]
    omega
  have zeroRat : (Cell.rational 0).bits≤budget := by
    have literal : (Cell.rational 0).bits=4 := by decide
    rw [literal]
    exact control.small
  have halfBits : (Cell.rational (1/2)).bits≤budget := by
    have literal : (Cell.rational (1/2)).bits=5 := by
      norm_num [Cell.bits,ratEncodingBits,ratNumBits,ratDenBits,natBits]
    rw [literal]
    dsimp [budget,calleeOperandBudget]
    omega
  have width : header.level≤rowWidth P.certificate.M := by unfold rowWidth; omega
  have centerAddress : (Cell.natural (header.readBase+header.level)).bits≤budget :=
    (ControlBudget.rowAddress P origin base budget header.readBase header.writeBase header.level control buffers width).1
  have intrinsic := sumFinish_scalar_encodingBits P Lgamma header.level P.certificate.Q header.level gammaBits
    (by omega) (⟨header.level,by omega⟩ : WalkCell header.level)
  have positive : 0<(P.certificate.Q+1)*(Lgamma+2) := Nat.mul_pos (by omega) (by omega)
  have centerEncoding : ratEncodingBits (row.getD header.level 0*(1/2))≤128*(P.certificate.Q+1)*(Lgamma+2) := by
    have actual : ratEncodingBits (row.getD header.level 0*(1/2))≤5*(P.certificate.Q+1)*(Lgamma+2)+4 := intrinsic.1
    simp only [Nat.mul_assoc] at actual ⊢
    omega
  have finalEncoding : ratEncodingBits (rowPrefixSum row header.level+row.getD header.level 0*(1/2))≤
      128*(P.certificate.Q+1)*(Lgamma+2) := by
    have actual : ratEncodingBits (rowPrefixSum row header.level+row.getD header.level 0*(1/2))≤
        20*(P.certificate.Q+1)*(Lgamma+2)+8 := intrinsic.2
    simp only [Nat.mul_assoc] at actual ⊢
    omega
  exact sumPhase_bits origin input base row before header budget position represented rowAt fresh safe outside rowSize bounds
    zeroRat halfBits centerAddress (calleeOperandBudget_rational P origin callerBudget Lgamma _ centerEncoding)
    (calleeOperandBudget_rational P origin callerBudget Lgamma _ finalEncoding)

end PDLower.CalibrationCompute
