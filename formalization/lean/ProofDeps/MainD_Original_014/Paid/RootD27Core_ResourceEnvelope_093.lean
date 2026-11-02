module

public import Paid.RootD27Core_TraceCounts_092

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace RootD27.Core

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDCompute.Solver

private theorem search_cost_arithmetic (J A E : ℕ) (small : E≤A) :
    11335*A+85000*A+51000*(J+1)*A+32768*E≤200000*(J+2)*A := by
  nlinarith [Nat.zero_le (J*A)]

private theorem core_cost_arithmetic (J M E Q : ℕ) (positiveE : 0<E) (positiveQ : 0<Q) :
    (8800*(M+1)+30300*(Q+1)*(M+1)^2+2535)+85000*(M+1)*E+
      51000*(J+1)*(M+1)*E+32768*E≤
        300000*((J+2)*E*(M+1)+Q*(M+1)^2) := by
  have mass : M+1≤(M+1)*E := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (M+1) (by omega : 1≤E)
  have small : E≤(M+1)*E := by
    simpa only [Nat.one_mul] using Nat.mul_le_mul_right E (by omega : 1≤M+1)
  have positive : 0<(M+1)*E := Nat.mul_pos (by omega) positiveE
  have preludeCostBound : 8800*(M+1)+2535≤11335*((M+1)*E) := by omega
  have calibration : 30300*(Q+1)*(M+1)^2≤60600*Q*(M+1)^2 := by
    calc
      _≤30300*(2*Q)*(M+1)^2 :=
        Nat.mul_le_mul_right ((M+1)^2) (Nat.mul_le_mul_left 30300 (by omega))
      _=_ := by ring
  have search:=search_cost_arithmetic J ((M+1)*E) E small
  nlinarith [Nat.zero_le ((J+2)*E*(M+1)),Nat.zero_le (Q*(M+1)^2)]

/-- The actual original prefix, Init164, proved J-loop and Final252
costs fit the ORIGINAL sourceCoreScale with one fixed input-independent
constant. Q positivity is part of the original certificate, not a new
qualification supplied by the caller. -/
theorem original_core_time_envelope (P : Parameters) (fee : ℚ) :
    (8800*(P.certificate.M+1)+30300*(P.certificate.Q+1)*(P.certificate.M+1)^2+2535)+
      85000*(P.certificate.M+1)*PDCompute.Solver.entryCount P.certificate.stages P.tools+
      51000*(P.bisectionBudget fee+1)*(P.certificate.M+1)*
        PDCompute.Solver.entryCount P.certificate.stages P.tools+
      32768*PDCompute.Solver.entryCount P.certificate.stages P.tools≤300000*sourceCoreScale P fee := by
  have positive : 0<PDCompute.Solver.entryCount P.certificate.stages P.tools := by
    unfold PDCompute.Solver.entryCount
    positivity
  have bound:=core_cost_arithmetic (P.bisectionBudget fee) P.certificate.M
    (PDCompute.Solver.entryCount P.certificate.stages P.tools) P.certificate.Q positive P.certificate.Q_pos
  simpa only [sourceCoreScale,PDCompute.Solver.entryCount,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using bound

/-- Working records include the real old prefix output, both retained
buffers and one reused solver/global region. No J-dependent space sum
is charged or silently discarded. -/
theorem original_core_space_envelope (P : Parameters) :
    150*(P.certificate.M+1)+156*PDCompute.Solver.entryCount P.certificate.stages P.tools+
      PDCompute.CoreMemory.globalSpan P.certificate.M P.certificate.stages P.tools+
      16*PDCompute.Solver.entryCount P.certificate.stages P.tools+4≤512*sourceRecordSpace P := by
  rw [PDCompute.CoreMemory.globalSpan_exact]
  unfold sourceRecordSpace PDCompute.Solver.entryCount
  omega

end RootD27.Core
