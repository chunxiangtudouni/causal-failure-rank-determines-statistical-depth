module

public import Paid.PDLower_CalibrationCompute_LevelGateBits_112
public import Paid.PDLower_CalibrationCompute_FinishBits_113

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation RootD27.Bits

namespace PDLower.CalibrationCompute

theorem levelGate_continue_bits (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma : ℕ)
    (input : List Cell) (initialCaller before : State) (header : Header)
    (arguments : CallArguments P base endpoints returnPC initialCaller) (initialSafe : SafeBits initialCaller callerBudget)
    (position : before.pc=labelAddress origin .levelGate) (represented : header.At before base)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before (calleeOperandBudget P origin callerBudget Lgamma))
    (M : header.M=P.certificate.M) (bounded : header.level≤header.M+1) :
    ∃ after : State,BitSegment origin input before after 165 (calleeOperandBudget P origin callerBudget Lgamma) ∧
      after.pc=labelAddress origin .levelInit ∧ header.At after base ∧
      after.register .fresh=.natural base ∧ after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  let middle := levelGateResult before base header.level header.M
  let after : State := {middle with pc:=labelAddress origin .levelInit}
  have gate := levelGate_caller_bits P origin base endpoints returnPC callerBudget Lgamma input initialCaller before header
    arguments initialSafe position represented fresh safe M
  refine ⟨after,?_,rfl,represented,?_,rfl,rfl,rfl⟩
  · simpa only [ite_eq_left bounded] using gate
  · exact (levelGate_fresh before base header.level header.M).trans fresh

/-- The actual terminating test and indirect return, with its address
and return-PC bits established by the same executed loads. -/
theorem levelGate_finish_bits (P : Parameters) (origin base endpoints returnPC callerBudget Lgamma : ℕ)
    (input : List Cell) (initialCaller before : State) (header : Header)
    (arguments : CallArguments P base endpoints returnPC initialCaller) (initialSafe : SafeBits initialCaller callerBudget)
    (position : before.pc=labelAddress origin .levelGate) (represented : header.At before base)
    (fresh : before.register .fresh=.natural base) (safe : SafeBits before (calleeOperandBudget P origin callerBudget Lgamma))
    (M : header.M=P.certificate.M) (finished : header.M+1<header.level) :
    ∃ after : State,BitSegment origin input before after 420 (calleeOperandBudget P origin callerBudget Lgamma) ∧
      after.pc=header.returnPC ∧ after.register .fresh=.natural base ∧ after.register .old=.natural header.returnPC ∧
      after.register .address=.natural (resultBase base header.M) ∧ after.register .index=.natural (rowWidth header.M) ∧
      after.heap=before.heap ∧ after.live=before.live ∧ after.output=before.output := by
  let budget := calleeOperandBudget P origin callerBudget Lgamma
  let middle := levelGateResult before base header.level header.M
  let branch : State := {middle with pc:=labelAddress origin .finish}
  have gate := levelGate_caller_bits P origin base endpoints returnPC callerBudget Lgamma input initialCaller before header
    arguments initialSafe position represented fresh safe M
  have branchRun : BitSegment origin input before branch 165 budget := by
    simpa only [ite_eq_right (by omega : ¬header.level≤header.M+1)] using gate
  have branchHeader : header.At branch base := represented
  have branchFresh : branch.register .fresh=.natural base :=
    (levelGate_fresh before base header.level header.M).trans fresh
  let after : State := {finishResult branch base header.M with pc:=header.returnPC}
  have bounds := calleeOperandBudget_control P origin base endpoints returnPC callerBudget Lgamma initialCaller arguments initialSafe
  have finishRun : BitSegment origin input branch after 255 budget :=
    finish_bitSegment P origin input branch base budget header bounds branchHeader branchFresh branchRun.final M rfl
  have registers := finish_registers branch base header branchHeader branchFresh
  exact ⟨after,branchRun.trans finishRun,rfl,registers.2.1,registers.1,registers.2.2.1,registers.2.2.2,rfl,rfl,rfl⟩

end PDLower.CalibrationCompute
