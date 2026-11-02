module

public import Paid.PDROC_EndpointOperands_Loop_010
public import Paid.PDROC_EndpointOperands_Loop_011
public import Paid.PDROC_EndpointOperands_Scalar_003

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 800000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits
open PDROC.CalibrationRow.Operand

/-- The original power update10 and natural-counter update8 share the
SAME incoming B. During the first ten instructions slot8 is still m;
the successful literal prefix records that fact instead of synchronizing
it with the already updated power. -/
theorem advance_prefix_safe (input : List Cell) (P : Parameters)
    (origin base E returnPC m budget : ℕ) (before : State) (values : ℕ → Cell)
    (rowBound : m ≤ P.certificate.M + 1) (header : Header before base values)
    (fresh : before.register .fresh = .natural base)
    (power : values 7 = .rational (powerRecurrence P.certificate.odds m))
    (odds : values 6 = .rational P.certificate.odds) (row : values 8 = .natural m)
    (safe : SafeBits before budget) (control : ControlBudget P origin base E returnPC budget)
    (rational : rationalBudget P ≤ budget) (position : before.pc + 18 ≤ pcCap origin returnPC) :
    PrefixSafe input advanceCode before budget := by
  let next := Function.update values 7 (.rational (powerRecurrence P.certificate.odds (m + 1)))
  have valid : ∀ command ∈ [HeaderCommand.rational .multiply 7 6 7], command.Valid := by
    intro command member
    have same := List.mem_singleton.mp member
    subst command
    norm_num [HeaderCommand.Valid, headerWords]
  have evaluated : headerEval [.rational .multiply 7 6 7] values = some next := by
    simp [headerEval, HeaderCommand.eval, Cell.rat?, RatOp.eval, power, odds, next, powerRecurrence]
  obtain ⟨middle, run, middleHeader, middleFresh, middlePC, _frame, _output⟩ :=
    headerCode_realize [.rational .multiply 7 6 7] input before base 0 0 values next
      valid header fresh evaluated
  have firstSafe := advance_scalar_prefix_safe input P origin base E returnPC m budget before values
    rowBound header fresh power odds safe control rational (by omega)
  have laterSafe := incrementRow_prefix_safe input middle base m budget next middleHeader middleFresh
    (by simp [next, row]) (firstSafe.final run)
    (ControlBudget.nat P origin base E returnPC budget 1 control (by unfold naturalCap; omega))
    (ControlBudget.nat P origin base E returnPC budget (m + 1) control (by unfold naturalCap; omega))
    (ControlBudget.headerAddress P origin base E returnPC budget control)
    (ControlBudget.pc P origin base E returnPC budget (middle.pc + 8) control (by
      rw [middlePC]
      change before.pc + 10 + 8 ≤ pcCap origin returnPC
      omega))
  rw [advanceCode_split]
  exact PrefixSafe.append input (headerCode [.rational .multiply 7 6 7]) incrementRowCode
    before middle budget run firstSafe laterSafe

end PDROC.EndpointOperands.Loop
