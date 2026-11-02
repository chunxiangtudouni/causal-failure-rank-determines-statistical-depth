module

public import Paid.PDROC_CalibrationRow_ControlOperands_009

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits ZeroRuntime

/-- Converts arbitrary EXISTING canonical zero-loop provenance. The
literal count and its actual(c+1,c) middle phase are retained; no second
trace, prezero suffix, or parameter-only old-scratch bound is supplied. -/
theorem zeroProvenance_safe (input : List Cell) (P : Parameters)
    (origin base level clock read write budget : ℕ) (previous : Array ℚ) (caller state : State)
    (callerSafe : SafeBits caller budget) (bounds : ControlBudget P origin base budget)
    (levelBound : level≤P.certificate.M+1)
    (provenance : ZeroProvenance P origin base level clock read write previous input caller state) :
    SafeBits state budget := by
  induction provenance with
  | initial _ => exact callerSafe
  | gate cursor before middle after state previousStep entry _bound position body control location _phase ih =>
    have data := entry.data
    have literal : PrefixSafe input (basicBlock .zeroGate).body before budget := by
      rw [zeroGate_body]
      exact gate_prefix_safe input before base 7 8 cursor (2*level+1) budget ih data.header.fresh
        (data.header.live 7 (by decide)) (data.header.live 8 (by decide)) data.cursorValue data.width
        (ControlBudget.slot P origin base budget 7 bounds (by decide))
        (ControlBudget.slot P origin base budget 8 bounds (by decide))
        (ControlBudget.literal P origin base budget 0 bounds (by decide))
        (ControlBudget.literal P origin base budget 1 bounds (by decide))
        (ControlBudget.pc_prefix P origin base budget bounds before .zeroGate 7 position (by decide))
    rcases location with ⟨count,_countBound,run⟩|same
    · exact literal count state run
    · subst state
      exact control_safe origin (basicBlock .zeroGate).control input middle after budget (literal.final body)
        (ControlBudget.pc_target P origin base budget bounds) control
  | cell cursor before middle after state previousStep entry inside index position body control location ih =>
    have literal := zeroCell_prefix_safe input P origin base level clock cursor read write budget previous before
      entry.data position index inside levelBound ih bounds
    rcases location with ⟨count,_countBound,run,_phase⟩|⟨same,_phase⟩
    · exact literal count state run
    · subst state
      exact control_safe origin (basicBlock .zeroCell).control input middle after budget (literal.final body)
        (ControlBudget.pc_target P origin base budget bounds) control

end PDROC.CalibrationRow.Operand
