module

public import Paid.PDROC_CalibrationRow_ControlOperands_005
public import Paid.PDROC_CalibrationRow_ControlOperands_006

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

theorem qScaffold_body_prefix_safe (input : List Cell) (P : Parameters) (origin base level budget : ℕ)
    (label : Label) (before : State) (entry : QScaffoldEntry P base level label before)
    (position : before.pc=labelAddress origin label) (safe : SafeBits before budget)
    (bounds : ControlBudget P origin base budget) : PrefixSafe input (basicBlock label).body before budget := by
  cases entry with
  | start before data =>
    exact reset_body_prefix_safe input P origin base budget 6 .stepStart before bounds safe data.header.fresh position (by decide) rfl
  | gate clock before _bound data =>
    simpa only [stepGate_body] using gate_prefix_safe input before base 6 3 clock P.certificate.Q budget safe
      data.control.header.fresh (data.control.header.live 6 (by decide)) (data.control.header.live 3 (by decide))
      data.control.clockValue data.control.header.Q
      (ControlBudget.slot P origin base budget 6 bounds (by decide)) (ControlBudget.slot P origin base budget 3 bounds (by decide))
      (ControlBudget.literal P origin base budget 0 bounds (by decide)) (ControlBudget.literal P origin base budget 1 bounds (by decide))
      (ControlBudget.pc_prefix P origin base budget bounds before .stepGate 7 position (by decide))
  | zeroStart _clock before _bound data =>
    exact reset_body_prefix_safe input P origin base budget 7 .zeroStart before bounds safe data.control.header.fresh position (by decide) rfl
  | scatterStart _clock before _bound data _row =>
    exact reset_body_prefix_safe input P origin base budget 7 .scatterStart before bounds safe data.header.fresh position (by decide) rfl
  | next clock before bound data _row =>
    exact stepNext_prefix_safe input before base clock budget safe data.control.header.fresh
      (data.control.header.live 6 (by decide)) data.control.clockValue
      (data.control.header.live 9 (by decide)) (data.control.header.live 10 (by decide))
      (ControlBudget.slot P origin base budget 6 bounds (by decide)) (ControlBudget.slot P origin base budget 9 bounds (by decide))
      (ControlBudget.slot P origin base budget 10 bounds (by decide)) (ControlBudget.literal P origin base budget 1 bounds (by decide))
      (ControlBudget.counter P origin base budget (clock+1) bounds (by omega))
      (ControlBudget.pc_prefix P origin base budget bounds before .stepNext 20 position (by decide))

/-- The original scaffold closure is instantiated with SAME caller B.
This only converts actual constructor witnesses on the existing trace. -/
theorem qScaffold_safeBits_closed (input : List Cell) (P : Parameters) (origin base level budget : ℕ)
    (bounds : ControlBudget P origin base budget) :
    QScaffoldClosed P origin base level input (fun state => SafeBits state budget) := by
  intro label before middle after entry safe position body control state location
  have literal := qScaffold_body_prefix_safe input P origin base level budget label before entry position safe bounds
  rcases location with ⟨count,_bound,run⟩|same
  · exact literal count state run
  · subst state
    exact control_safe origin (basicBlock label).control input middle after budget (literal.final body)
      (ControlBudget.pc_target P origin base budget bounds) control

end PDROC.CalibrationRow.Operand
