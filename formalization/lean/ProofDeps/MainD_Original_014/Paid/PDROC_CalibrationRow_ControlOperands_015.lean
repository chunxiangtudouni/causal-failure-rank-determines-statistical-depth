module

public import Paid.PDROC_CalibrationRow_ControlOperands_008
public import Paid.PDROC_CalibrationRow_ControlOperands_014
public import Paid.PDROC_CalibrationRow_InitOperands_005

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1600000

@[expose] public section

namespace PDROC.CalibrationRow.Operand

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open PDLower.CalibrationCompute RootD27.Bits

/-- Lifts the EXISTING full-row canonical provenance, preserving its
actual component caller links. Only the real original caller is assumed
SafeBits B; every newly assigned value is proved from fixed envelopes. -/
theorem rowProvenance_safe (input : List Cell) (P : Parameters) (origin base level Lgamma budget : ℕ)
    (caller state : State) (callerSafe : SafeBits caller budget)
    (bounds : RowBudget P origin base Lgamma budget) (levelBound : level≤P.certificate.M+1)
    (provenance : RowProvenance P origin base level input caller state) : SafeBits state budget := by
  induction provenance with
  | initial => exact callerSafe
  | levelInit state header position location =>
    have literal := levelInit_prefix_safe input P origin base level budget caller header position levelBound callerSafe bounds.control
    rcases location with ⟨count,_countBound,run⟩|same
    · exact literal count state run
    · subst state
      exact (literal.final (levelInit_execute input P caller base level header)).withPC
        (labelAddress origin .initGate) (ControlBudget.pc_target P origin base budget bounds.control .initGate)
  | init before state previous _header _position _cursor _width _read _write phase ih =>
    have address : firstRow base+rowWidth P.certificate.M≤controlNaturalCap P base := by
      unfold controlNaturalCap
      omega
    exact initProvenance_safe input P origin base level budget before state ih bounds.control.small
      (ControlBudget.address P origin base budget _ bounds.control address)
      (fun target => (PDROC.DataBits.natBits_mono (by omega : labelAddress origin target+15≤labelAddress origin target+32)).trans
        (bounds.control.pcBits target)) levelBound phase
  | scaffold label before middle after state previous entry position body control prefixRun ih =>
    exact qScaffold_safeBits_closed input P origin base level budget bounds.control label before middle after
      entry ih position body control state prefixRun
  | q before state previous _data _position phase ih =>
    exact qProvenance_safe input P origin base level Lgamma budget before state ih bounds levelBound phase

end PDROC.CalibrationRow.Operand
