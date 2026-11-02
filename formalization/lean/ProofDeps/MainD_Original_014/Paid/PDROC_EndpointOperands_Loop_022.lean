module

public import Paid.PDROC_EndpointOperands_Loop_014

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1000000

@[expose] public section

namespace PDROC.EndpointOperands.Loop

open PaperProofs.Paid PaperProofs.Paid.Parameters PaperProofs.Paid.Computation
open RootD27.Endpoint PDCompute.Solver RootD27.Bits

/-- Discharge local closure by the actual literal Test/Body/Restore
prefix proofs. The only numerical inputs are the fixed new-value budget
and SAME real source SafeBits; no row-run or whole-loop oracle remains. -/
theorem loop_safeBits_closed (P : Parameters) (program : Program) (input : List Cell)
    (origin base E returnPC budget : ℕ) (separated : base + 48 ≤ E)
    (control : ControlBudget P origin base E returnPC budget) (rational : rationalBudget P ≤ budget) :
    LoopClosed P program input base E returnPC (origin + 105) (origin + 113) (origin + 229)
      (fun state => SafeBits state budget) := by
  intro phase m values before state entry safe actual
  cases phase with
  | test =>
    exact test_phase_safe program input P origin base E returnPC m budget values before state
      entry.header entry.fresh entry.invariant.counter entry.invariant.stop entry.position safe control actual
  | body =>
    have literal := rowStraight_prefix_safe input P origin base E returnPC m budget before values
      entry.eligible entry.header entry.fresh entry.invariant separated safe control rational (by
        rw [entry.position]
        change origin + 113 + 115 ≤ pcCap origin returnPC
        unfold pcCap
        omega)
    exact ControlledPrefix.safe program input rowStraightCode before state (origin + 105) budget literal
      (ControlBudget.pc P origin base E returnPC budget (origin + 105) control (by unfold pcCap; omega)) actual
  | restore =>
    exact restore_phase_safe program input P origin base E returnPC budget values before state
      entry.header entry.fresh entry.invariant.stop entry.position safe control actual

/-- Pointwise transport of ANY existing canonical loop source witness,
so the actual functional trace itself is strengthened without selecting
or aligning another existential run. Old cells retain caller B. -/
theorem loopProvenance_safe (P : Parameters) (program : Program) (input : List Cell)
    (origin base E returnPC budget : ℕ) (caller state : State) (separated : base + 48 ≤ E)
    (callerSafe : SafeBits caller budget) (control : ControlBudget P origin base E returnPC budget)
    (rational : rationalBudget P ≤ budget)
    (provenance : LoopProvenance P program input base E returnPC (origin + 105) (origin + 113) (origin + 229) caller state) :
    SafeBits state budget := by
  have closed := loop_safeBits_closed P program input origin base E returnPC budget separated control rational
  induction provenance with
  | initial => exact callerSafe
  | block previous entry actual ih => exact closed _ _ _ _ _ entry ih actual

end PDROC.EndpointOperands.Loop
