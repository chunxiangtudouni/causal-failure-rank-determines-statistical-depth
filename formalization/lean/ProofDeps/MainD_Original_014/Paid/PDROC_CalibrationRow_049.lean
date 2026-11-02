module

public import Paid.PDROC_CalibrationRow_047
public import Paid.PDROC_CalibrationRow_Zero_005
public import Paid.PDROC_CalibrationRow_Scatter_007

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 1400000

@[expose] public section

namespace PDROC.CalibrationRow

open PaperProofs.Paid PaperProofs.Paid.Computation
open PDLower.CalibrationCompute PDMenu.ComputeFrame

/-- Same-caller Q provenance. Zero/scatter nodes retain their concrete
entry and complete internal canonical provenance, rather than replacing
them by a terminal row or an assumed operand bound. Scaffold blocks keep
the old clock and fixed physical rows through all transient swap states. -/
inductive QProvenance (P : Parameters) (origin base level : ℕ) (input : List Cell)
    (caller : State) : State→Prop where
  | initial : QProvenance P origin base level input caller caller
  | block (label : Label) (before middle after state : State)
      (previous : QProvenance P origin base level input caller before)
      (entry : QScaffoldEntry P base level label before)
      (position : before.pc=labelAddress origin label)
      (body : linearExecute input (basicBlock label).body before=some middle)
      (control : (controlInstruction origin (basicBlock label).control).execute input middle=some after)
      (prefixRun : BlockPrefix input label before after state) :
      QProvenance P origin base level input caller state
  | zero (clock : ℕ) (before state : State)
      (previous : QProvenance P origin base level input caller before)
      (bound : clock<P.certificate.Q)
      (data : ZeroData P base level clock 0
        (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2
        (P.walkRow level true clock) before)
      (position : before.pc=labelAddress origin .zeroGate)
      (phase : ZeroRuntime.ZeroProvenance P origin base level clock
        (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2
        (P.walkRow level true clock) input before state) :
      QProvenance P origin base level input caller state
  | scatter (clock : ℕ) (before state : State)
      (previous : QProvenance P origin base level input caller before)
      (bound : clock<P.certificate.Q)
      (data : ScatterData P base level clock 0
        (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2 before)
      (position : before.pc=labelAddress origin .scatterGate)
      (phase : ScatterProvenance P origin base level clock
        (rowPointers base P.certificate.M clock).1 (rowPointers base P.certificate.M clock).2 input before state) :
      QProvenance P origin base level input caller state

theorem qProvenance_closed (P : Parameters) (origin base level : ℕ) (input : List Cell) (caller : State) :
    QScaffoldClosed P origin base level input (QProvenance P origin base level input caller) := by
  intro label before middle after entry previous position body control state prefixRun
  exact QProvenance.block label before middle after state previous entry position body control prefixRun

end PDROC.CalibrationRow
